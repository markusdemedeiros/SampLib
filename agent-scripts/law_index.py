#!/usr/bin/env python3
"""Regenerate the GitHub sampler-law table from curated laws and accepted proofs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "agent-docs/SamplerLaws.json"
OUTPUT = ROOT / "LAWS.md"


def implementations() -> dict[str, dict]:
    result = {}
    for path in sorted((ROOT / "code/Samplers").rglob("*.lean")):
        text = path.read_text()
        namespace = []
        offset = 0
        for line_number, line in enumerate(text.splitlines(keepends=True), 1):
            match = re.match(r"namespace\s+([\w.]+)", line)
            if match:
                namespace.append(match[1])
            if re.match(r"end(?:\s+[\w.]+)?\s*$", line) and namespace:
                namespace.pop()
            match = re.search(r"@\[pl_fold\]\s+def\s+(\w+)", line)
            if match:
                name = ".".join(namespace + [match[1]])
                if name in result:
                    raise ValueError(f"Duplicate implementation: {name}")
                comments = list(re.finditer(r"/--(.*?)\-/", text[:offset], re.S))
                comment = ""
                if comments and not text[comments[-1].end():offset].strip():
                    comment = " ".join(comments[-1].group(1).split())
                result[name] = {
                    "file": str(path.relative_to(ROOT)),
                    "line": line_number,
                    "comment": comment,
                }
            offset += len(line)
    return result


def historical_accepted_proofs() -> dict[str, str]:
    campaign = json.loads((ROOT / "agent-docs/VerificationCampaign.json").read_text())
    result = {
        "Occil.realCoin": "SampLib/Samplers/RealCoin.lean",
        "Occil.vonNeumann": "SampLib/Samplers/VonNeumann.lean",
    }
    hashes = {}

    def current_hash(path: str) -> str:
        if path not in hashes:
            hashes[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        return hashes[path]

    for row in campaign["baseline_records"]:
        for source, expected in row["source_snapshot"].items():
            if current_hash(source) != expected:
                raise ValueError(f"Baseline proof dependency changed: {source}")

    for row in campaign["candidates"]:
        if row["status"] != "accepted":
            continue
        path = row["proof_module"].replace(".", "/") + ".lean"
        digest = current_hash(path)
        if digest != row["reviewed_sha256"]:
            raise ValueError(f"Accepted proof changed since review: {row['sampler']}")
        receipt = json.loads((ROOT / row["review_receipt"]).read_text())
        accepted = [x for x in receipt["accepted"] if x["sampler"] == row["sampler"]]
        if len(accepted) != 1 or accepted[0]["sha256"] != digest:
            raise ValueError(f"No matching acceptance receipt: {row['sampler']}")
        for source, expected in accepted[0]["source_snapshot"].items():
            if current_hash(source) != expected:
                raise ValueError(f"Reviewed dependency changed: {source}")
        for source, expected in receipt["context"]["files"].items():
            if current_hash(source) != expected:
                raise ValueError(f"Review configuration changed: {source}")
        result[row["sampler"]] = path
    return result


def accepted_proofs() -> dict[str, str]:
    campaign_path = ROOT / "agent-docs/ExactVerificationCampaign.json"
    if not campaign_path.exists():
        return historical_accepted_proofs()

    from audit_exact_sampler_proofs import validate_receipt, validate_scope
    from exact_baseline import validate_baseline_overlay
    from proof_dependencies import review_context
    from relocation import module_path

    result = validate_baseline_overlay()
    context = review_context()
    campaign = json.loads(campaign_path.read_text())
    for row in validate_scope(campaign, context):
        if row["status"] != "accepted":
            continue
        validate_receipt(row, context)
        name = row["sampler"]
        if name in result:
            raise ValueError(f"Duplicate accepted sampler across campaigns: {name}")
        result[name] = module_path(row["proof_module"])
    return result


def draft_proofs(names: set[str], accepted: dict[str, str]) -> dict[str, str]:
    result = {}
    by_short = {}
    for name in names:
        by_short.setdefault(name.split(".")[-1], []).append(name)
    for path in sorted((ROOT / "SampLib").glob("*/*.lean")):
        text = path.read_text()
        for short in re.findall(r"\btheorem\s+(\w+)_distSpec\b", text):
            candidates = [n for n in by_short.get(short, [])
                          if re.search(r"\b" + re.escape(n) + r"\b", text)]
            if len(candidates) == 1 and candidates[0] not in accepted:
                result[candidates[0]] = str(path.relative_to(ROOT))
    return result


def table_cell(text: str) -> str:
    return " ".join(text.split()).replace("|", "&#124;")


def validate_math(name: str, law: str) -> None:
    if re.search(r"\\operatorname\b", law):
        raise ValueError(f"Unsupported macro in law index; use \\mathrm or \\text: {name}")
    if "#" in law:
        raise ValueError(f"Use \\lvert and \\rvert for cardinality in the law index: {name}")
    if "|" in law:
        raise ValueError(f"Raw table pipe in law; use \\mid or \\lvert: {name}")
    if "$" in law:
        raise ValueError(f"Nested math delimiter: {name}")
    depth = 0
    # Escaped set delimiters are literal symbols, not TeX grouping braces.
    for symbol in re.sub(r"\\[{}]", "", law):
        depth += (symbol == "{") - (symbol == "}")
        if depth < 0:
            raise ValueError(f"Unbalanced math braces: {name}")
    if depth:
        raise ValueError(f"Unbalanced math braces: {name}")
    if len(re.findall(r"\\left\b", law)) != len(re.findall(r"\\right\b", law)):
        raise ValueError(f"Unbalanced scalable math delimiters: {name}")


def render(catalog: dict, sources: dict[str, dict], proofs: dict[str, str]) -> str:
    entries = catalog["entries"]
    if set(entries) != set(sources):
        missing, stale = set(sources) - set(entries), set(entries) - set(sources)
        raise ValueError(f"Catalog coverage mismatch: missing={sorted(missing)}, stale={sorted(stale)}")
    drafts = draft_proofs(set(sources), proofs)
    counts = {role: sum(e["role"] == role for e in entries.values())
              for role in {e["role"] for e in entries.values()}}
    pending = sum(e["law"] is None for e in entries.values() if e["role"] == "sampler")
    lines = [
        "# Sampler laws", "",
        "[Implementations](code/README.md) · [Verified suite](SampLib/README.md)", "",
        f"This index lists {counts.get('sampler', 0)} sampler entries, with {len(proofs)} "
        "accepted proofs. A **verified** link points to an accepted proof, and a **draft** "
        "link points to a proof that no one has reviewed. A dash means that the sampler has no "
        "proof. The code and the proofs state the domains and parameter conventions.", "",
        r"$\mathrm{Geom}_0(p)$ counts failures. $\mathrm{Cat}(w)$ has masses "
        r"$w_i/\sum_jw_j$. $\mathsf{Lazy}[D]$ denotes the intended latent law of a stateful real. "
        r"$\mathsf{Grid}_s[D]$ labels a numerical algorithm that targets $D$. It does "
        r"**not** claim that its output is an exact or exactly rounded draw from $D$.", "",
        "A formula without a proof describes the intended law and does not establish "
        "correctness. Removable singularities use the continuous extensions that the code "
        "specifies. “Uncharacterized” marks a missing law description, rather than a guess.", "",
    ]
    if pending:
        lines.extend([f"The laws of {pending} samplers remain uncharacterized.", ""])
    for role in ["sampler", "deterministic", "support"]:
        selected = [(name, entry) for name, entry in entries.items() if entry["role"] == role]
        if not selected:
            continue
        if role != "sampler":
            lines.extend(["## " + ("Deterministic generators and helpers" if role == "deterministic"
                                      else "Stateful and sampling support"), ""])
        group = None
        for name, entry in sorted(selected, key=lambda x: (x[1]["group"], x[0])):
            if entry["group"] != group:
                group = entry["group"]
                lines.extend([("## " if role == "sampler" else "### ") + group, "",
                              "| Sampler | Law | Method | Code | Proof |",
                              "| --- | --- | --- | --- | --- |"])
            source = sources[name]
            law = "$" + entry["law"] + "$" if entry["law"] else "Uncharacterized"
            if role == "deterministic":
                law = "Deterministic"
            elif role == "support" and not entry["law"]:
                law = "Support operation"
            proof = "—"
            if name in proofs:
                proof = f"[**verified**]({proofs[name]})"
            elif name in drafts:
                label = "draft" if role == "sampler" else "proof"
                proof = f"[{label}]({drafts[name]})"
            link = f"[{Path(source['file']).name}]({source['file']}#L{source['line']})"
            lines.append(f"| `{name}` | {table_cell(law)} | {table_cell(entry['method'])} | {link} | {proof} |")
        lines.append("")
    lines.extend(["---", "", "`python3 agent-scripts/law_index.py` generates this file from "
                  "the [law catalog](agent-docs/SamplerLaws.json), the implementation "
                  "declarations, and the accepted review records. GitHub renders the inline "
                  "math with MathJax.", ""])
    return "\n".join(lines)


FOLDERS = {
    "Core": "This directory holds the spec interfaces beyond `IsDistSpec`, helpers for closed "
            "terms, lists, and arrays, and a proof-mode extension. Every family builds on it.",
    "Common": "This directory holds the laws and helpers that several families share, "
              "together with every helper that they import.",
    "Latent": "This directory holds the shared lazy-real machinery: the latent spec kinds, "
              "worlds, views, and uniform bags.",
    "Uniform": "This directory holds the proofs for uniform integers and primitive coins.",
    "Bernoulli": "This directory holds the proofs for coin composition and for linear, "
                 "rational, series, polynomial, and envelope Bernoulli factories.",
    "Constants": "This directory holds the proofs for coins of named constants, which digit "
                 "and interval engines produce.",
    "Discrete": "This directory holds the proofs for count laws, compound distributions, "
                "urns, and discrete tails.",
    "Continuous": "This directory holds the proofs for comparison-based continuous samplers "
                  "and generic rejection.",
    "Combinatorial": "This directory holds the proofs for collection sampling, shuffles, and "
                     "permutations.",
    "Weighted": "This directory holds the proofs for weighted choice: tables, trees, alias "
                "and optimal samplers, and entropy recycling.",
    "General": "This directory holds the proofs for general schemes: Markov chains, coupling "
               "from the past, Metropolis sampling, and point selection.",
    "PSRN": "This directory holds the proofs for lazy exact reals: arithmetic, observations, "
            "and exact continuous samplers.",
}
ROLES = [("Laws", "target laws, kernels, and expectation lemmas"),
         ("Syntax", "unfolding lemmas for the `pl%` source terms"),
         ("Support", "CTE loop invariants and other program-level helpers")]


def folder_readmes(catalog: dict, sources: dict[str, dict],
                   proofs: dict[str, str]) -> dict[Path, str]:
    """One index per SampLib folder: what it holds and which accepted proofs live there."""
    result = {}
    for folder, summary in FOLDERS.items():
        base = ROOT / "SampLib" / folder
        specs = sorted(base.glob("*.lean"))
        lines = [f"# {folder}", "", summary, "",
                 "For how the directories fit together, see the "
                 "[library layout](../README.md#layout)."]
        rows = sorted((name, path) for name, path in proofs.items()
                      if base.relative_to(ROOT) in Path(path).parents)
        if rows:
            lines.extend(["", f"## Verified samplers ({len(rows)})", "",
                          "| Sampler | Law | Proof | Code |", "| --- | --- | --- | --- |"])
            for name, path in rows:
                law = catalog["entries"].get(name, {}).get("law")
                law = "$" + law + "$" if law else "—"
                source = sources[name]
                code = f"[{Path(source['file']).name}](../../{source['file']}#L{source['line']})"
                target = Path(path).relative_to(base.relative_to(ROOT))
                lines.append(f"| `{name}` | {table_cell(law)} | "
                             f"[{Path(path).stem}]({target}) | {code} |")
        contents = [f"- Top level: {len(specs)} modules"] if specs else []
        for role, meaning in ROLES:
            count = len(list((base / role).glob("*.lean")))
            if count:
                contents.append(f"- [`{role}/`]({role}): {count} modules with {meaning}")
        lines.extend(["", "## Contents", "", *contents, "", "---", "",
                      "`python3 agent-scripts/law_index.py` generates this file.", ""])
        result[base / "README.md"] = "\n".join(lines)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the generated index is stale")
    args = parser.parse_args()
    catalog = json.loads(CATALOG.read_text())
    sources = implementations()
    for name, entry in catalog["entries"].items():
        if entry["law"]:
            validate_math(name, entry["law"])
        if not entry["method"]:
            raise ValueError(f"Missing description: {name}")
    proofs = accepted_proofs()
    if not set(proofs) <= set(sources):
        raise ValueError("Accepted proof has no indexed implementation")
    outputs = {OUTPUT: render(catalog, sources, proofs),
               **folder_readmes(catalog, sources, proofs)}
    for path, text in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f"{path.relative_to(ROOT)} is stale; "
                                 "run python3 agent-scripts/law_index.py")
        else:
            path.write_text(text)
    print(f"Indexed {len(sources)} definitions with {len(proofs)} accepted proofs.")


if __name__ == "__main__":
    main()
