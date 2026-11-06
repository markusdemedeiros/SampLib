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


def accepted_proofs() -> dict[str, str]:
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


def draft_proofs(names: set[str], accepted: dict[str, str]) -> dict[str, str]:
    result = {}
    by_short = {}
    for name in names:
        by_short.setdefault(name.split(".")[-1], []).append(name)
    for path in sorted((ROOT / "SampLib/Samplers").glob("*.lean")):
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
        f"{counts.get('sampler', 0)} sampler entries; {len(proofs)} accepted proofs. "
        "**Verified** links identify accepted proofs; **draft** links are unreviewed. "
        "A dash means unverified. Domains and parameter conventions are in the code/proof.", "",
        r"$\mathrm{Geom}_0(p)$ counts failures. $\mathrm{Cat}(w)$ has masses "
        r"$w_i/\sum_jw_j$. $\mathsf{Lazy}[D]$ denotes the intended latent law of a stateful real. "
        r"$\mathsf{Grid}_s[D]$ labels a numerical algorithm targeting $D$; it does **not** "
        r"claim its output is an exact or exactly rounded draw from $D$.", "",
        "Unverified formulas describe intended laws, not established correctness. "
        "Removable singularities use the continuous extensions specified in the code. "
        "“Uncharacterized” records a missing law description rather than guessing one.", "",
    ]
    if pending:
        lines.extend([f"{pending} sampler laws remain uncharacterized.", ""])
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
    lines.extend(["---", "", "Generated by `python3 agent-scripts/law_index.py` from "
                  "[the law catalog](agent-docs/SamplerLaws.json), implementation declarations, "
                  "and accepted review records. GitHub renders the inline math with MathJax.", ""])
    return "\n".join(lines)


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
    result = render(catalog, sources, proofs)
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != result:
            raise SystemExit("LAWS.md is stale; run python3 agent-scripts/law_index.py")
    else:
        OUTPUT.write_text(result)
    print(f"Indexed {len(sources)} definitions with {len(proofs)} accepted proofs.")


if __name__ == "__main__":
    main()
