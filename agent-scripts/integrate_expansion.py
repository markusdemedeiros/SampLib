#!/usr/bin/env python3
"""Integrate independently signed sampler proofs into the public suite."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

from audit_sampler_proofs import verify_receipt
from proof_dependencies import ROOT, review_context
from relocation import current_module, module_path


def read(path: Path):
    return json.loads(path.read_text())


def write(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def proof_kind(row: dict) -> str:
    """Normalize the three reviewer groups' classification field names."""
    kinds = {row[key] for key in ("proof_kind", "algorithm_kind", "classification")
             if key in row}
    if len(kinds) > 1:
        raise SystemExit(f"Conflicting proof classifications: {row['sampler']}")
    kind = next(iter(kinds), "core")
    if kind not in {"core", "derived", "generic"}:
        raise SystemExit(f"Not a counted sampler: {row['sampler']}")
    return kind


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group", action="append", choices=["Factories", "Discrete", "Structured"])
    args = parser.parse_args()
    campaign_path = ROOT / "agent-docs/VerificationCampaign.json"
    expansion_path = ROOT / "agent-docs/ExpansionCampaign.json"
    campaign, expansion = read(campaign_path), read(expansion_path)
    baseline = set(expansion["baseline_sampler_names"])
    if len(baseline) != 47 or expansion["baseline_sampler_count"] != 47:
        raise SystemExit("Expansion baseline must remain the original 47 samplers")
    planned = {row["sampler"]: row for row in expansion["candidates"]}
    existing = {row["sampler"]: row for row in campaign["candidates"]}
    context = review_context()
    additions = []
    for group in args.group or ("Factories", "Discrete", "Structured"):
        path = ROOT / f"agent-docs/reviews/Expansion{group}Candidates.json"
        if not path.exists():
            continue
        for row in read(path):
            name = row["sampler"]
            if row["status"] != "accepted":
                continue
            if name in baseline or name not in planned:
                raise SystemExit(f"Unplanned or preexisting candidate: {name}")
            row["proof_kind"] = proof_kind(row)
            verify_receipt(row, context)
            if row["reviewer"].rsplit("/", 1)[-1] != planned[name]["reviewer"].rsplit("/", 1)[-1]:
                # A second valid review is evidence, not a second sampler or a
                # reason to replace the campaign's assigned primary reviewer.
                continue
            if name not in existing:
                additions.append(row)
                existing[name] = row
            else:
                existing[name].update(row)
            planned[name].update(row)
    campaign["candidates"].extend(additions)
    accepted = [row for row in campaign["candidates"] if row["status"] == "accepted"]
    if len({row["sampler"] for row in accepted}) != len(accepted):
        raise SystemExit("Duplicate accepted sampler")
    campaign["accepted"] = [row["sampler"] for row in accepted]
    campaign["objective"] = (
        "Execute the 120–170 additional-sampler expansion from the frozen 47-sampler "
        "suite, rejecting poor Math/Program logic fits and pursuing all viable candidates."
    )
    campaign["target_new_samplers"] = 45 + expansion["minimum_additional"]
    campaign["target_total_samplers"] = 47 + expansion["minimum_additional"]
    campaign["expansion_ledger"] = "agent-docs/ExpansionCampaign.json"
    expansion["accepted_additional"] = [
        row["sampler"] for row in accepted if row["sampler"] not in baseline
    ]
    root_path = ROOT / "SampLib.lean"
    imports = root_path.read_text()
    for row in accepted:
        line = "import " + current_module(row["proof_module"])
        if line not in imports.splitlines():
            imports += line + "\n"
    # Every receipt is validated before any authoritative artifact changes.
    write(campaign_path, campaign)
    write(expansion_path, expansion)
    root_path.write_text(imports)
    total = len(accepted) + len(campaign["baseline"])
    for relative in ("README.md", "agent-scripts/readme_index.py"):
        path = ROOT / relative
        text = path.read_text()
        text = re.sub(r"contains \*\*\d+ samplers\*\*", f"contains **{total} samplers**", text)
        text = re.sub(
            r"\*\*\d+ (?:new proofs|additions to the original 47-sampler suite)\*\*",
            f"**{len(expansion['accepted_additional'])} additions to the original 47-sampler suite**",
            text,
        )
        path.write_text(text)
    suite_path = ROOT / "SampLib/README.md"
    text = suite_path.read_text()
    text = re.sub(r"\d+ sampler specifications: \d+ new verifications",
                  f"{total} sampler specifications: {len(accepted)} new verifications", text)
    start, end = "<!-- expansion:start -->", "<!-- expansion:end -->"
    new_rows = [row for row in accepted if row["sampler"] not in baseline]
    lines = [start, "## Expansion campaign", "",
             "This table lists the accepted additions to the original 47-sampler suite. "
             "The [law index](../LAWS.md) also lists implementations that have no proof.", "",
             "| Sampler | Kind | Law and domain | Proof |", "| --- | --- | --- | --- |"]
    for row in new_rows:
        module = row["proof_module"].split(".")[-1]
        target = module_path(row["proof_module"]).removeprefix("SampLib/")
        domain = row["reviewed_domain"].replace("|", "\\|")
        kind = proof_kind(row)
        lines.append(f"| `{row['sampler']}` | {kind} | {domain} | "
                     f"[{module}]({target}) |")
    lines += ["", end, ""]
    block = "\n".join(lines) + "\n"
    if start in text:
        before, tail = text.split(start, 1)
        _, after = tail.split(end, 1)
        text = before + block + after.lstrip("\n")
    else:
        text = text.replace("## Reading and checking the proofs", block + "\n## Reading and checking the proofs")
    suite_path.write_text(text)
    print(f"Integrated {len(additions)} additions; {total} sampler specifications total.")
    print(f"Expansion accepted: {len(expansion['accepted_additional'])}; goal remains active.")


if __name__ == "__main__":
    main()
