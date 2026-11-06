#!/usr/bin/env python3
"""Draft review records for accepted proofs whose sources changed in a refactor.

A refactor that keeps every public statement (see `statement_pins.py`) still voids the
receipts of the proofs it touches. This helper finds those proofs and drafts, for one
reviewer, the records that re-bind them:

- exact-campaign rows: one new receipt per previous caller artifact, in the existing
  receipt shape, ready for `integrate_exact_receipt.py`;
- historical rows: one `historical_source_change_review` for `exact_baseline.py`, with
  `proof_sha256` set where the proof file itself changed.

It only computes hashes and snapshots. The reviewer reads every change, writes the
evidence file, and is responsible for the judgment the records state. Run with
`--list` first to see the stale proofs and the text the evidence must name.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from audit_exact_sampler_proofs import (MANIFEST, AuditError, agent_identity, read_json,
                                        validate_receipt, validate_scope)
from exact_baseline import historical_rows
from proof_dependencies import ROOT, review_context, sha256, source_snapshot
from relocation import current_module, current_path, module_path, relocate_snapshot

FIELDS = ("sampler", "public_spec", "spec_kind", "classification", "reviewed_domain")
HISTORICAL_CHECKS = ["source", "domain", "unchanged_sampler"]
REVISION_CHECKS = ["proof", "statement", "build", "axioms", "caller"]


def stale_exact(context: dict) -> list[dict]:
    rows = validate_scope(read_json(MANIFEST), context)
    stale = []
    for row in rows:
        if row["status"] != "accepted":
            continue
        try:
            validate_receipt(row, context)
        except AuditError:
            stale.append(row)
    return stale


def stale_historical() -> list[dict]:
    _, rows = historical_rows()
    stale = []
    for row in rows:
        if "baseline_record" in row:
            original = row["baseline_record"]["source_snapshot"]
            proof_sha = None
        else:
            receipt = read_json(ROOT / row["review_receipt"])
            entry = next(e for e in receipt["accepted"] if e["sampler"] == row["sampler"])
            original, proof_sha = entry["source_snapshot"], entry["sha256"]
        current = source_snapshot(row["proof_module"], row["implementation"])
        if relocate_snapshot(original) != current:
            stale.append({**row, "original": original, "current": current,
                          "proof_sha": proof_sha})
    return stale


def draft_exact(rows: list[dict], reviewer: str, prefix: str, evidence: str,
                context: dict) -> list[Path]:
    groups: dict[str, list[dict]] = {}
    for row in rows:
        if agent_identity(row["reviewer"]) == agent_identity(reviewer):
            old = read_json(ROOT / row["review_receipt"])
            groups.setdefault(old["caller_evidence"], []).append((row, old))
    written = []
    for index, (caller, members) in enumerate(sorted(groups.items()), 1):
        caller_path = current_path(caller)
        accepted = []
        for row, old in members:
            entry = next(e for e in old["accepted"] if e["sampler"] == row["sampler"])
            module = current_module(row["proof_module"])
            accepted.append({
                **{key: entry[key] for key in FIELDS}, "proof_module": module,
                "sha256": sha256(ROOT / module_path(module)), "review_evidence": evidence,
                "checks": entry["checks"],
                "source_snapshot": source_snapshot(module, row["implementation"])})
        receipt = {"reviewer": reviewer, "context": context, "caller_evidence": caller_path,
                   "caller_sha256": sha256(ROOT / caller_path), "support": [],
                   "accepted": accepted}
        path = ROOT / f"{prefix}{index:03d}.json"
        if path.exists():
            raise SystemExit(f"Receipts are immutable: {path.relative_to(ROOT)}")
        path.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
        written.append(path)
    return written


def draft_historical(rows: list[dict], author: str, reviewer: str, output: str,
                     evidence: str, context: dict) -> Path:
    accepted = []
    for row in rows:
        item = {"sampler": row["sampler"], "direct_sampler_unchanged": True,
                "checks": list(HISTORICAL_CHECKS),
                "previous_source_snapshot": row["original"], "source_snapshot": row["current"]}
        proof = module_path(row["proof_module"])
        current = sha256(ROOT / proof)
        recorded = row["proof_sha"] or row["original"].get(
            row["proof_module"].replace(".", "/") + ".lean")
        if relocate_snapshot({row["proof_module"].replace(".", "/") + ".lean": recorded}) != \
                {proof: current}:
            item.update(previous_proof_sha256=recorded, proof_sha256=current)
            item["checks"] += REVISION_CHECKS
        accepted.append(item)
    review = {"kind": "historical_source_change_review", "author": author,
              "reviewer": reviewer, "context": context, "review_evidence": evidence,
              "review_evidence_sha256": sha256(ROOT / evidence), "accepted": accepted}
    path = ROOT / output
    if path.exists():
        raise SystemExit(f"Reviews are immutable: {output}")
    path.write_text(json.dumps(review, indent=2, ensure_ascii=False) + "\n")
    return path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list stale proofs and stop")
    parser.add_argument("--reviewer", help="canonical reviewer role, for example /root/review_exact_a")
    parser.add_argument("--author", default="/root/round3", help="author of the refactor")
    parser.add_argument("--evidence", help="repository path of the reviewer's evidence .md")
    parser.add_argument("--exact-prefix", help="receipt path prefix, for example "
                        "agent-docs/reviews/ExactRefactorA")
    parser.add_argument("--historical", help="output path of the historical review JSON")
    parser.add_argument("--samplers", type=Path,
                        help="JSON list restricting the drafts to these samplers")
    args = parser.parse_args()
    context = review_context()
    exact, historical = stale_exact(context), stale_historical()
    if args.samplers:
        chosen = set(json.loads(args.samplers.read_text()))
        exact = [row for row in exact if row["sampler"] in chosen]
        historical = [row for row in historical if row["sampler"] in chosen]
    if args.list:
        for row in exact:
            module = current_module(row["proof_module"])
            print("EXACT", row["reviewer"], row["sampler"], row["public_spec"],
                  sha256(ROOT / module_path(module)))
        for row in historical:
            print("HISTORICAL", row["sampler"], row["public_spec"],
                  sha256(ROOT / module_path(row["proof_module"])))
        return
    if not (args.reviewer and args.evidence):
        raise SystemExit("Pass --reviewer and --evidence (or --list)")
    if args.exact_prefix:
        for path in draft_exact(exact, args.reviewer, args.exact_prefix, args.evidence, context):
            print("Drafted", path.relative_to(ROOT))
    if args.historical:
        path = draft_historical(historical, args.author, args.reviewer, args.historical,
                                args.evidence, context)
        print("Drafted", path.relative_to(ROOT))


if __name__ == "__main__":
    main()
