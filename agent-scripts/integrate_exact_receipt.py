#!/usr/bin/env python3
"""Validate immutable reviews before updating only the new exact campaign ledger."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from audit_exact_sampler_proofs import (MANIFEST, agent_identity, local_file, read_json,
                                        require, validate_receipt, validate_scope)
from proof_dependencies import ROOT, review_context
from relocation import current_module


def integrate(receipt_paths: list[str]) -> list[str]:
    context = review_context()
    campaign = read_json(MANIFEST)
    original = MANIFEST.read_bytes()
    rows = validate_scope(campaign, context)
    indexed = {row["sampler"]: row for row in rows}
    additions = {}
    fields = ("proof_module", "public_spec", "review_evidence", "spec_kind", "classification",
              "reviewed_domain")
    for receipt_name in receipt_paths:
        receipt = read_json(local_file(receipt_name))
        for entry in receipt.get("accepted", []):
            name = entry["sampler"]
            require(name in indexed, f"Unscoped acceptance: {name}")
            require(name not in additions, f"Duplicate acceptance in one integration: {name}")
            row = dict(indexed[name])
            require(agent_identity(receipt.get("reviewer")) == agent_identity(row.get("reviewer")),
                    f"Receipt is not from the assigned independent reviewer: {name}")
            row.update({key: entry[key] for key in fields})
            row.update(status="accepted", reviewed_sha256=entry["sha256"],
                       review_receipt=receipt_name)
            row.pop("revision_reason", None)
            validate_receipt(row, context)
            previous = indexed[name].get("review_receipt")
            if previous and previous != receipt_name:
                row["review_history"] = [*row.get("review_history", []), previous]
            additions[name] = row
    require(bool(additions), "No reviewed acceptances to integrate")
    require(MANIFEST.read_bytes() == original, "Concurrent campaign edit; retry integration")
    require(review_context() == context, "Dependency context changed during integration")
    for name, row in additions.items():
        indexed[name].update(row)
    MANIFEST.write_text(json.dumps(campaign, indent=2, ensure_ascii=False) + "\n")
    imports = (ROOT / "SampLib.lean").read_text().splitlines()
    missing = sorted({current_module(row["proof_module"]) for row in additions.values()
                      if f"import {current_module(row['proof_module'])}" not in imports})
    print(f"Integrated {len(additions)} independently reviewed exact campaign entries.")
    for module in missing:
        print(f"Root import needed: import {module}")
    return missing


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", nargs="+", help="repository-relative immutable JSON receipts")
    args = parser.parse_args()
    integrate(args.receipt)


if __name__ == "__main__":
    main()
