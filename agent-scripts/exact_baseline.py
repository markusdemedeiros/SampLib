"""Revalidate the old 216-entry suite at the new dependency without rewriting reviews.

This is a compatibility overlay, not a claim that the old reviewers re-reviewed a
new upstream checkout. Explicit source-change reviews are required when project
sources differ; otherwise the old independent mathematical reviews remain intact.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import tempfile

from audit_sampler_proofs import BASELINE, CALLERS, LEAN_HEADER
from audit_exact_sampler_proofs import (agent_identity, caller_imports, local_file, read_json,
                                        require, run, validate_axioms)
from proof_dependencies import ROOT, review_context, sha256, source_snapshot
from relocation import (current_imports, current_path, module_path, relocate_context,
                        relocate_file, relocate_snapshot)

CAMPAIGN = ROOT / "agent-docs/ExactVerificationCampaign.json"
DEFAULT_OVERLAY = ROOT / "agent-docs/reviews/ExactBaselineRevalidation001.json"


def historical_rows() -> tuple[dict, list[dict]]:
    exact = read_json(CAMPAIGN)
    baseline = exact["baseline"]
    path = local_file(baseline["historical_campaign"])
    require(sha256(path) == baseline["historical_campaign_sha256"], "Historical campaign changed")
    old = read_json(path)
    rows = [dict(row) for row in old["candidates"] if row["status"] == "accepted"]
    records = {row["sampler"]: row for row in old["baseline_records"]}
    for sampler, (module, spec, implementation) in BASELINE.items():
        rows.append({"sampler": sampler, "proof_module": module, "public_spec": spec,
                     "implementation": implementation, "baseline_record": records[sampler],
                     "spec_kind": "plain"})
    require(len(rows) == baseline["historical_accepted_total"] == 216,
            "Historical suite must remain exactly 216 distinct entries")
    require(len({row["sampler"] for row in rows}) == 216, "Duplicate historical sampler")
    return exact, rows


def source_change_reviews(paths: list[str], context: dict) -> dict[str, dict]:
    indexed = {}
    for name in paths:
        path = local_file(name)
        review = read_json(path)
        require(relocate_context(review.get("context")) == context,
                f"Source-change review context differs: {name}")
        require(bool(review.get("reviewer")) and bool(review.get("author")) and
                agent_identity(review["reviewer"]) != agent_identity(review["author"]),
                f"Non-independent source-change review: {name}")
        evidence = local_file(review.get("review_evidence"))
        require(sha256(evidence) == review.get("review_evidence_sha256"),
                f"Source-change review evidence changed: {name}")
        for row in review.get("accepted", []):
            sampler = row.get("sampler")
            require(sampler not in indexed, f"Duplicate source-change review: {sampler}")
            require(row.get("direct_sampler_unchanged") is True,
                    f"Changed historical sampler needs a full new proof review: {sampler}")
            required = {"source", "domain", "unchanged_sampler"}
            if "proof_sha256" in row:
                # A revised proof: the reviewer re-checked the whole proof, and the
                # statement pins (checked by the exact audit) fix what it proves.
                required |= {"proof", "statement", "build", "axioms", "caller"}
                require(bool(row.get("previous_proof_sha256")),
                        f"Revised proof must name the proof it replaces: {sampler}")
            require(required <= set(row.get("checks", [])),
                    f"Incomplete source-change review: {sampler}")
            indexed[sampler] = {"review": name, "review_sha256": sha256(path), "entry": row}
    return indexed


def current_entries(rows: list[dict], context: dict, reviews: dict) -> tuple[list[dict], list[str]]:
    entries = []
    callers = set(CALLERS)
    for row in rows:
        sampler = row["sampler"]
        snapshot = source_snapshot(row["proof_module"], row["implementation"])
        record = {key: row[key] for key in
                  ("sampler", "proof_module", "public_spec", "implementation")}
        record["spec_kind"] = row.get("spec_kind", "plain")
        record["source_snapshot"] = snapshot
        if "baseline_record" in row:
            original = row["baseline_record"]["source_snapshot"]
            record["historical_baseline"] = True
        else:
            receipt_path = local_file(row["review_receipt"])
            receipt = read_json(receipt_path)
            candidates = [entry for entry in receipt["accepted"] if entry["sampler"] == sampler]
            require(len(candidates) == 1, f"Ambiguous historical receipt: {sampler}")
            entry = candidates[0]
            proof = row["proof_module"].replace(".", "/") + ".lean"
            current = sha256(local_file(module_path(row["proof_module"])))
            reviewed = relocate_file(proof, entry["sha256"])[1]
            revision = reviews.get(sampler, {}).get("entry", {})
            require(entry["sha256"] == row["reviewed_sha256"] and
                    (reviewed == current or
                     (revision.get("previous_proof_sha256") in (entry["sha256"], reviewed)
                      and revision.get("proof_sha256") == current)),
                    f"Historical proof changed without a revision review: {sampler}")
            require(receipt["reviewer"] == row["reviewer"] != row["owner"],
                    f"Historical independent review mismatch: {sampler}")
            require(receipt["context"]["packages"]["clutch-lean"] ==
                    "54e780e43709d2f28386b83bffccdde498141b25", "Unexpected historical clutch pin")
            old_context = receipt["context"]
            for name, expected in old_context["files"].items():
                if name not in {"lakefile.toml", "lake-manifest.json"}:
                    name, expected = relocate_file(name, expected)
                    require(context["files"].get(name) == expected,
                            f"Policy/toolchain changed since historical review: {name}")
            for name, revision in old_context["packages"].items():
                if name != "clutch-lean":
                    require(context["packages"].get(name) == revision,
                            f"Additional dependency changed since historical review: {name}")
            caller = receipt["caller_evidence"]
            caller_path, caller_sha = relocate_file(caller, receipt["caller_sha256"])
            require(sha256(local_file(caller_path)) == caller_sha,
                    f"Historical independent caller changed: {caller}")
            callers.add(caller)
            original = entry["source_snapshot"]
            record["historical_receipt"] = row["review_receipt"]
            record["historical_receipt_sha256"] = sha256(receipt_path)
        if snapshot != relocate_snapshot(original):
            require(sampler in reviews, f"Project source drift needs explicit review: {sampler}")
            review = reviews[sampler]
            require(review["entry"].get("previous_source_snapshot") == original,
                    f"Source-change review does not identify original snapshot: {sampler}")
            require(relocate_snapshot(review["entry"].get("source_snapshot")) == snapshot,
                    f"Source-change review current snapshot differs: {sampler}")
            record["source_change_review"] = review["review"]
            record["source_change_review_sha256"] = review["review_sha256"]
        entries.append(record)
    return entries, sorted(callers)


def validate_baseline_overlay(path: Path | None = None) -> dict[str, str]:
    """Return source-checked public proof paths covered by a current revalidation."""
    if path is None:
        campaign = read_json(CAMPAIGN)
        path = local_file(campaign.get("baseline_revalidation",
                                      str(DEFAULT_OVERLAY.relative_to(ROOT))))
    overlay = read_json(path)
    exact, rows = historical_rows()
    context = review_context()
    require(context == relocate_context(exact["baseline"]["context"]),
            "Exact campaign baseline context changed")
    require(overlay.get("schema_version") == 1 and overlay.get("kind") == "dependency_revalidation",
            "Unknown baseline revalidation schema")
    require(relocate_context(overlay.get("context")) == context,
            "Baseline revalidation context changed")
    require(overlay.get("historical_campaign_sha256") ==
            exact["baseline"]["historical_campaign_sha256"],
            "Baseline revalidation identifies a different historical campaign")
    reviews = source_change_reviews(overlay.get("source_change_reviews", []), context)
    entries, callers = current_entries(rows, context, reviews)
    recorded = [{**entry, "source_snapshot": relocate_snapshot(entry["source_snapshot"])}
                for entry in overlay.get("entries", [])]
    require(recorded == entries, "Baseline revalidation sources or receipts changed")
    current_callers = {current_path(name): sha256(local_file(current_path(name)))
                       for name in callers}
    require(relocate_snapshot(overlay.get("callers")) == current_callers,
            "Revalidated caller source changed")
    require({"build", "signatures", "axioms", "callers", "sources"} <=
            set(overlay.get("checks", [])),
            "Incomplete baseline revalidation")
    log = local_file(overlay.get("log"))
    require(sha256(log) == overlay.get("log_sha256"), "Baseline revalidation log changed")
    output = log.read_text()
    expected = [(row["public_spec"], row["sampler"]) for row in rows]
    require(re.findall(r"^SPEC_OK (\S+) (\S+)$", output, re.M) == expected,
            "Baseline log does not show all exact specification/program checks")
    validate_axioms(output, [row["public_spec"] for row in rows])
    require("BASELINE_REVALIDATION_OK 216" in output, "Missing completed baseline log marker")
    return {row["sampler"]: module_path(row["proof_module"]) for row in rows}


def revalidate(output: Path, log: Path, review_paths: list[str]) -> None:
    require(not output.exists(), "Revalidation receipts are immutable; choose a new output path")
    require(log.exists(), "Capture this command's stdout to the requested repository log")
    exact, rows = historical_rows()
    context = review_context()
    require(context == relocate_context(exact["baseline"]["context"]),
            "Exact campaign baseline context changed")
    reviews = source_change_reviews(review_paths, context)
    entries, callers = current_entries(rows, context, reviews)
    run(["lake", "build"])
    commands = []
    for row in rows:
        command = ("#audit_owned_dist_spec" if row.get("spec_kind") == "owned"
                   else "#audit_dist_spec")
        commands.extend([f"{command} {row['public_spec']} for {row['sampler']}",
                         f"#print axioms {row['public_spec']}"])
    with tempfile.TemporaryDirectory(prefix="samplib-baseline-revalidation-") as directory:
        path = Path(directory) / "Baseline.lean"
        path.write_text(current_imports(LEAN_HEADER) + "\n".join(commands) + "\n")
        checked = run(["lake", "env", "lean", str(path)])
    expected = [(row["public_spec"], row["sampler"]) for row in rows]
    require(re.findall(r"^SPEC_OK (\S+) (\S+)$", checked, re.M) == expected,
            "Baseline checked specification/program pairs differ")
    validate_axioms(checked, [row["public_spec"] for row in rows])
    for caller in callers:
        print(f"REVALIDATE_CALLER {caller}", flush=True)
        run(["lake", "build", *caller_imports(current_path(caller))])
        run(["lake", "env", "lean", current_path(caller)])
    require(review_context() == context, "Context changed during baseline revalidation")
    require(current_entries(rows, context, reviews) == (entries, callers),
            "Baseline sources changed during revalidation")
    print("BASELINE_REVALIDATION_OK 216", flush=True)
    overlay = {"schema_version": 1, "kind": "dependency_revalidation",
               "meaning": ("Unchanged historical proofs and explicit source-change reviews have "
                           "been checked at the new dependency. This does not rewrite historical "
                           "independent reviews."),
               "context": context,
               "historical_campaign_sha256": exact["baseline"]["historical_campaign_sha256"],
               "source_change_reviews": review_paths, "entries": entries,
               "callers": {name: sha256(local_file(current_path(name))) for name in callers},
               "checks": ["build", "signatures", "axioms", "callers", "sources"],
               "log": str(log.relative_to(ROOT)), "log_sha256": sha256(log)}
    output.write_text(json.dumps(overlay, indent=2, ensure_ascii=False) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--source-change-review", action="append", default=[])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        proofs = validate_baseline_overlay(args.output)
        print(f"Validated current-context baseline overlay for {len(proofs)} proofs.")
    else:
        require(args.log is not None, "Pass --log and redirect stdout to that file")
        revalidate((args.output or DEFAULT_OVERLAY).resolve(), args.log.resolve(),
                   args.source_change_review)


if __name__ == "__main__":
    main()
