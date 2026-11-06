"""Keep the current verification count separate from the frozen goal baseline."""

import json
import re

from proof_dependencies import ROOT, sha256


def verify_expansion_state(campaign: dict, require_complete: bool = False) -> int:
    relative = campaign.get("expansion_ledger")
    if relative is None:
        return 0
    expansion = json.loads((ROOT / relative).read_text())
    baseline = set(expansion["baseline_sampler_names"])
    log = ROOT / expansion["baseline_audit_log"]
    audited = set(re.findall(r"^SPEC_OK \S+ (\S+)$", log.read_text(), re.M))
    if (len(baseline) != 47 or expansion["baseline_sampler_count"] != 47
            or baseline != audited or sha256(log) != expansion["baseline_audit_sha256"]):
        raise SystemExit("Expansion baseline differs from the frozen 47-sampler audit")
    rows = expansion["candidates"]
    indexed = {row["sampler"]: row for row in rows}
    if len(indexed) != len(rows) or baseline & set(indexed):
        raise SystemExit("Duplicate expansion candidate or preexisting sampler counted again")
    accepted = {row["sampler"]: row for row in campaign["candidates"]
                if row["status"] == "accepted"}
    names = set(accepted) | set(campaign["baseline"])
    if not baseline <= names:
        raise SystemExit("An original sampler disappeared from the accepted suite")
    additions = names - baseline
    signed = {row["sampler"] for row in rows if row["status"] == "accepted"}
    if additions != signed or set(expansion.get("accepted_additional", [])) != additions:
        raise SystemExit("Expansion count differs from independently accepted additions")
    for name in additions:
        for field in ("proof_module", "public_spec", "reviewed_sha256", "review_receipt"):
            if indexed[name].get(field) != accepted[name].get(field):
                raise SystemExit(f"Expansion acceptance metadata differs: {name}, {field}")
    if (expansion["minimum_additional"] < 120 or campaign["target_new_samplers"] < 165
            or campaign["target_total_samplers"] < 167):
        raise SystemExit("Campaign metadata weakens the additional 120-sampler minimum")
    if require_complete:
        if len(additions) < 120:
            raise SystemExit(f"Expansion has {len(additions)} additions; at least 120 are required")
        pending = [row["sampler"] for row in rows
                   if row["status"] not in {"accepted", "rejected"}]
        if pending:
            raise SystemExit(f"Expansion still has {len(pending)} unassessed or unfinished candidates")
        for row in rows:
            if row["status"] != "rejected":
                continue
            evidence = row.get("rejection_evidence")
            if (not row.get("rejection_reason") or not evidence
                    or not (ROOT / evidence).is_file()
                    or row["sampler"] not in (ROOT / evidence).read_text()):
                raise SystemExit(f"Rejection lacks concrete review evidence: {row['sampler']}")
    return len(additions)
