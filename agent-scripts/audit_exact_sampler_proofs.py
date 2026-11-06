#!/usr/bin/env python3
"""Audit the frozen 137-entry exact-sampler campaign independently of historic reviews.

Run under lean_gate.py. Review receipts establish the domain, mathematical
interpretation and proof-quality judgment; this script checks their binding to
sources, the dependency context, actual Lean theorem types, axioms and callers.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import tempfile

from audit_sampler_proofs import LEAN_HEADER, STANDARD_AXIOMS
from proof_dependencies import ROOT, review_context, sha256, source_snapshot
from relocation import (current_imports, current_module, module_path, relocate_context,
                        relocate_file, relocate_snapshot)

MANIFEST = ROOT / "agent-docs/ExactVerificationCampaign.json"
SCOPE_COUNT = 137
CLUTCH_REVISION = "06a7b3e2b26f3e58c01edb12e39bdf439ba5a982"
STATUSES = {"pending", "in_progress", "ready_for_review", "revision_requested",
            "accepted", "finding"}
CLASSIFICATIONS = {"core", "derived", "support"}
REQUIRED_CHECKS = {"source", "build", "axioms", "caller", "boundaries", "protocol"}


# The existing conditional interface preserves both the latent uniform and the
# refined heap ownership. It is intentionally distinct from a marginal law.
EXACT_LEAN_HEADER = LEAN_HEADER.replace(
    "import SampLib.OwnedDistSpec", "import SampLib.OwnedDistSpec\nimport SampLib.UniformBagCoin"
).replace(
    "if head.isConstOf ``SampLib.IsDistSpec || "
    "head.isConstOf ``SampLib.IsOwnedDistSpec then",
    "if [``SampLib.IsDistSpec, ``SampLib.IsOwnedDistSpec, "
    "``SampLib.UniformBag.IsCoinSpec, "
    "`SampLib.LatentReal.IsLatentDistSpec, "
    "`SampLib.LatentReal.IsLatentPayloadSpec, "
    "`SampLib.LatentReal.IsLatentVectorSpec, "
    "`SampLib.LatentReal.IsLatentCoinProgramSpec].any head.isConstOf then",
).replace(
    'let label := if specName == ``SampLib.IsDistSpec then "IsDistSpec" else "IsOwnedDistSpec"',
    'let label := specName.toString',
).replace(
    "private partial def containsOwnSpec",
    r'''private partial def callsSampler (target : Name) (e : Expr) : MetaM Bool := do
  let e := stripLets e
  match e with
  | .lam n domain body bi =>
      withLocalDecl n bi domain fun source =>
        callsSampler target (body.instantiate1 source)
  | _ => return (programHead e).getAppFn.isConstOf target

private def programParameter (info : ConstantInfo) : Option Nat :=
  (parameterIndex `e info.type).orElse (fun _ => parameterIndex `program info.type)

private partial def containsOwnSpec''',
).replace(
    "parameterIndex `e specInfo.type", "programParameter specInfo",
).replace(
    "return (programHead args[index]!).getAppFn.isConstOf target",
    "return ← callsSampler target args[index]!",
).replace(
    "unless (programHead args[index]!).getAppFn.isConstOf samplerName do",
    "unless ← callsSampler samplerName args[index]! do",
) + r'''
elab "#audit_latent_coin_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.UniformBag.IsCoinSpec

'''
SPEC_AUDIT_COMMANDS = {
    "plain": "#audit_dist_spec",
    "owned": "#audit_owned_dist_spec",
    "latent_coin": "#audit_latent_coin_spec",
    "latent_real": "#audit_latent_real_spec",
    "latent_vector": "#audit_latent_vector_spec",
    "conditional_coin": "#audit_conditional_coin_spec",
}


def lean_audit_header(kinds: set[str]) -> str:
    """Load the deferred-real protocol only when a reviewed instance uses it."""
    imports, commands = [], []
    if "latent_real" in kinds:
        imports.append("import SampLib.LatentSpec")
        commands.append(r'''
elab "#audit_latent_real_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.LatentReal.IsLatentDistSpec
''')
    if "conditional_coin" in kinds:
        imports.append("import SampLib.LatentCoinSpec")
        commands.append(r'''
elab "#audit_conditional_coin_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.LatentReal.IsLatentCoinProgramSpec
''')
    if "latent_vector" in kinds:
        imports.append("import SampLib.LatentVectorSpec")
        commands.append(r'''
elab "#audit_latent_vector_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.LatentReal.IsLatentVectorSpec
''')
    return current_imports(EXACT_LEAN_HEADER.replace(
        "import SampLib.UniformBagCoin", "\n".join(["import SampLib.UniformBagCoin", *imports]),
    )) + "\n".join(commands)


class AuditError(ValueError):
    """An authoritative campaign invariant failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def agent_identity(name: str) -> str:
    """Treat short team names and their /root/ canonical names identically."""
    require(isinstance(name, str) and bool(name), "Missing agent identity")
    if name == "/root":
        return name
    if "/" not in name:
        require(re.fullmatch(r"[a-z][a-z0-9_]*", name) is not None, "Invalid short agent name")
        return "/root/" + name
    require(re.fullmatch(r"/root(?:/[a-z][a-z0-9_]*)+", name) is not None,
            f"Invalid canonical agent name: {name}")
    return name


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def local_file(name: str) -> Path:
    require(isinstance(name, str) and bool(name), "Missing artifact path")
    path = ROOT / name
    require(path.resolve().is_relative_to(ROOT), f"Artifact escapes repository: {name}")
    require(path.is_file(), f"Missing artifact: {name}")
    return path


def validate_scope(campaign: dict, context: dict) -> list[dict]:
    require(campaign.get("schema_version") == 1, "Unknown campaign schema")
    names = campaign.get("scope_sampler_names", [])
    require(campaign.get("scope_count") == SCOPE_COUNT == len(names), "Goal scope must remain 137")
    require(len(set(names)) == SCOPE_COUNT, "Duplicate frozen scope name")
    scope = local_file(campaign["scope_source"])
    require(sha256(scope) == campaign["scope_sha256"], "Frozen queue changed")
    queue_names = re.findall(r"^\| `(Occil\.[^`]+)` \|", scope.read_text(), re.M)
    require(queue_names == names, "Frozen names differ from original queue")
    baseline = campaign["baseline"]
    require(context == relocate_context(baseline["context"]),
            "Review configuration/dependency context changed")
    require(context["packages"].get("clutch-lean") == CLUTCH_REVISION,
            "This campaign must use the new pinned clutch revision")
    historical = local_file(baseline["historical_campaign"])
    require(sha256(historical) == baseline["historical_campaign_sha256"],
            "Historic campaign changed; do not rewrite its old-context receipts")
    from exact_source_repairs import validate_source_repairs

    repairs = validate_source_repairs(campaign, context)
    for name, expected in baseline["implementation_snapshot"].items():
        expected = repairs.get(name, expected)
        require(sha256(local_file(name)) == expected,
                f"Baseline sampler implementation changed: {name}")
    rows = campaign.get("candidates", [])
    require([row.get("sampler") for row in rows] == names, "Candidate scope/order changed")
    for row in rows:
        require(row.get("status") in STATUSES, f"Invalid status: {row['sampler']}")
        require(row.get("implementation") in baseline["implementation_snapshot"],
                f"Unpinned implementation: {row['sampler']}")
        require(not row.get("owner") or isinstance(row["owner"], str), "Malformed owner")
        if row.get("status") == "finding":
            finding = row.get("finding")
            require(isinstance(finding, dict) and bool(finding.get("summary")),
                    f"Finding needs an explicit summary: {row['sampler']}")
            local_file(finding.get("evidence"))
    return rows


def validate_receipt(row: dict, context: dict) -> str:
    name = row["sampler"]
    require(bool(row.get("owner")) and bool(row.get("reviewer")), f"Unassigned review: {name}")
    require(agent_identity(row["owner"]) != agent_identity(row["reviewer"]),
            f"Author cannot review own proof: {name}")
    require(row.get("classification") in CLASSIFICATIONS, f"Unclassified proof: {name}")
    require(row.get("spec_kind") in SPEC_AUDIT_COMMANDS, f"Unsupported spec interface: {name}")
    require(bool(row.get("reviewed_domain")), f"Missing reviewed parameter domain: {name}")
    module = row.get("proof_module")
    require(isinstance(module, str) and re.fullmatch(r"SampLib(?:\.\w+)+", module) is not None,
            f"Invalid proof module: {name}")
    proof = local_file(module_path(module))
    recorded_proof = module.replace(".", "/") + ".lean"
    require(sha256(proof) == relocate_file(recorded_proof, row.get("reviewed_sha256"))[1],
            f"Reviewed proof changed: {name}")
    require(isinstance(row.get("public_spec"), str) and
            re.fullmatch(r"SampLib(?:\.\w+)+", row["public_spec"]) is not None,
            f"Missing or malformed public specification: {name}")
    receipt = read_json(local_file(row.get("review_receipt")))
    require(agent_identity(receipt.get("reviewer")) == agent_identity(row["reviewer"]),
            f"Receipt reviewer mismatch: {name}")
    require(relocate_context(receipt.get("context")) == context,
            f"Receipt uses a different dependency pin: {name}")
    matches = [entry for entry in receipt.get("accepted", []) if entry.get("sampler") == name]
    require(len(matches) == 1, f"No unique receipt acceptance: {name}")
    entry = matches[0]
    for field in ("proof_module", "public_spec", "review_evidence", "spec_kind", "classification",
                  "reviewed_domain"):
        require(entry.get(field) == row.get(field), f"Receipt {field} mismatch: {name}")
    require(entry.get("sha256") == row["reviewed_sha256"], f"Receipt proof hash mismatch: {name}")
    required_checks = REQUIRED_CHECKS | (
        {"observation", "aliases"} if row["spec_kind"] in {"latent_real", "latent_vector", "conditional_coin"}
        else set()
    )
    if row["spec_kind"] == "latent_vector":
        required_checks |= {"joint", "coordinates"}
    if row["spec_kind"] == "conditional_coin":
        required_checks.add("joint")
    require(required_checks <= set(entry.get("checks", [])),
            f"Incomplete reviewer checks: {name}")
    snapshot = relocate_snapshot(entry.get("source_snapshot"))
    require(snapshot == source_snapshot(module, row["implementation"]),
            f"Transitive reviewed sources changed: {name}")
    evidence = local_file(row.get("review_evidence"))
    text = evidence.read_text()
    require(row["public_spec"] in text and row["reviewed_sha256"] in text,
            f"Review prose must identify exact theorem and source hash: {name}")
    caller_name = receipt.get("caller_evidence")
    caller_path, caller_sha = relocate_file(caller_name, receipt.get("caller_sha256"))
    caller = local_file(caller_path)
    require(caller.suffix == ".lean" and caller_name.startswith("agent-docs/reviews/Exact"),
            f"Caller must be a reviewer-owned Exact campaign Lean artifact: {name}")
    require(sha256(caller) == caller_sha, f"Reviewed caller changed: {name}")
    for support in receipt.get("support", []):
        support_name = support.get("path") or support["module"].replace(".", "/") + ".lean"
        support_path, support_sha = relocate_file(support_name, support.get("sha256"))
        require(sha256(local_file(support_path)) == support_sha,
                f"Reviewed support changed: {support_name}")
    for path_name, expected in snapshot.items():
        if path_name.endswith(".lean") and not path_name.startswith("code/"):
            text = local_file(path_name).read_text()
            require(re.search(r"\b(?:sorry|admit|axiom)\b", strip_comments(text)) is None,
                    f"Placeholder or explicit axiom in project proof closure: {path_name}")
    return caller_path


def strip_comments(text: str) -> str:
    """Remove nested Lean comments before the conservative placeholder scan."""
    result = []
    i = 0
    depth = 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif pair == "-/" and depth:
            depth -= 1
            i += 2
        elif not depth and pair == "--":
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif depth:
            i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def run(command: list[str]) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    require(result.returncode == 0, f"Command failed: {command}")
    require("warning:" not in result.stdout, f"Command emitted warnings: {command}")
    return result.stdout


def caller_imports(caller: str) -> list[str]:
    from proof_dependencies import imports_of

    return [module for module in imports_of(ROOT / caller) if module.startswith("SampLib")]


def validate_axioms(output: str, specs: list[str]) -> None:
    for spec in specs:
        pattern = re.escape(f"'{spec}' depends on axioms:") + r"\s*\[([^]]*)\]"
        match = re.search(pattern, output)
        if match:
            axioms = {name.strip() for name in match[1].split(",") if name.strip()}
            require(not axioms - STANDARD_AXIOMS, f"Unapproved axioms for {spec}: {axioms}")
        else:
            require(f"'{spec}' does not depend on any axioms" in output,
                    f"Missing transitive axiom report: {spec}")


def audit(manifest: Path, metadata_only: bool, require_complete: bool) -> None:
    campaign = read_json(manifest)
    context = review_context()
    rows = validate_scope(campaign, context)
    accepted = [row for row in rows if row["status"] == "accepted"]
    specs = [row["public_spec"] for row in accepted]
    require(len(set(specs)) == len(specs), "Duplicate accepted public specification")
    callers = {validate_receipt(row, context) for row in accepted}
    if require_complete:
        require(len(accepted) == SCOPE_COUNT,
                f"Goal incomplete: {len(accepted)}/137 accepted; "
                "findings do not silently shrink scope")
    counts = Counter(row["status"] for row in rows)
    print("Exact campaign: " + ", ".join(f"{n} {s}" for s, n in sorted(counts.items())), flush=True)
    if metadata_only:
        print("Metadata/receipt checks only; Lean theorem and caller checks were not run.")
        return
    run(["lake", "build"])
    imports = (ROOT / "SampLib.lean").read_text().splitlines()
    for row in accepted:
        require(f"import {current_module(row['proof_module'])}" in imports,
                f"Accepted proof missing from public root: {row['sampler']}")
    if accepted:
        commands = []
        for row in accepted:
            command = SPEC_AUDIT_COMMANDS[row["spec_kind"]]
            commands.extend([f"{command} {row['public_spec']} for {row['sampler']}",
                             f"#check {row['public_spec']}", f"#print axioms {row['public_spec']}"])
        with tempfile.TemporaryDirectory(prefix="samplib-exact-audit-") as directory:
            path = Path(directory) / "Audit.lean"
            header = lean_audit_header({row["spec_kind"] for row in accepted})
            path.write_text(header + "\n".join(commands) + "\n")
            output = run(["lake", "env", "lean", str(path)])
        expected = [(row["public_spec"], row["sampler"]) for row in accepted]
        require(re.findall(r"^SPEC_OK (\S+) (\S+)$", output, re.M) == expected,
                "Checked specification/program pairs differ from accepted rows")
        validate_axioms(output, specs)
        for caller in sorted(callers):
            # Build the caller's imports first: `lake env lean` alone would accept
            # stale build output for modules that `lake build` no longer covers.
            run(["lake", "build", *caller_imports(caller)])
            run(["lake", "env", "lean", caller])
    from statement_pins import PINS, check as changed_statements

    if PINS.exists():
        changed = changed_statements()
        require(not changed, "Public statements differ from their pins: " + ", ".join(changed))
    require(read_json(manifest) == campaign,
            "Campaign changed during audit; rerun the current state")
    require(review_context() == context, "Dependency context changed during audit")
    validate_scope(campaign, context)
    for row in accepted:
        validate_receipt(row, context)
    print(f"Audited {len(accepted)}/137 independently reviewed exact sampler specifications.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--metadata-only", action="store_true",
                        help="check frozen scope and receipts without claiming Lean validation")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    try:
        audit(args.manifest, args.metadata_only, args.require_complete)
    except (AuditError, KeyError, TypeError, ValueError, OSError) as error:
        raise SystemExit(f"Exact campaign audit failed: {error}") from error


if __name__ == "__main__":
    main()
