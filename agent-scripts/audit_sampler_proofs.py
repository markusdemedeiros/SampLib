#!/usr/bin/env python3
"""Check independently reviewed sampler specs against final compiled sources.

Human review establishes the mathematical interpretation and protocol fit. This
check binds those reviews to source/dependency snapshots, checks actual program
heads and non-circular spec signatures, and audits transitive Lean axioms.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

from proof_dependencies import ROOT, review_context, sha256, source_snapshot
from expansion_state import verify_expansion_state
from relocation import (current_imports, current_module, current_path, module_path,
                        relocate_context, relocate_file, relocate_snapshot)

MANIFEST = ROOT / "agent-docs/VerificationCampaign.json"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_CHECKS = {"source", "build", "axioms", "caller", "boundaries"}
BASELINE = {
    "Occil.realCoin": ("SampLib.Samplers.RealCoin", "SampLib.RealCoin.realCoin_distSpec",
                       "code/Samplers/Uniform.lean"),
    "Occil.vonNeumann": ("SampLib.Samplers.VonNeumann", "SampLib.VonNeumann.vonNeumann_distSpec",
                         "code/Samplers/Bernoulli/Basic.lean"),
}
CALLERS = ["agent-docs/reviews/CoinCallers.lean", "agent-docs/reviews/DiscreteCallers.lean",
           "agent-docs/reviews/StructuredCallers.lean",
           "agent-docs/reviews/NextBatchWeightedFactoriesCallers.lean",
           "agent-docs/reviews/NextBatchFiniteCallers.lean",
           "agent-docs/reviews/NextBatchContinuousCallers.lean",
           "agent-docs/reviews/NextBatchBinomialMathCallers.lean"]


def valid_review_caller(path: str) -> bool:
    return path in CALLERS or re.fullmatch(
        r"agent-docs/reviews/Expansion(?:Factories|Discrete|Structured)"
        r"Batch[0-9]{3}Callers\.lean", path
    ) is not None

LEAN_HEADER = r'''import SampLib
import SampLib.OwnedDistSpec
import Lean.Elab.Command

open Lean Meta Elab Command

private partial def stripLets (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => stripLets (body.instantiate1 value)
  | e => e

private partial def parameterIndex (name : Name) (e : Expr) (i : Nat := 0) : Option Nat :=
  match e with
  | .forallE n _ body _ => if n == name then some i else parameterIndex name body (i + 1)
  | .mdata _ body => parameterIndex name body i
  | _ => none

private partial def programHead (e : Expr) : Expr :=
  let e := stripLets e
  if e.getAppFn.isConstOf ``ProbLang.Exp.app then
    let args := e.getAppArgs
    if args.size ≥ 2 then programHead args[args.size - 2]! else e
  else e

private partial def containsOwnSpec (target : Name) (fuel : Nat) (e : Expr) : MetaM Bool := do
  if fuel == 0 then throwError "Premise inspection exhausted its structural bound"
  let e ← withTransparency .reducible (whnf (stripLets e))
  let e := stripLets e
  let head := e.getAppFn
  if head.isConstOf ``SampLib.IsDistSpec || head.isConstOf ``SampLib.IsOwnedDistSpec then
    let specInfo ← getConstInfo head.constName!
    let some index := parameterIndex `e specInfo.type
      | throwError "Cannot locate distribution specification's program parameter"
    let args := e.getAppArgs
    if index < args.size then
      return (programHead args[index]!).getAppFn.isConstOf target
    return false
  match e with
  | .forallE n domain body bi =>
      if (← containsOwnSpec target (fuel - 1) domain) then return true
      withLocalDecl n bi domain fun x =>
        containsOwnSpec target (fuel - 1) (body.instantiate1 x)
  | .lam n domain body bi =>
      withLocalDecl n bi domain fun x =>
        containsOwnSpec target (fuel - 1) (body.instantiate1 x)
  | _ =>
      if [``And, ``Or, ``Iff, ``Exists].any (fun name => head.isConstOf name) then
        for arg in e.getAppArgs do
          if (← containsOwnSpec target (fuel - 1) arg) then return true
      return false

private def auditSpecification (theoremName samplerName specName : Name) : CommandElabM Unit := do
  let info ← getConstInfo theoremName
  let specInfo ← getConstInfo specName
  let label := if specName == ``SampLib.IsDistSpec then "IsDistSpec" else "IsOwnedDistSpec"
  let some index := parameterIndex `e specInfo.type
    | throwError "Cannot locate {label}'s program parameter"
  let _ ← getConstInfo samplerName
  liftTermElabM do
    forallTelescopeReducing info.type fun params result => do
      let result := stripLets result
      unless result.getAppFn.isConstOf specName do
        throwError "{theoremName} does not conclude with {label}"
      let args := result.getAppArgs
      unless index < args.size do throwError "Incomplete {label} application"
      unless (programHead args[index]!).getAppFn.isConstOf samplerName do
        throwError "{theoremName} does not specify a call to {samplerName}"
      for param in params do
        let premise ← inferType param
        if (← containsOwnSpec samplerName 128 premise) then
          throwError "{theoremName} assumes its own concrete sampler in a premise"
      logInfo m!"SPEC_OK {theoremName} {samplerName}"

elab "#audit_dist_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.IsDistSpec

elab "#audit_owned_dist_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.IsOwnedDistSpec

'''


def fail(message: str) -> None:
    raise SystemExit(message)


def run_lean(path: Path) -> str:
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="")
    if result.returncode or "warning:" in result.stdout:
        fail(f"Lean check failed or emitted warnings: {path}")
    return result.stdout


def verify_receipt(row: dict, context: dict) -> None:
    receipt_path = row.get("review_receipt")
    if not receipt_path or not (ROOT / receipt_path).is_file():
        fail(f"Missing reviewer-owned receipt for {row['sampler']}")
    receipt = json.loads((ROOT / receipt_path).read_text())
    if receipt.get("reviewer") != row["reviewer"] or row["owner"] == row["reviewer"]:
        fail(f"Independent reviewer mismatch for {row['sampler']}")
    if relocate_context(receipt.get("context")) != context:
        fail(f"Review configuration/dependency context changed: {receipt_path}")
    caller = receipt.get("caller_evidence")
    if not caller or not valid_review_caller(caller):
        fail(f"Missing reviewer-owned caller artifact: {receipt_path}")
    caller_path, caller_sha = relocate_file(caller, receipt.get("caller_sha256"))
    if not (ROOT / caller_path).is_file() or sha256(ROOT / caller_path) != caller_sha:
        fail(f"Reviewed caller/boundary checks changed: {caller}")
    for support in receipt.get("support", []):
        path = support.get("path")
        if path is None:
            path = support["module"].replace(".", "/") + ".lean"
        path, expected = relocate_file(path, support["sha256"])
        if sha256(ROOT / path) != expected:
            fail(f"Reviewed support source changed: {path}")
    matches = [entry for entry in receipt["accepted"] if entry["sampler"] == row["sampler"]]
    if len(matches) != 1:
        fail(f"No unique accepted reviewer receipt for {row['sampler']}")
    entry = matches[0]
    kind = row.get("spec_kind", "plain")
    if kind not in {"plain", "owned"} or entry.get("spec_kind", "plain") != kind:
        fail(f"Review specification kind mismatch for {row['sampler']}")
    for field in ("proof_module", "public_spec", "review_evidence"):
        if entry.get(field) != row.get(field):
            fail(f"Review {field} mismatch for {row['sampler']}")
    if entry.get("sha256") != row.get("reviewed_sha256"):
        fail(f"Reviewed direct source differs for {row['sampler']}")
    if not REQUIRED_CHECKS <= set(entry.get("checks", [])):
        fail(f"Incomplete independent checks for {row['sampler']}")
    snapshot = source_snapshot(row["proof_module"], row["implementation"])
    if relocate_snapshot(entry.get("source_snapshot")) != snapshot:
        fail(f"Transitive project source review is stale: {row['sampler']}")
    recorded = row["proof_module"].replace(".", "/") + ".lean"
    if sha256(ROOT / module_path(row["proof_module"])) != relocate_file(
            recorded, row["reviewed_sha256"])[1]:
        fail(f"Reviewed proof source changed: {row['sampler']}")
    evidence = ROOT / row["review_evidence"]
    if not evidence.is_file():
        fail(f"Review evidence missing: {evidence}")
    text = evidence.read_text()
    if row["public_spec"] not in text or row["reviewed_sha256"] not in text:
        fail(f"Prose evidence does not identify this reviewed spec/hash: {row['sampler']}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--check-callers", action="store_true",
                        help="check all accepted callers while a campaign is still active")
    args = parser.parse_args()
    campaign = json.loads(MANIFEST.read_text())
    accepted = [row for row in campaign["candidates"] if row["status"] == "accepted"]
    names = [row["sampler"] for row in accepted]
    specs = [row["public_spec"] for row in accepted]
    if len(names) != len(set(names)) or len(specs) != len(set(specs)):
        fail("Duplicate accepted sampler or public spec")
    if set(campaign["baseline"]) != set(BASELINE) or set(names) & set(BASELINE):
        fail("Baseline identity/count mismatch")
    if campaign.get("accepted") != names:
        fail("Redundant accepted list differs from accepted candidate rows")
    verify_expansion_state(campaign, args.require_complete)
    if campaign["target_new_samplers"] < 30 or campaign["target_total_samplers"] < 32:
        fail("Campaign metadata weakens the requested objective")
    if args.require_complete:
        if len(accepted) < max(30, campaign["target_new_samplers"]):
            fail(f"Only {len(accepted)} new accepted samplers; at least30 required")
        if len(accepted) + len(BASELINE) < max(32, campaign["target_total_samplers"]):
            fail("Requested total suite size is not met")
    if not accepted:
        fail("No independently accepted proofs to audit yet")

    context = review_context()
    root_imports = (ROOT / "SampLib.lean").read_text().splitlines()
    audited = []
    for row in accepted:
        verify_receipt(row, context)
        if f"import {current_module(row['proof_module'])}" not in root_imports:
            fail(f"Root import missing for {row['sampler']}")
        audited.append((row["sampler"], row["public_spec"]))
    baseline_records = {row["sampler"]: row for row in campaign.get("baseline_records", [])}
    for sampler, (module, spec, implementation) in BASELINE.items():
        row = baseline_records.get(sampler)
        if not row or relocate_snapshot(row.get("source_snapshot")) != source_snapshot(
                module, implementation):
            fail(f"Baseline source snapshot missing or stale: {sampler}")
        if f"import {current_module(module)}" not in root_imports:
            fail(f"Baseline root import missing: {sampler}")
        audited.append((sampler, spec))

    build = subprocess.run(["lake", "build"], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(build.stdout, end="")
    if build.returncode or "warning:" in build.stdout:
        fail("Full project build failed or emitted warnings")
    commands = []
    kinds = {row["sampler"]: row.get("spec_kind", "plain") for row in accepted}
    for sampler, spec in audited:
        command = "#audit_owned_dist_spec" if kinds.get(sampler) == "owned" else "#audit_dist_spec"
        commands += [f"{command} {spec} for {sampler}", f"#check {spec}", f"#print axioms {spec}"]
    with tempfile.TemporaryDirectory(prefix="samplib-proof-audit-") as directory:
        audit = Path(directory) / "Audit.lean"
        audit.write_text(current_imports(LEAN_HEADER) + "\n".join(commands) + "\n")
        output = run_lean(audit)
    found = re.findall(r"^SPEC_OK (\S+) (\S+)$", output, re.M)
    expected = [(spec, sampler) for sampler, spec in audited]
    if found != expected:
        fail("Checked spec/sampler pairs differ from the requested audit")
    for _, spec in audited:
        match = re.search(re.escape(f"'{spec}' depends on axioms:") + r"\s*\[([^]]*)\]", output)
        if match:
            axioms = {name.strip() for name in match[1].split(",") if name.strip()}
            if axioms - STANDARD_AXIOMS:
                fail(f"Unapproved axioms for {spec}: {axioms - STANDARD_AXIOMS}")
        elif f"'{spec}' does not depend on any axioms" not in output:
            fail(f"Missing exact transitive axiom audit for {spec}")
    if args.require_complete or args.check_callers:
        receipt_callers = {
            json.loads((ROOT / row["review_receipt"]).read_text())["caller_evidence"]
            for row in accepted
        }
        for filename in dict.fromkeys([*CALLERS, *sorted(receipt_callers)]):
            path = ROOT / current_path(filename)
            if not path.is_file():
                fail(f"Missing reproducible independent caller checks: {filename}")
            run_lean(path)
    # Recheck after compilation: a concurrent edit invalidates this run.
    if review_context() != context:
        fail("Configuration/dependency context changed during the audit")
    for row in accepted:
        verify_receipt(row, context)
    for sampler, (module, _, implementation) in BASELINE.items():
        if relocate_snapshot(baseline_records[sampler]["source_snapshot"]) != source_snapshot(
                module, implementation):
            fail(f"Baseline changed during the audit: {sampler}")
    print(f"Audited {len(accepted)} distinct new, independently reviewed samplers; "
          f"{len(audited)} sampler specifications including both baselines.")


if __name__ == "__main__":
    main()
