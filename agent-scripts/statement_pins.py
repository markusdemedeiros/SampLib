#!/usr/bin/env python3
"""Pin what each accepted public spec states, so proof refactors cannot change it.

A statement fingerprint hashes a public spec's type together with the type and body of
every project definition (`SampLib.*`) that the type mentions, followed transitively.
Proofs are erased before hashing (they cannot change what a statement means), and private
names are read as their user-facing names, so proofs may change and helpers may become
public while the meaning of every public statement stays fixed. `--check` recomputes all fingerprints from the
current build and compares them with the pinned file.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PINS = ROOT / "agent-docs/PublicStatementPins.json"

LEAN_COMMAND = r'''
open Lean Meta Elab Command

/-- A private name read as its user-facing name, so making a lemma public changes nothing. -/
def statementName (n : Name) : Name := (privateToUserName? n).getD n

/-- Erase proofs and normalize constant names; record the constants that remain. -/
def statementExpr (e : Expr) (used : IO.Ref (Array Name)) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if !e.hasLooseBVars && (← (try isProof e catch _ => pure false)) then
      return .done (.const `proof [])
    if let .const n ls := e then
      used.modify (·.push n)
      return .done (.const (statementName n) ls)
    return .continue)

/-- Hash a theorem's type with every project definition it depends on, up to proofs. -/
elab "#statement_fingerprint " id:ident : command => liftTermElabM do
  let env ← getEnv
  let root := id.getId
  let some info := env.find? root | throwError "unknown constant {root}"
  let used ← IO.mkRef (#[] : Array Name)
  let rootType ← statementExpr info.type used
  let mut parts : Array (String × UInt64) := #[("", rootType.hash)]
  let mut seen : NameSet := {}
  let mut todo ← used.get
  used.set #[]
  while h : 0 < todo.size do
    let name := todo.back
    todo := todo.pop
    if seen.contains name || !(`SampLib).isPrefixOf (statementName name) then
      continue
    seen := seen.insert name
    let key := (statementName name).toString
    match env.find? name with
    | some (.defnInfo d) =>
        let ty ← statementExpr d.type used
        let val ← statementExpr d.value used
        parts := parts.push (key, mixHash ty.hash val.hash)
    | some (.inductInfo d) =>
        let ty ← statementExpr d.type used
        parts := parts.push (key, ty.hash)
        used.modify (· ++ d.ctors.toArray)
    | some ci =>
        let ty ← statementExpr ci.type used
        parts := parts.push (key, ty.hash)
    | none => pure ()
    todo := todo ++ (← used.get)
    used.set #[]
  let sorted := parts.qsort (fun a b => a.1 < b.1)
  if (← getOptions).getBool `statement.parts then
    for (k, v) in sorted do logInfo m!"PART {root} {k} {v}"
  let digest := sorted.foldl (fun acc p => mixHash acc (mixHash (hash p.1) p.2)) 7
  logInfo m!"STATEMENT {root} {digest} {sorted.size}"
'''


def fingerprints(specs: list[str], cwd: Path = ROOT, parts: bool = False) -> dict[str, str]:
    """Compute fingerprints from the compiled library in `cwd` (with `parts`, print each part)."""
    command = LEAN_COMMAND.replace("(← getOptions).getBool `statement.parts", str(parts).lower())
    source = "import SampLib\n" + command + "".join(
        f"#statement_fingerprint {spec}\n" for spec in specs)
    with tempfile.TemporaryDirectory(prefix="samplib-statements-") as directory:
        path = Path(directory) / "Statements.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=cwd, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    found = dict(re.findall(r"STATEMENT (\S+) (\d+) \d+", result.stdout))
    if result.returncode or set(found) != set(specs):
        raise ValueError(f"Statement fingerprinting failed:\n{result.stdout[-3000:]}")
    return found


def accepted_specs() -> list[str]:
    campaign = json.loads((ROOT / "agent-docs/ExactVerificationCampaign.json").read_text())
    specs = {row["public_spec"] for row in campaign["candidates"] if row["status"] == "accepted"}
    overlay = json.loads((ROOT / campaign["baseline_revalidation"]).read_text())
    specs |= {entry["public_spec"] for entry in overlay["entries"]}
    return sorted(specs)


def check(cwd: Path = ROOT) -> list[str]:
    """Return the public specs whose statement differs from its pin."""
    pins = json.loads(PINS.read_text())["statements"]
    current = fingerprints(sorted(pins), cwd)
    return sorted(spec for spec, digest in pins.items() if current[spec] != digest)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pin", type=Path, metavar="CHECKOUT",
                        help="write pins computed from a built checkout of the base commit")
    parser.add_argument("--commit", help="the commit that CHECKOUT holds")
    args = parser.parse_args()
    if args.pin:
        if PINS.exists():
            raise SystemExit("Statement pins are immutable; review any change explicitly")
        specs = accepted_specs()
        PINS.write_text(json.dumps({
            "schema_version": 1, "commit": args.commit,
            "meaning": ("Fingerprint of each accepted public spec's type and of every SampLib "
                        "definition it depends on. Proofs may change; these may not."),
            "statements": fingerprints(specs, args.pin)}, indent=1) + "\n")
        print(f"Pinned {len(specs)} public statements.")
        return
    changed = check()
    if changed:
        raise SystemExit("Public statements changed:\n" + "\n".join(changed))
    print("All pinned public statements are unchanged.")


if __name__ == "__main__":
    main()
