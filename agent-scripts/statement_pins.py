#!/usr/bin/env python3
"""Pin what each accepted public spec states, so proof refactors cannot change it.

A statement fingerprint hashes a public spec's type together with the type and body of
every project definition (`SampLib.*`) that the type mentions, followed transitively.
Proof bodies of theorems are excluded, so proofs may change freely while the meaning of
every public statement stays fixed. `--check` recomputes all fingerprints from the
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
open Lean Elab Command in
/-- Hash a theorem's type with every project definition it depends on. -/
elab "#statement_fingerprint " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  let some info := env.find? root | throwError "unknown constant {root}"
  let mut todo := info.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut parts : Array (String × UInt64) := #[("", info.type.hash)]
  while h : 0 < todo.size do
    let name := todo.back
    todo := todo.pop
    if seen.contains name || !(`SampLib).isPrefixOf name then
      continue
    seen := seen.insert name
    match env.find? name with
    | some (.defnInfo d) =>
        parts := parts.push (name.toString, mixHash d.type.hash d.value.hash)
        todo := todo ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | some (.inductInfo d) =>
        parts := parts.push (name.toString, d.type.hash)
        todo := todo ++ d.type.getUsedConstants ++ d.ctors.toArray
    | some ci =>
        parts := parts.push (name.toString, ci.type.hash)
        todo := todo ++ ci.type.getUsedConstants
    | none => pure ()
  let sorted := parts.qsort (fun a b => a.1 < b.1)
  let digest := sorted.foldl (fun acc p => mixHash acc (mixHash (hash p.1) p.2)) 7
  logInfo m!"STATEMENT {root} {digest} {sorted.size}"
'''


def fingerprints(specs: list[str], cwd: Path = ROOT) -> dict[str, str]:
    """Compute fingerprints from the compiled library in `cwd`."""
    source = "import SampLib\n" + LEAN_COMMAND + "".join(
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
