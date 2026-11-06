"""Check that proof-local instances pass without admitting circular specs."""

from pathlib import Path
import tempfile

from audit_sampler_proofs import LEAN_HEADER, ROOT, run_lean


with tempfile.TemporaryDirectory(prefix="samplib-signature-regression-") as directory:
    path = Path(directory) / "Cases.lean"
    path.write_text(LEAN_HEADER + (ROOT / "agent-scripts/audit_signature_cases.lean").read_text())
    output = run_lean(path)
    if output.count("SPEC_OK ") != 3:
        raise SystemExit("Expected both ordinary specs and the owned spec to pass")
