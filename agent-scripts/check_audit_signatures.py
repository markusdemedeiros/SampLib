"""Check that proof-local instances pass without admitting circular specs."""

from pathlib import Path
import tempfile

from audit_sampler_proofs import LEAN_HEADER, ROOT, run_lean
from relocation import current_imports


with tempfile.TemporaryDirectory(prefix="samplib-signature-regression-") as directory:
    path = Path(directory) / "Cases.lean"
    cases = (ROOT / "agent-scripts/audit_signature_cases.lean").read_text()
    path.write_text(current_imports(LEAN_HEADER) + cases)
    output = run_lean(path)
    if output.count("SPEC_OK ") != 3:
        raise SystemExit("Expected both ordinary specs and the owned spec to pass")
