"""Check vector/conditional heads and reject circular specification premises."""

from pathlib import Path
import tempfile

from audit_exact_sampler_proofs import lean_audit_header, require, run, validate_axioms
from proof_dependencies import ROOT
from relocation import current_imports


with tempfile.TemporaryDirectory(prefix='samplib-exact-signatures-') as directory:
    path = Path(directory) / 'Cases.lean'
    header = lean_audit_header({'plain', 'owned', 'latent_coin', 'latent_real', 'latent_vector',
                                'conditional_coin'})
    header = header.replace('import SampLib\n',
                            'import SampLib\nimport SampLib.Samplers.PSRNInsideShape\nimport SampLib.PSRNCoin\n')
    cases = (ROOT/'agent-scripts/exact_audit_signature_cases.lean').read_text()
    path.write_text(current_imports(header) + cases)
    output = run(['lake', 'env', 'lean', str(path)])
    require(output.count('SPEC_OK ') == 2, 'Expected valid vector and conditional-coin specifications')
    validate_axioms(output, ['ExactAuditRegression.circularVector',
                             'ExactAuditRegression.circularPayload',
                             'ExactAuditRegression.circularCoin'])
