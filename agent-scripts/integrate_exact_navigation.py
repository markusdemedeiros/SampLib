#!/usr/bin/env python3
"""Expose reviewed exact-campaign proofs without rewriting the historic campaign."""

from collections import Counter

from audit_exact_sampler_proofs import MANIFEST, read_json, require, validate_receipt, validate_scope
from proof_dependencies import ROOT, review_context
from relocation import current_module, module_path


def main() -> None:
    context = review_context()
    campaign_bytes = MANIFEST.read_bytes()
    campaign = read_json(MANIFEST)
    rows = validate_scope(campaign, context)
    accepted = [row for row in rows if row['status'] == 'accepted']
    for row in accepted:
        validate_receipt(row, context)

    root_path = ROOT / 'SampLib.lean'
    imports = root_path.read_text()
    for module in sorted({current_module(row['proof_module']) for row in accepted}):
        line = f'import {module}'
        if line not in imports.splitlines():
            imports += line + '\n'

    start, end = '<!-- exact:start -->', '<!-- exact:end -->'
    kinds = Counter(row['classification'] for row in accepted)
    lines = [
        start, '## Exact verification campaign', '',
        f'**{len(accepted)} of 137 entries accepted** in the '
        '[current campaign](../agent-docs/ExactVerificationCampaign.md). '
        'This table extends the historical suite above; supporting interfaces and derived '
        'wrappers are identified explicitly.', '',
        '| Sampler | Kind | Domain | Proof | Review |',
        '| --- | --- | --- | --- | --- |',
    ]
    for row in accepted:
        proof = module_path(row['proof_module'])
        proof_target = proof.removeprefix('SampLib/')
        domain = ' '.join(row['reviewed_domain'].split()).replace('|', '&#124;')
        lines.append(
            f"| `{row['sampler']}` | {row['classification']} | {domain} | "
            f"[{row['public_spec']}]({proof_target}) | "
            f"[review](../{row['review_evidence']}) |"
        )
    lines.extend(['', end])
    block = '\n'.join(lines)
    suite_path = ROOT / 'SampLib/README.md'
    suite = suite_path.read_text()
    if start in suite:
        before, tail = suite.split(start, 1)
        _, after = tail.split(end, 1)
        suite = before + block + after
    else:
        suite = suite.rstrip() + '\n\n' + block + '\n'

    require(MANIFEST.read_bytes() == campaign_bytes, 'Campaign changed during integration; retry')
    require(review_context() == context, 'Dependency context changed during integration')
    root_path.write_text(imports)
    suite_path.write_text(suite)
    counts = ', '.join(f'{n} {kind}' for kind, n in sorted(kinds.items()))
    print(f'Published {len(accepted)}/137 exact campaign entries ({counts}).')


if __name__ == '__main__':
    main()
