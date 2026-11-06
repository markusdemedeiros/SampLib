"""Validate independently reviewed patches against the campaign's original sources."""

import json
import re

from proof_dependencies import ROOT, sha256


def local_file(name):
    if not isinstance(name, str) or not name:
        raise ValueError('Repair artifact path is missing')
    path = ROOT / name
    if not path.resolve().is_relative_to(ROOT) or not path.is_file():
        raise ValueError(f'Repair artifact is missing or outside the repository: {name}')
    return path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def identity(name):
    require(isinstance(name, str) and bool(name), 'Repair author/reviewer is missing')
    if name == '/root':
        return name
    name = name.removeprefix('/root/')
    require(re.fullmatch(r'[a-z][a-z0-9_]*', name) is not None,
            'Malformed repair author/reviewer identity')
    return '/root/' + name


def validate_source_repairs(campaign, context):
    """Return reviewed current hashes; retain the original baseline unchanged.

    Each receipt binds the original bytes, exact replacements, resulting bytes,
    affected goal entries and independent review. This approves an implementation
    repair, not its sampler proof or any stale transitive proof snapshot.
    """
    original = campaign['baseline']['implementation_snapshot']
    candidates = {row['sampler']: row['implementation'] for row in campaign['candidates']}
    result = {}
    for name in campaign.get('implementation_repair_reviews', []):
        review = json.loads(local_file(name).read_text())
        require(review.get('kind') == 'implementation_repair_review', 'Unknown repair review kind')
        require(review.get('context') == context, 'Repair review dependency context changed')
        require(identity(review.get('author')) != identity(review.get('reviewer')),
                'Repair author cannot review own change')
        require({'source', 'domain', 'other_definitions'} <= set(review.get('checks', [])),
                'Implementation repair review is incomplete')
        evidence = local_file(review.get('review_evidence'))
        require(sha256(evidence) == review.get('review_evidence_sha256'),
                'Implementation repair evidence changed')
        changes = review.get('changes', [])
        require(bool(changes), 'Repair review has no changes')
        for change in changes:
            path = change.get('path')
            require(path in original and path not in result, 'Unpinned or duplicate repaired source')
            before = local_file(change.get('before_source'))
            require(sha256(before) == original[path] == change.get('before_sha256'),
                    'Repair original source differs from frozen baseline')
            samplers = change.get('samplers', [])
            require(bool(samplers) and len(set(samplers)) == len(samplers),
                    'Repair must name its affected sampler entries')
            require(all(candidates.get(sampler) == path for sampler in samplers),
                    'Repair identifies an out-of-scope sampler or different source')
            text = before.read_text()
            replacements = change.get('replacements', [])
            require(bool(replacements), 'Repair has no exact replacements')
            for replacement in replacements:
                old, new = replacement.get('before'), replacement.get('after')
                require(isinstance(old, str) and bool(old) and isinstance(new, str) and old != new,
                        'Invalid repair replacement')
                require(text.count(old) == 1, 'Repair replacement is not unique in original source')
                text = text.replace(old, new, 1)
            current = local_file(path)
            require(current.read_bytes() == text.encode(), 'Source differs from reviewed exact patch')
            digest = sha256(current)
            require(digest == change.get('after_sha256') and digest != original[path],
                    'Repair resulting source digest differs')
            result[path] = digest
    return result
