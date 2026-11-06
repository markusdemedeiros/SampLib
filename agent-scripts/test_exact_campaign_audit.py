#!/usr/bin/env python3
"""Adversarial checks for the exact campaign's acceptance boundaries."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import audit_exact_sampler_proofs as audit
import exact_source_repairs as repairs
from proof_dependencies import review_context


class ExactCampaignAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.campaign = audit.read_json(audit.MANIFEST)
        cls.context = review_context()

    def setUp(self):
        self.campaign = deepcopy(type(self).campaign)
        self.context = deepcopy(type(self).context)

    def test_original_scope_validates(self):
        rows = audit.validate_scope(self.campaign, self.context)
        self.assertEqual(len(rows), 137)
        self.assertEqual(len({row['sampler'] for row in rows}), 137)

    def test_coordinated_scope_shrink_is_rejected(self):
        self.campaign['scope_count'] = 136
        self.campaign['scope_sampler_names'].pop()
        self.campaign['candidates'].pop()
        with self.assertRaisesRegex(audit.AuditError, 'scope must remain 137'):
            audit.validate_scope(self.campaign, self.context)

    def test_duplicate_scope_name_is_rejected(self):
        names = self.campaign['scope_sampler_names']
        names[-1] = names[0]
        with self.assertRaisesRegex(audit.AuditError, 'Duplicate frozen scope'):
            audit.validate_scope(self.campaign, self.context)

    def test_reordered_candidate_attribution_is_rejected(self):
        rows = self.campaign['candidates']
        rows[0], rows[1] = rows[1], rows[0]
        with self.assertRaisesRegex(audit.AuditError, 'scope/order changed'):
            audit.validate_scope(self.campaign, self.context)

    def test_changed_dependency_context_is_rejected(self):
        self.context['packages']['clutch-lean'] = '0' * 40
        with self.assertRaisesRegex(audit.AuditError, 'dependency context changed'):
            audit.validate_scope(self.campaign, self.context)

    def test_stale_implementation_snapshot_is_rejected(self):
        snapshots = self.campaign['baseline']['implementation_snapshot']
        snapshots[next(iter(snapshots))] = '0' * 64
        with self.assertRaisesRegex(audit.AuditError, 'implementation changed'):
            audit.validate_scope(self.campaign, self.context)

    def test_author_cannot_be_own_reviewer(self):
        row = self.campaign['candidates'][0]
        row['reviewer'] = row['owner']
        with self.assertRaisesRegex(audit.AuditError, 'Author cannot review own proof'):
            audit.validate_receipt(row, self.context)

    def test_short_reviewer_alias_cannot_bypass_independence(self):
        row = self.campaign['candidates'][0]
        row['reviewer'] = row['owner'].rsplit('/', 1)[-1]
        with self.assertRaisesRegex(audit.AuditError, 'Author cannot review own proof'):
            audit.validate_receipt(row, self.context)

    def test_root_identity_is_valid_but_malformed_paths_are_not(self):
        self.assertEqual(audit.agent_identity('/root'), '/root')
        for name in ['/', ' ', '/root/x/..', '/root/../review_exact_a']:
            with self.subTest(identity=name):
                with self.assertRaises(audit.AuditError):
                    audit.agent_identity(name)

    def test_missing_axiom_evidence_is_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, 'Missing transitive axiom report'):
            audit.validate_axioms('', ['Sampler.spec'])

    def test_sorry_and_foreign_axioms_are_rejected(self):
        for name in ['sorryAx', 'Sampler.assumed_correct']:
            with self.subTest(axiom=name):
                output = f"'Sampler.spec' depends on axioms: [propext, {name}]"
                with self.assertRaisesRegex(audit.AuditError, 'Unapproved axioms'):
                    audit.validate_axioms(output, ['Sampler.spec'])

    def test_standard_axioms_are_allowed(self):
        audit.validate_axioms(
            "'Sampler.spec' depends on axioms: [propext, Classical.choice, Quot.sound]",
            ['Sampler.spec'],
        )
        audit.validate_axioms("'Sampler.spec' does not depend on any axioms", ['Sampler.spec'])

    def test_findings_cannot_make_incomplete_campaign_complete(self):
        for row in self.campaign['candidates']:
            row['status'] = 'pending'
        self.campaign['candidates'][0].update(
            status='finding', finding={'summary': 'Actual domain defect', 'evidence': 'AGENTS.md'},
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Campaign.json'
            path.write_text(json.dumps(self.campaign))
            with patch.object(audit, 'review_context', return_value=self.context):
                with patch.object(audit, 'run') as run:
                    with self.assertRaisesRegex(audit.AuditError, 'Goal incomplete: 0/137'):
                        audit.audit(path, metadata_only=True, require_complete=True)
                    run.assert_not_called()


class SourceRepairTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        root_patch = patch.object(repairs, 'ROOT', self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        self.original = self.root / 'before.txt'
        self.original.write_text('def sampler := 1\n')
        self.current = self.root / 'sampler.lean'
        self.current.write_text('def sampler := 2\n')
        evidence = self.root / 'review.md'
        evidence.write_text('Independent review of the exact proposed change.\n')
        self.context = {'packages': {'clutch-lean': 'current'}}
        self.review = {
            'kind': 'implementation_repair_review', 'author': '/root',
            'reviewer': '/root/review_exact_a', 'context': self.context,
            'checks': ['source', 'domain', 'other_definitions'],
            'review_evidence': 'review.md', 'review_evidence_sha256': repairs.sha256(evidence),
            'changes': [{
                'path': 'sampler.lean', 'before_source': 'before.txt',
                'before_sha256': repairs.sha256(self.original),
                'after_sha256': repairs.sha256(self.current), 'samplers': ['Occil.sampler'],
                'replacements': [{'before': ':= 1', 'after': ':= 2'}],
            }],
        }
        self.campaign = {
            'baseline': {'implementation_snapshot': {'sampler.lean': repairs.sha256(self.original)}},
            'candidates': [{'sampler': 'Occil.sampler', 'implementation': 'sampler.lean'}],
            'implementation_repair_reviews': ['review.json'],
        }

    def validate(self):
        (self.root / 'review.json').write_text(json.dumps(self.review))
        return repairs.validate_source_repairs(self.campaign, self.context)

    def test_exact_reviewed_patch_is_accepted_without_rewriting_original(self):
        frozen = deepcopy(self.campaign['baseline'])
        self.assertEqual(self.validate(), {'sampler.lean': repairs.sha256(self.current)})
        self.assertEqual(self.campaign['baseline'], frozen)

    def test_extra_source_edit_is_rejected_even_with_updated_result_hash(self):
        self.current.write_text('def sampler := 2\naxiom assumed : False\n')
        self.review['changes'][0]['after_sha256'] = repairs.sha256(self.current)
        with self.assertRaisesRegex(ValueError, 'differs from reviewed exact patch'):
            self.validate()

    def test_rewriting_original_cannot_hide_changed_baseline(self):
        self.original.write_text('def sampler := 9\n')
        self.review['changes'][0]['before_sha256'] = repairs.sha256(self.original)
        with self.assertRaisesRegex(ValueError, 'differs from frozen baseline'):
            self.validate()

    def test_repair_cannot_name_an_out_of_scope_sampler(self):
        self.review['changes'][0]['samplers'] = ['Occil.other']
        with self.assertRaisesRegex(ValueError, 'out-of-scope sampler'):
            self.validate()

    def test_patch_must_identify_a_unique_location(self):
        self.review['changes'][0]['replacements'][0]['before'] = ':= 9'
        with self.assertRaisesRegex(ValueError, 'not unique'):
            self.validate()

    def test_stale_review_context_is_rejected(self):
        self.review['context'] = {'packages': {'clutch-lean': 'old'}}
        with self.assertRaisesRegex(ValueError, 'dependency context changed'):
            self.validate()

    def test_changed_review_evidence_is_rejected(self):
        (self.root / 'review.md').write_text('Replaced after review.\n')
        with self.assertRaisesRegex(ValueError, 'repair evidence changed'):
            self.validate()

    def test_repair_cannot_be_self_reviewed_through_an_alias(self):
        self.review.update(author='/root/review_exact_a', reviewer='review_exact_a')
        with self.assertRaisesRegex(ValueError, 'cannot review own change'):
            self.validate()

    def test_malformed_repair_identities_are_rejected(self):
        for name in ['/', ' ', '/root/x/..', '/root/../review_exact_a']:
            with self.subTest(identity=name):
                self.review['reviewer'] = name
                with self.assertRaisesRegex(ValueError, 'Malformed repair'):
                    self.validate()


if __name__ == '__main__':
    unittest.main()
