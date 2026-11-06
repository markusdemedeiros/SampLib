"""Regression checks for immutable review batches and stale evidence."""

import json
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import audit_sampler_proofs as audit
import expansion_state
import integrate_expansion as integration
from integrate_expansion import proof_kind
from proof_dependencies import sha256


class ReviewReceiptTests(unittest.TestCase):
    def test_immutable_batch_paths(self):
        for group in ("Factories", "Discrete", "Structured"):
            self.assertTrue(audit.valid_review_caller(
                f"agent-docs/reviews/Expansion{group}Batch001Callers.lean"))
        for path in ("../ExpansionDiscreteBatch001Callers.lean",
                     "agent-docs/reviews/ExpansionDiscreteCallers.lean",
                     "agent-docs/reviews/ExpansionDiscreteBatch001Callers.py"):
            self.assertFalse(audit.valid_review_caller(path))

    def test_changed_caller_or_transitive_source_invalidates_acceptance(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            caller = "agent-docs/reviews/ExpansionDiscreteBatch001Callers.lean"
            proof = "SampLib/Samplers/Example.lean"
            helper = "SampLib/Helper.lean"
            evidence = "agent-docs/reviews/Example.md"
            receipt = "agent-docs/reviews/Example.json"
            for relative in (caller, proof, helper, evidence):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("original\n")

            def snapshot(*_):
                return {name: sha256(root / name) for name in (proof, helper)}

            digest = sha256(root / proof)
            (root / evidence).write_text(f"Example.spec {digest}\n")
            row = dict(sampler="Occil.example", owner="author", reviewer="reviewer",
                       proof_module="SampLib.Samplers.Example", public_spec="Example.spec",
                       reviewed_sha256=digest, review_evidence=evidence, review_receipt=receipt,
                       implementation="code/Samplers/Example.lean")
            entry = dict(sampler=row["sampler"], proof_module=row["proof_module"],
                         public_spec=row["public_spec"], review_evidence=evidence,
                         sha256=digest, checks=sorted(audit.REQUIRED_CHECKS),
                         source_snapshot=snapshot())
            (root / receipt).write_text(json.dumps(dict(
                reviewer="reviewer", context={}, accepted=[entry], caller_evidence=caller,
                caller_sha256=sha256(root / caller))))
            with patch.object(audit, "ROOT", root), patch.object(audit, "source_snapshot", snapshot):
                audit.verify_receipt(row, {})
                row["spec_kind"] = "owned"
                with self.assertRaisesRegex(SystemExit, "specification kind mismatch"):
                    audit.verify_receipt(row, {})
                row.pop("spec_kind")
                (root / caller).write_text("changed caller\n")
                with self.assertRaisesRegex(SystemExit, "caller/boundary checks changed"):
                    audit.verify_receipt(row, {})
                (root / caller).write_text("original\n")
                (root / helper).write_text("changed transitive helper\n")
                with self.assertRaisesRegex(SystemExit, "Transitive project source review is stale"):
                    audit.verify_receipt(row, {})


class ExpansionAccountingTests(unittest.TestCase):
    def test_two_independent_reviews_count_one_sampler(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = [f"Old.sampler{i}" for i in range(47)]
            prior = [dict(sampler=name, status="accepted", proof_module=f"Old.Module{i}",
                          public_spec=f"Old.spec{i}", reviewed_domain="Prior domain")
                     for i, name in enumerate(baseline[2:])]
            name = "New.sampler"
            primary = dict(sampler=name, status="accepted", owner="author",
                           reviewer="/root/primary", proof_module="New.Module",
                           public_spec="New.spec", reviewed_domain="Full domain")
            secondary = dict(primary, reviewer="/root/secondary")
            files = {
                "agent-docs/VerificationCampaign.json": dict(
                    baseline=baseline[:2], candidates=prior),
                "agent-docs/ExpansionCampaign.json": dict(
                    baseline_sampler_names=baseline, baseline_sampler_count=47,
                    minimum_additional=120,
                    candidates=[dict(sampler=name, reviewer="primary", status="assigned")]),
                "agent-docs/reviews/ExpansionFactoriesCandidates.json": [],
                "agent-docs/reviews/ExpansionDiscreteCandidates.json": [primary],
                "agent-docs/reviews/ExpansionStructuredCandidates.json": [secondary],
            }
            for relative, value in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps(value))
            for relative in ("SampLib.lean", "README.md", "agent-scripts/readme_index.py",
                             "SampLib/README.md"):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("## Reading and checking the proofs\n")
            with patch.object(integration, "ROOT", root), \
                    patch.object(integration, "review_context", return_value={}), \
                    patch.object(integration, "verify_receipt") as verify, \
                    patch("sys.argv", ["integrate_expansion.py"]), \
                    contextlib.redirect_stdout(io.StringIO()):
                integration.main()
            self.assertEqual(verify.call_count, 2)
            campaign = json.loads((root / "agent-docs/VerificationCampaign.json").read_text())
            matches = [row for row in campaign["candidates"] if row["sampler"] == name]
            self.assertEqual(len(matches), 1)
            self.assertEqual(matches[0]["reviewer"], "/root/primary")
            self.assertEqual(len(campaign["accepted"]), 46)

    def test_review_classifications_are_preserved(self):
        for field in ("proof_kind", "algorithm_kind", "classification"):
            self.assertEqual(proof_kind(dict(sampler="Example", **{field: "derived"})),
                             "derived")
        with self.assertRaisesRegex(SystemExit, "Conflicting proof classifications"):
            proof_kind(dict(sampler="Example", proof_kind="core", classification="derived"))
        with self.assertRaisesRegex(SystemExit, "Not a counted sampler"):
            proof_kind(dict(sampler="Example", classification="helper"))

    def test_minimum_does_not_excuse_unfinished_candidates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = [f"Old.sampler{i}" for i in range(47)]
            log = root / "baseline.log"
            log.write_text("".join(f"SPEC_OK Old.spec{i} {name}\n"
                                   for i, name in enumerate(baseline)))
            additions = [dict(sampler=f"New.sampler{i}", status="accepted",
                              proof_module=f"New.Module{i}", public_spec=f"New.spec{i}",
                              reviewed_sha256=str(i), review_receipt=f"receipt{i}.json")
                         for i in range(120)]
            ledger = dict(baseline_sampler_names=baseline, baseline_sampler_count=47,
                          baseline_audit_log="baseline.log", baseline_audit_sha256=sha256(log),
                          minimum_additional=120,
                          candidates=additions + [dict(sampler="New.pending", status="assigned")],
                          accepted_additional=[row["sampler"] for row in additions])
            path = root / "expansion.json"
            path.write_text(json.dumps(ledger))
            campaign = dict(expansion_ledger="expansion.json", baseline=baseline[:2],
                            candidates=[dict(sampler=name, status="accepted")
                                        for name in baseline[2:]] + additions,
                            target_new_samplers=165, target_total_samplers=167)
            with patch.object(expansion_state, "ROOT", root):
                self.assertEqual(expansion_state.verify_expansion_state(campaign), 120)
                with self.assertRaisesRegex(SystemExit, "unfinished candidates"):
                    expansion_state.verify_expansion_state(campaign, require_complete=True)
                ledger["baseline_sampler_names"][0] = "New.pending"
                path.write_text(json.dumps(ledger))
                with self.assertRaisesRegex(SystemExit, "frozen 47-sampler audit"):
                    expansion_state.verify_expansion_state(campaign)


if __name__ == "__main__":
    unittest.main()
