"""Relocations translate recorded reviews only through mechanical moves."""

import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import relocation


def git(root: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)


class RelocationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        files = {
            "SampLib/A.lean": "def a := 1\n",
            "SampLib/B.lean": "public import SampLib.A\nimport Mathlib\n\ntheorem b := rfl\n",
            "Callers.lean": "import SampLib.B\n",
            "Doc.md": "[a](SampLib/A.lean) [web](https://x.org/SampLib/A.lean) "
                      "[b](SampLib/B.lean)\n",
        }
        for name, text in files.items():
            (self.root / name).parent.mkdir(parents=True, exist_ok=True)
            (self.root / name).write_text(text)
        git(self.root, "init", "-q")
        git(self.root, "-c", "user.name=t", "-c", "user.email=t@t", "add", ".")
        git(self.root, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "base")
        self.before = {name: relocation.digest((self.root / name).read_bytes()) for name in files}
        self.patches = [patch.object(relocation, "ROOT", self.root),
                        patch.object(relocation, "RECORDS", self.root / "relocations")]
        for item in self.patches:
            item.start()
        relocation.records.cache_clear()
        relocation.apply({"SampLib/A.lean": "SampLib/Core/A.lean"},
                         self.root / "relocations/R001.json", "HEAD", ["Doc.md"])
        relocation.records.cache_clear()

    def tearDown(self) -> None:
        for item in self.patches:
            item.stop()
        relocation.records.cache_clear()
        self.directory.cleanup()

    def current(self, name: str) -> str:
        return relocation.digest((self.root / name).read_bytes())

    def test_moves_rewrite_only_references(self) -> None:
        self.assertEqual((self.root / "SampLib/B.lean").read_text(),
                         "public import SampLib.Core.A\nimport Mathlib\n\ntheorem b := rfl\n")
        self.assertEqual((self.root / "Callers.lean").read_text(), "import SampLib.B\n")
        self.assertEqual((self.root / "Doc.md").read_text(),
                         "[a](SampLib/Core/A.lean) [web](https://x.org/SampLib/A.lean) "
                         "[b](SampLib/B.lean)\n")
        self.assertFalse((self.root / "SampLib/A.lean").exists())
        self.assertEqual(relocation.current_module("SampLib.A"), "SampLib.Core.A")
        self.assertEqual(relocation.module_path("SampLib.B"), "SampLib/B.lean")

    def test_recorded_snapshot_translates_to_current_tree(self) -> None:
        recorded = {name: self.before[name] for name in ("SampLib/A.lean", "SampLib/B.lean")}
        self.assertEqual(relocation.relocate_snapshot(recorded),
                         {"SampLib/Core/A.lean": self.current("SampLib/Core/A.lean"),
                          "SampLib/B.lean": self.current("SampLib/B.lean")})

    def test_stale_recorded_hash_stays_stale(self) -> None:
        path, sha = relocation.relocate_file("SampLib/B.lean", "0" * 64)
        self.assertEqual(path, "SampLib/B.lean")
        self.assertEqual(sha, "0" * 64)

    def test_record_cannot_hide_an_edit(self) -> None:
        record_path = self.root / "relocations/R001.json"
        record = json.loads(record_path.read_text())
        record["files"]["SampLib/B.lean"]["after_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Not a mechanical rewrite"):
            relocation.check_record(record)

    def test_records_are_immutable(self) -> None:
        with self.assertRaises(SystemExit):
            relocation.apply({}, self.root / "relocations/R001.json", "HEAD", [])


if __name__ == "__main__":
    unittest.main()
