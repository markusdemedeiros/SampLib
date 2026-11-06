#!/usr/bin/env python3
"""Move Lean modules without voiding reviews, and check recorded moves.

A relocation record in `agent-docs/relocations/` lists every file whose path or bytes
a move changed. Each change is mechanical: Lean import lines and Markdown link targets
are rewritten through the module and path maps, and nothing else differs. `--check`
replays that rewrite from the recorded base commit and compares every hash, so a
record cannot hide an edit. Audits translate recorded snapshots, contexts and module
names through the records instead of rewriting immutable reviews.
"""

from __future__ import annotations

import argparse
from functools import cache
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RECORDS = ROOT / "agent-docs/relocations"
IMPORT = re.compile(r"^((?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)(\S+)", re.M)
LINK = re.compile(r"(\]\()([^)\s#]+)")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rewrite_lean(text: str, modules: dict[str, str]) -> str:
    return IMPORT.sub(lambda m: m[1] + modules.get(m[2], m[2]), text)


def rewrite_markdown(text: str, doc: str, paths: dict[str, str]) -> str:
    """Retarget relative links of a document that itself stays in place."""
    base = PurePosixPath(doc).parent

    def target(match: re.Match) -> str:
        link = match[2]
        if "://" in link or link.startswith("/"):
            return match[0]
        resolved = os.path.normpath(base / link)
        if resolved not in paths:
            return match[0]
        return match[1] + os.path.relpath(paths[resolved], base)

    return LINK.sub(target, text)


def rewrite(path: str, data: bytes, modules: dict[str, str], paths: dict[str, str]) -> bytes:
    if path.endswith(".lean"):
        return rewrite_lean(data.decode(), modules).encode()
    if path.endswith(".md"):
        return rewrite_markdown(data.decode(), path, paths).encode()
    return data


@cache
def records() -> tuple[dict, ...]:
    return tuple(json.loads(p.read_text()) for p in sorted(RECORDS.glob("*.json")))


def current_module(module: str) -> str:
    for record in records():
        module = record["modules"].get(module, module)
    return module


def current_path(path: str) -> str:
    for record in records():
        entry = record["files"].get(path)
        if entry is not None:
            path = entry["path"]
    return path


def current_imports(text: str) -> str:
    """Point a generated Lean header's imports at the current module names."""
    return IMPORT.sub(lambda m: m[1] + current_module(m[2]), text)


def relocate_file(path: str, sha: str) -> tuple[str, str]:
    """Translate a recorded (path, hash) pair; a stale hash keeps its mismatch."""
    for record in records():
        entry = record["files"].get(path)
        if entry is not None:
            if sha == entry["before_sha256"]:
                sha = entry["after_sha256"]
            path = entry["path"]
    return path, sha


def relocate_snapshot(snapshot: dict[str, str]) -> dict[str, str]:
    if not isinstance(snapshot, dict):
        return snapshot
    return dict(sorted(relocate_file(path, sha) for path, sha in snapshot.items()))


def relocate_context(context: dict) -> dict:
    if not isinstance(context, dict) or "files" not in context:
        return context
    return {**context, "files": relocate_snapshot(context["files"])}


def module_path(module: str) -> str:
    return current_module(module).replace(".", "/") + ".lean"


def git_blob(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), "show", f"{commit}:{path}"])


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check_record(record: dict) -> None:
    require(record.get("schema_version") == 1 and record.get("kind") == "module_relocation",
            "Unknown relocation schema")
    base = record["base_commit"]
    targets = [entry["path"] for entry in record["files"].values()]
    require(len(set(targets)) == len(targets), "Two files relocate to one path")
    for old, new in record["modules"].items():
        entry = record["files"].get(old.replace(".", "/") + ".lean")
        require(entry is not None and entry["path"] == new.replace(".", "/") + ".lean",
                f"Module move lacks its file move: {old}")
    paths = {old: e["path"] for old, e in record["files"].items() if e["path"] != old}
    for old, entry in record["files"].items():
        before = git_blob(base, old)
        require(digest(before) == entry["before_sha256"], f"Base content differs: {old}")
        after = rewrite(old, before, record["modules"], paths)
        require(digest(after) == entry["after_sha256"], f"Not a mechanical rewrite: {old}")
        require(after != before or old != entry["path"], f"Unchanged file listed: {old}")


def check(record_paths: list[Path] | None = None) -> int:
    """Replay each record from its base commit; audits compare the results to the tree."""
    paths = record_paths or sorted(RECORDS.glob("*.json"))
    for path in paths:
        check_record(json.loads(path.read_text()))
    return len(paths)


def tracked_texts() -> list[str]:
    out = subprocess.check_output(["git", "-C", str(ROOT), "ls-files", "*.lean", "*.md"],
                                  text=True)
    return [p for p in out.splitlines() if (ROOT / p).is_file()]


def apply(moves: dict[str, str], output: Path, base: str, docs: list[str]) -> None:
    """Move files (old path -> new path) and rewrite every tracked Lean file and `docs`."""
    if output.exists():
        raise SystemExit("Relocation records are immutable; choose a new output path")
    head = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", base], text=True).strip()
    status = ["git", "-C", str(ROOT), "status", "--porcelain", "--untracked-files=no", "--",
              "*.lean"]
    if subprocess.check_output(status, text=True).strip():
        raise SystemExit("Lean sources differ from the base commit; start from a clean tree")
    modules = {}
    for old, new in moves.items():
        if old.startswith("SampLib/") and new.startswith("SampLib/"):
            modules[old.removesuffix(".lean").replace("/", ".")] = \
                new.removesuffix(".lean").replace("/", ".")
    record = {"schema_version": 1, "kind": "module_relocation", "base_commit": head,
              "meaning": ("Paths and import lines changed mechanically; proof text did not. "
                          "Check with `python3 agent-scripts/relocation.py --check`."),
              "modules": dict(sorted(modules.items())), "files": {}}
    sources = [p for p in tracked_texts() if p.endswith(".lean")] + docs
    outputs = {}
    for old in sorted(set(sources) | set(moves)):
        before = git_blob(head, old)
        after = rewrite(old, before, modules, moves)
        new = moves.get(old, old)
        if new == old and after == before:
            continue
        outputs[old] = after
        record["files"][old] = {"path": new, "before_sha256": digest(before),
                                "after_sha256": digest(after)}
    for old, entry in record["files"].items():
        if entry["path"] != old:
            (ROOT / old).unlink()
    for old, entry in record["files"].items():
        target = ROOT / entry["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(outputs[old])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n")
    check([output])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--apply", type=Path, help="JSON map of old path -> new path")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--base", default="HEAD")
    parser.add_argument("--doc", action="append", default=[],
                        help="also retarget links in this tracked Markdown file")
    args = parser.parse_args()
    if args.apply:
        apply(json.loads(args.apply.read_text()), args.output, args.base, args.doc)
    print(f"Checked {check()} relocation record(s).")


if __name__ == "__main__":
    main()
