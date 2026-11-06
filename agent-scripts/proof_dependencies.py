"""Source snapshots shared by reviewers and the final sampler-proof audit."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
HEADER_TOOL = ROOT / "agent-scripts/parse_lean_imports.lean"
_HEADERS: dict[Path, tuple[str, list[str]]] = {}


def parse_headers(paths: list[Path]) -> None:
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(HEADER_TOOL), *map(str, paths)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode or "warning:" in result.stdout:
        raise ValueError(f"Lean header parsing failed: {result.stdout}")
    for line in result.stdout.splitlines():
        item = json.loads(line)
        path = Path(item["path"])
        _HEADERS[path] = (sha256(path), item["imports"])


def imports_of(path: Path) -> list[str]:
    if not _HEADERS:
        paths = [ROOT / "SampLib.lean"]
        for directory in (ROOT / "SampLib", ROOT / "code", ROOT / "tests"):
            paths.extend(directory.rglob("*.lean"))
        parse_headers(paths)
    if path not in _HEADERS or _HEADERS[path][0] != sha256(path):
        parse_headers([path])
    return _HEADERS[path][1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def project_module(module: str) -> Path | None:
    relative = Path(module.replace(".", "/") + ".lean")
    for base in (ROOT, ROOT / "code", ROOT / "tests"):
        path = base / relative
        if path.is_file():
            return path
    return None


def source_snapshot(module: str, implementation: str) -> dict[str, str]:
    """Hash the implementation and the entire project-local import closure."""
    entry = project_module(module)
    if entry is None:
        raise ValueError(f"No source for {module}")
    pending = [entry, ROOT / implementation]
    found: dict[str, str] = {}
    while pending:
        path = pending.pop()
        relative = str(path.relative_to(ROOT))
        if relative in found:
            continue
        found[relative] = sha256(path)
        for imported in imports_of(path):
            dependency = project_module(imported)
            if dependency is not None:
                pending.append(dependency)
    return dict(sorted(found.items()))


def review_context() -> dict:
    """Pin configuration, proof policy, and clean dependency checkouts."""
    files = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "AGENTS.md",
             "agent-docs/VerifyingSamplers.md"]
    context = {"files": {name: sha256(ROOT / name) for name in files}, "packages": {}}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError(f"Unpinned dependency type: {package['name']}")
        name = package["name"].removeprefix("«").removesuffix("»")
        path = ROOT / ".lake/packages" / name
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if head != package["rev"]:
            raise ValueError(f"Dependency HEAD differs from manifest: {name}")
        dirty = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        untracked = subprocess.check_output(
            ["git", "-C", str(path), "ls-files", "--others", "--exclude-standard", "*.lean"], text=True)
        if dirty or untracked:
            raise ValueError(f"Dependency has unreviewed source changes: {name}")
        context["packages"][name] = head
    return context
