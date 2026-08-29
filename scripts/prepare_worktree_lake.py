#!/usr/bin/env python3
"""Share immutable Lake dependency checkouts with a Git worktree.

The root package build stays under the worktree's own ``.lake/build``.  Only
``.lake/packages`` is linked, and only from a worktree with the same manifest
and Lean toolchain.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def run_git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, check=True, text=True, capture_output=True
    )
    return result.stdout


def worktree_paths(root: Path) -> list[Path]:
    paths: list[Path] = []
    current: Path | None = None
    for line in run_git(root, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            current = Path(line.removeprefix("worktree ")).resolve()
            paths.append(current)
    return paths


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compatible(root: Path, candidate: Path) -> bool:
    manifest = root / "lake-manifest.json"
    toolchain = root / "lean-toolchain"
    return (
        (candidate / "lake-manifest.json").is_file()
        and (candidate / "lean-toolchain").is_file()
        and sha256(manifest) == sha256(candidate / "lake-manifest.json")
        and toolchain.read_bytes() == (candidate / "lean-toolchain").read_bytes()
    )


def link_directory(target: Path, source: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.is_symlink():
        if target.resolve() == source.resolve():
            print(f"already linked: {target} -> {source}")
            return
        raise SystemExit(f"refusing to replace existing link: {target}")
    if target.exists():
        raise SystemExit(
            f"refusing to replace existing directory: {target}; "
            "move it aside or run lake update for a local dependency checkout"
        )
    try:
        target.symlink_to(source, target_is_directory=True)
    except OSError as error:
        if os.name != "nt":
            raise SystemExit(f"could not link {target} to {source}: {error}") from error
        # Directory junctions do not require Windows Developer Mode/admin rights.
        result = subprocess.run(
            ["cmd", "/c", "mklink", "/J", str(target), str(source)],
            text=True,
            capture_output=True,
        )
        if result.returncode != 0:
            raise SystemExit(
                "could not create a dependency junction; enable Developer Mode "
                f"or create it manually ({result.stderr.strip()})"
            )
    print(f"linked: {target} -> {source}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        type=Path,
        help="worktree containing the dependency checkout (auto-detected by default)",
    )
    args = parser.parse_args()

    root = Path(run_git(Path.cwd(), "rev-parse", "--show-toplevel").strip()).resolve()
    manifest = root / "lake-manifest.json"
    if not manifest.is_file() or not (root / "lean-toolchain").is_file():
        raise SystemExit("not a DeepSeek-STC checkout: lake-manifest.json or lean-toolchain is missing")
    if json.loads(manifest.read_text()).get("packagesDir") != ".lake/packages":
        raise SystemExit("lake-manifest.json does not use the expected .lake/packages layout")

    local_packages = root / ".lake" / "packages"
    if local_packages.is_dir() and not local_packages.is_symlink():
        print(f"dependency checkout already exists locally: {local_packages}")
        return 0

    candidates = [args.source.resolve()] if args.source else worktree_paths(root)
    source_root = next(
        (
            candidate
            for candidate in candidates
            if candidate != root
            and compatible(root, candidate)
            and (candidate / ".lake" / "packages").is_dir()
        ),
        None,
    )
    if source_root is None:
        raise SystemExit(
            "no compatible worktree has .lake/packages; run `lake update` once "
            "in a populated checkout, then rerun this command"
        )
    link_directory(local_packages, (source_root / ".lake" / "packages").resolve())
    print("root build outputs remain local to this worktree under .lake/build")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as error:
        message = error.stderr.strip() if error.stderr else str(error)
        raise SystemExit(f"git command failed: {message}") from error
