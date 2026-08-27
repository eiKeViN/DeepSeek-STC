#!/usr/bin/env python3
"""Strict placeholder scan for STC production Lean files (P0-T04).

rg-compatible replacement for environments without ripgrep: same regex
`\\b(sorry|admit|axiom|unsafe)\\b`, same `path:line:text` output shape, and
the same exit-code contract:
  0 = at least one lexical match
  1 = no matches
  2 = scan error (missing directory, I/O failure, etc.)

Usage:  python scripts/scan_lean.py STC
"""
import re
import sys
from pathlib import Path

PATTERN = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: python scripts/scan_lean.py STC", file=sys.stderr)
        return 2
    root = Path(sys.argv[1])
    if not root.is_dir():
        print(f"scan error: directory does not exist: {root}", file=sys.stderr)
        return 2
    files = sorted(root.rglob("*.lean"))
    found = 0
    for path in files:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as e:
            print(f"scan error: cannot read {path}: {e}", file=sys.stderr)
            return 2
        for lineno, line in enumerate(text.splitlines(), 1):
            if PATTERN.search(line):
                found += 1
                print(f"{path}:{lineno}:{line}")
    return 0 if found else 1


if __name__ == "__main__":
    sys.exit(main())
