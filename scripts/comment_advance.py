#!/usr/bin/env python3
"""Anchor-comment silent-repair tool for Lean files.

Invariant: exactly one open comment region (started by the frontier '/-')
closed by the single '-/' anchor near the bottom of the file. A declaration is
live iff it lies outside that region.

Protocol (strict — follow every step):
  1. python scripts/comment_advance.py FILE            # report (#n, #n+1, #n+2)
  2. fix declaration #n+1 (edits only inside its body; never touch the markers)
  3. lake env lean FILE                                # ONLY allowed errors: in #n+1
  4. python scripts/comment_advance.py FILE advance    # silence #n+2, activate #n+1
  (repeat)

Commands:
  report (default)  print the frontier and the silent-block shape
  check             exit 0 iff the invariant holds, else print the violation
  advance           verify, then: silence #n+2 (inline '/- ' prefix) and
                    activate #n+1 (strip its '/- ' prefix); re-verify

Opt-in: this tool is used only when the current user asks for the
silent-repair workflow in natural language; otherwise the file is edited
normally.
"""

import re
import sys

DECL = re.compile(r"^(theorem|lemma|abbrev|def|inductive|structure|example)\s+(\w+)")
COMMENTED_DECL = re.compile(r"^/-\s+(theorem|lemma|abbrev|def|inductive|structure|example)\s+(\w+)")


def read_lines(path):
    with open(path, encoding="utf-8", newline="") as f:
        text = f.read()
    newline = "\r\n" if "\r\n" in text else "\n"
    return text.splitlines(keepends=True), newline


def scan(path):
    lines, _nl = read_lines(path)
    decls = []  # (line_index, name)
    live = []  # (line_index, name)   depth-0 declarations
    silent = []  # (line_index, name) declarations inside the frontier block
    depth = 0
    frontier_open_line = None  # LAST zero->positive transition
    anchor_line = None  # last line that brings depth back to 0
    for i, ln in enumerate(lines):
        opens = ln.count("/-")
        closes = ln.count("-/")
        m = DECL.match(ln) or COMMENTED_DECL.match(ln)
        if m:
            decls.append((i, m.group(2)))
            if depth == 0:
                live.append((i, m.group(2)))
            else:
                silent.append((i, m.group(2)))
        if opens or closes:
            was_zero = depth == 0
            depth += opens - closes
            if depth < 0:
                raise SystemExit(f"FAIL: unbalanced '-/' at line {i + 1}")
            if was_zero and depth > 0:
                frontier_open_line = i
            if depth == 0 and opens == 0:
                anchor_line = i
    if depth != 0:
        raise SystemExit(f"FAIL: net comment depth {depth} (unterminated block)")
    if frontier_open_line is None:
        raise SystemExit("FAIL: no open comment block found (no silent region?)")
    if anchor_line is None or anchor_line <= frontier_open_line:
        raise SystemExit("FAIL: frontier block never closes")
    # after the frontier opener, depth must stay positive until the anchor
    depth2 = 0
    for i, ln in enumerate(lines):
        opens = ln.count("/-")
        closes = ln.count("-/")
        depth2 += opens - closes
        if frontier_open_line < i < anchor_line and depth2 == 0:
            raise SystemExit(
                "FAIL: depth returned to 0 at line "
                f"{i + 1} before the anchor (line {anchor_line + 1}) — "
                "more than one comment region"
            )
    return lines, decls, live, silent, frontier_open_line, anchor_line


def report(path):
    lines, decls, live, silent, frontier_open_line, anchor_line = scan(path)
    print(f"file: {path}")
    print(f"frontier opener: line {frontier_open_line + 1}; anchor '-/': line {anchor_line + 1}")
    print(f"declarations: {len(decls)} total, {len(live)} live, {len(silent)} silent")
    if live:
        i, n = live[-1]
        print(f"  #n   (last live):      {n}  (line {i + 1})")
    if silent:
        i, n = silent[0]
        print(f"  #n+1 (next to fix):    {n}  (line {i + 1})")
    if len(silent) > 1:
        i, n = silent[1]
        print(f"  #n+2 (to stay silent): {n}  (line {i + 1})")
    print(f"  silent region: {len(silent)} declarations (lines {silent[0][0] + 1}..{silent[-1][0] + 1})")


def advance(path):
    lines, decls, live, silent, frontier_open_line, anchor_line = scan(path)
    if not silent:
        raise SystemExit("FAIL: nothing silent — nothing to advance")
    n1_idx, n1_name = silent[0]
    n2_idx, n2_name = (silent[1] if len(silent) > 1 else (None, None))
    # activate #n+1: strip the inline '/- ' prefix from its declaration line
    ln1 = lines[n1_idx]
    if not COMMENTED_DECL.match(ln1):
        raise SystemExit(
            f"FAIL: {n1_name} (line {n1_idx + 1}) is silent but has no inline '/- ' "
            "prefix to strip — is the opener a standalone line? (not handled)"
        )
    lines[n1_idx] = COMMENTED_DECL.sub(r"\1 \2", ln1, count=1)
    # silence #n+2 (if any): prefix its declaration line
    if n2_idx is not None:
        ln2 = lines[n2_idx]
        if not DECL.match(ln2):
            raise SystemExit(
                f"FAIL: {n2_name} (line {n2_idx + 1}) is not a plain declaration line — "
                "cannot prefix it"
            )
        lines[n2_idx] = "/- " + ln2
    _old, nl = read_lines(path)
    with open(path, "w", encoding="utf-8", newline="") as f:
        for ln in lines:
            f.write(ln.rstrip("\r\n") + nl)
    # re-verify
    lines, decls, live2, silent2, _, _ = scan(path)
    if live2 and live2[-1][1] == n1_name:
        print(f"advanced: {n1_name} now live"
              + (f"; {n2_name} now silent" if n2_name else "; nothing left to silence"))
        if silent2:
            i, n = silent2[0]
            print(f"  next (#n+1): {n} (line {i + 1})")
    else:
        raise SystemExit("FAIL: post-advance verification failed")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: comment_advance.py FILE [report|check|advance]")
    path = sys.argv[1]
    cmd = sys.argv[2] if len(sys.argv) > 2 else "report"
    if cmd == "report":
        report(path)
    elif cmd == "check":
        scan(path)
        print("invariant holds")
    elif cmd == "advance":
        advance(path)
    else:
        raise SystemExit(f"unknown command {cmd}")


if __name__ == "__main__":
    main()
