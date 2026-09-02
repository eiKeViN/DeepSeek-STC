#!/usr/bin/env python3
"""Anchor-comment silent-repair tool for Lean files.

Invariant: exactly one open comment region — the frontier '/- ' prefix sits on
the declaration line of the last checkpointed (fixed) declaration, closed by
the single '-/' anchor near the bottom.  A declaration is compiled iff it is
textually before the opener; the scan's "live" list additionally contains the
opener line itself (it is recorded before the line's own '/-' is counted).

Two marker states:
  checkpoint state: opener on the last-fixed decl; report's #n+1 = next to fix.
  working state:    opener on #n+2; the compiler sees through #n+1.

Protocol (strict — follow every step):
  1. python scripts/comment_advance.py FILE report       # #n+1 = next to fix
  2. python scripts/comment_advance.py FILE advance      # compile through #n+1
  3. fix declaration #n+1 (edits only inside its body; never touch the markers)
  4. lake env lean FILE                                  # ONLY allowed errors: in #n+1
  5. python scripts/comment_advance.py FILE checkpoint   # record #n+1 as fixed
  (repeat from 1; stop only in checkpoint state)

Commands:
  report (default)  print the frontier and the silent-block shape
  check             exit 0 iff the invariant holds, else print the violation
  advance           checkpoint -> working: strip the opener's prefix, prefix
                    #n+2's line (or, if #n+2 does not exist, remove the anchor
                    too — the file becomes fully live)
  checkpoint        working -> checkpoint: strip the opener's prefix, prefix
                    the just-fixed declaration's line

Opt-in: this tool is used only when the current user asks for the
silent-repair workflow in natural language, or when the file being modified
exceeds 500 lines (AGENTS.md); otherwise the file is edited normally.
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


def write_lines(path, lines):
    _old, nl = read_lines(path)
    with open(path, "w", encoding="utf-8", newline="") as f:
        for ln in lines:
            f.write(ln.rstrip("\r\n") + nl)


def scan(path):
    lines, _nl = read_lines(path)
    decls = []  # (line_index, name)
    live = []  # (line_index, name)   depth-0 declarations
    silent = []  # (line_index, name) declarations inside the frontier block
    depth = 0
    frontier_open_line = None  # LAST zero->positive transition
    anchor_line = None  # last line that brings depth back to 0
    total_opens = 0
    total_closes = 0
    for i, ln in enumerate(lines):
        opens = ln.count("/-")
        closes = ln.count("-/")
        total_opens += opens
        total_closes += closes
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
    if total_opens == 0 and total_closes == 0:
        return lines, decls, list(live), [], None, None  # fully live file
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


def decl_index(decls, name):
    for j, (_i, n) in enumerate(decls):
        if n == name:
            return j
    return None


def report(path):
    lines, decls, live, silent, frontier_open_line, anchor_line = scan(path)
    print(f"file: {path}")
    if frontier_open_line is None:
        print("fully live: no silent region")
        return
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
    if silent:
        print(f"  silent region: {len(silent)} declarations (lines {silent[0][0] + 1}..{silent[-1][0] + 1})")
    else:
        print("  no silent declarations (file fully live)")


def advance(path):
    """checkpoint -> working: strip the opener's prefix, prefix #n+2's line."""
    lines, decls, live, silent, frontier_open_line, anchor_line = scan(path)
    if frontier_open_line is None:
        raise SystemExit("FAIL: no silent region — nothing to advance")
    if not silent:
        raise SystemExit("FAIL: nothing silent — nothing to advance")
    op_idx, op_name = live[-1]
    ln_op = lines[op_idx]
    if not COMMENTED_DECL.match(ln_op):
        raise SystemExit(
            f"FAIL: opener line {op_idx + 1} is not a '/- '-prefixed declaration"
        )
    n1_idx, n1_name = silent[0]
    if decl_index(decls, op_name) + 1 != decl_index(decls, n1_name):
        raise SystemExit("FAIL: opener and #n+1 are not consecutive declarations")
    lines[op_idx] = COMMENTED_DECL.sub(r"\1 \2", ln_op, count=1)
    if len(silent) > 1:
        n2_idx, n2_name = silent[1]
        ln2 = lines[n2_idx]
        if not DECL.match(ln2):
            raise SystemExit(
                f"FAIL: {n2_name} (line {n2_idx + 1}) is not a plain declaration line — "
                "cannot prefix it"
            )
        lines[n2_idx] = "/- " + ln2
    else:
        # last declaration: remove the anchor too, the file becomes fully live
        ln_a = lines[anchor_line]
        lines[anchor_line] = ln_a.replace("-/", "", 1)
    write_lines(path, lines)
    lines, decls, live2, silent2, f2, a2 = scan(path)
    if f2 is None:
        print(f"advanced: {n1_name} now compiled; no silent region left")
        return
    if live2 and live2[-1][1] == silent[1][1] and (
            len(silent) == 2 or (silent2 and silent2[0][1] == silent[2][1])):
        print(f"advanced: {n1_name} now compiled (fix it next); opener on {silent[1][1]}")
        return
    raise SystemExit("FAIL: post-advance verification failed")


def checkpoint(path):
    """working -> checkpoint: strip the opener's prefix, prefix the just-fixed decl."""
    lines, decls, live, silent, frontier_open_line, anchor_line = scan(path)
    if frontier_open_line is None:
        raise SystemExit("FAIL: no silent region — nothing to checkpoint")
    if len(live) < 2 or not silent:
        raise SystemExit("FAIL: working state expected (opener on #n+2)")
    op_idx, op_name = live[-1]
    fix_idx, fix_name = live[-2]
    if not COMMENTED_DECL.match(lines[op_idx]):
        raise SystemExit(
            f"FAIL: opener line {op_idx + 1} is not a '/- '-prefixed declaration"
        )
    if not DECL.match(lines[fix_idx]):
        raise SystemExit(
            f"FAIL: {fix_name} (line {fix_idx + 1}) is not a plain declaration line — "
            "cannot prefix it"
        )
    if decl_index(decls, fix_name) + 1 != decl_index(decls, op_name):
        raise SystemExit("FAIL: just-fixed decl and opener are not consecutive")
    if decl_index(decls, op_name) + 1 != decl_index(decls, silent[0][1]):
        raise SystemExit("FAIL: opener and #n+1 are not consecutive declarations")
    lines[op_idx] = COMMENTED_DECL.sub(r"\1 \2", lines[op_idx], count=1)
    lines[fix_idx] = "/- " + lines[fix_idx]
    write_lines(path, lines)
    lines, decls, live2, silent2, _, _ = scan(path)
    if live2 and silent2 and live2[-1][1] == fix_name and silent2[0][1] == op_name:
        print(f"checkpointed: {fix_name} fixed; next (#n+1): {op_name}")
        return
    raise SystemExit("FAIL: post-checkpoint verification failed")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: comment_advance.py FILE [report|check|advance|checkpoint]")
    path = sys.argv[1]
    cmd = sys.argv[2] if len(sys.argv) > 2 else "report"
    if cmd == "report":
        report(path)
    elif cmd == "check":
        scan(path)
        print("invariant holds")
    elif cmd == "advance":
        advance(path)
    elif cmd == "checkpoint":
        checkpoint(path)
    else:
        raise SystemExit(f"unknown command {cmd}")


if __name__ == "__main__":
    main()
