#!/usr/bin/env python3
"""Generate the deterministic P13 conformance/readiness manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
P8_PATH = "docs/status/P8-conformance-manifest.json"


def git_value(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def source_record(path: str) -> dict[str, str]:
    data = (ROOT / path).read_bytes()
    return {"path": path, "sha256": hashlib.sha256(data).hexdigest()}


def build_manifest() -> dict:
    sources = [
        "docs/plans/P13-Execution-Plan.md",
        "docs/status/Definition-Ledger.json",
        "docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json",
    ]
    entries = [
        {"id": "P13-T01", "delivery": "in_progress", "evidence": ["I", "K", "E"]},
        {"id": "P13-T02", "delivery": "in_progress", "evidence": ["I"]},
        {"id": "P13-T03", "delivery": "in_progress", "evidence": ["I", "E"]},
        {"id": "P13-T04", "delivery": "in_progress", "evidence": ["I", "K"]},
        {"id": "P13-T05", "delivery": "in_progress", "evidence": ["I", "K"]},
        {"id": "P13-T06", "delivery": "in_progress", "evidence": ["I"]},
        {"id": "P13-T07", "delivery": "in_progress", "evidence": ["I"]},
        {"id": "P13-T08", "delivery": "in_progress", "evidence": ["I"]},
        {"id": "P12", "delivery": "completed", "evidence": ["A", "I", "K", "E"]},
    ]
    return {
        "schema_version": "p13-v1",
        "plan_id": "DH-P13-GLOBAL-METATHEORY-EXEC-01",
        "repository": "DeepSeek-STC",
        "execution_base_commit": git_value("merge-base", "HEAD", "origin/main"),
        "branch": git_value("branch", "--show-current"),
        "sources": [source_record(path) for path in sources],
        "entries": entries,
        "finite_evidence": {
            "nonempty_state": True,
            "rule_constructor_surface": True,
            "guarded_rule_cases": True,
            "support_cycle": "abstract_snapshot_only",
            "alpha_nonidentity": True,
            "negative_profiles": ["abstract_support_cycle"],
        },
        "boundaries": {
            "architecture": "A",
            "production": "I",
            "kernel": "K",
            "executable": "E",
            "r0": "abstract seam only",
            "r1_plus": "not proved",
            "scoped_global_generalization": "not proved",
            "newer_paper_reconciliation": "not scheduled",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = Path(args.output)
    try:
        relative = output.resolve().relative_to(ROOT).as_posix()
    except ValueError as exc:
        raise SystemExit("output must be inside the repository") from exc
    if relative == P8_PATH or relative.endswith("P8-conformance-manifest.json"):
        raise SystemExit("refusing to write the historical P8 manifest")
    payload = json.dumps(build_manifest(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != payload:
            raise SystemExit("P13 manifest drift detected")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(payload, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
