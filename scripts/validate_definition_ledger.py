#!/usr/bin/env python3
"""Validator for docs/status/Definition-Ledger.json (P0-T03).

Derives the expected ID set from H03's numbered_nodes and auxiliary_nodes,
joins the corresponding H04 rows by ID, and rejects duplicates, omissions,
unknown IDs, copied-baseline drift, and any inferred readiness.  Reads the
frozen H03/H04 baselines; never edits them.

Usage:  python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json

Exit 0: all checks pass.  Exit 1: validation failures.
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
H03_PATH = ROOT / "docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json"
H04_PATH = ROOT / "docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json"

FROZEN_H03 = "8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8"
FROZEN_H04 = "63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db"

DELIVERY_VOCAB = ["planned", "in_progress", "completed", "blocked", "deferred"]
EVIDENCE_VOCAB = ["pending", "aligned", "passed", "proved", "tested", "seam_only", "deferred", "not_applicable"]
H04_COPIED = ["target_layer", "paper_relation", "blocking_decisions", "readiness"]


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    errors = []
    if len(sys.argv) != 2:
        print("usage: python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json")
        return 1
    ledger_path = Path(sys.argv[1])

    # --- frozen inputs ----------------------------------------------------
    try:
        h03 = json.loads(H03_PATH.read_text(encoding="utf-8"))
        h04 = json.loads(H04_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError as e:
        print(f"FATAL: missing frozen input: {e}")
        return 1
    h03_hash, h04_hash = sha256_of(H03_PATH), sha256_of(H04_PATH)
    if h03_hash != FROZEN_H03:
        errors.append(f"H03 file hash {h03_hash} != frozen {FROZEN_H03}")
    if h04_hash != FROZEN_H04:
        errors.append(f"H04 file hash {h04_hash} != frozen {FROZEN_H04}")

    # --- ledger -----------------------------------------------------------
    try:
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"FATAL: ledger not found: {ledger_path}")
        return 1
    except json.JSONDecodeError as e:
        print(f"FATAL: ledger is not valid JSON: {e}")
        return 1

    if ledger.get("schema_version") != "1.0":
        errors.append(f"schema_version {ledger.get('schema_version')!r} != '1.0'")
    if ledger.get("source_graph", {}).get("sha256") != h03_hash:
        errors.append("ledger.source_graph.sha256 does not match the H03 file hash")
    if ledger.get("source_disposition", {}).get("sha256") != h04_hash:
        errors.append("ledger.source_disposition.sha256 does not match the H04 file hash")

    numbered = h03["numbered_nodes"]
    auxiliary = h03["auxiliary_nodes"]
    h03_by_id = {n["id"]: n for n in numbered}
    h03_by_id.update({a["id"]: a for a in auxiliary})
    h04_by_id = {d["id"]: d for d in h04["numbered_dispositions"]}
    h04_by_id.update({d["id"]: d for d in h04["auxiliary_dispositions"]})
    expected_ids = [n["id"] for n in numbered] + [a["id"] for a in auxiliary]

    rows = ledger.get("items", [])
    ids = [r.get("id") for r in rows]

    # duplicates / omissions / unknown IDs
    dupes = sorted({i for i in ids if ids.count(i) > 1})
    if dupes:
        errors.append(f"duplicate rows: {dupes}")
    missing = sorted(set(expected_ids) - set(ids))
    if missing:
        errors.append(f"omitted IDs: {missing}")
    unknown = sorted(set(ids) - set(expected_ids))
    if unknown:
        errors.append(f"unknown IDs: {unknown}")
    if len(rows) != 82:
        errors.append(f"row count {len(rows)} != 82")

    # per-row checks
    inferred = []
    for r in rows:
        iid = r.get("id")
        if iid not in h03_by_id:
            continue  # already reported
        h3node, disp = h03_by_id[iid], h04_by_id[iid]
        kind = "auxiliary" if iid in {a["id"] for a in auxiliary} else h3node["kind"]
        if r.get("kind") != kind:
            errors.append(f"{iid}: kind {r.get('kind')!r} != expected {kind!r}")
        if r.get("paper_anchor") != h3node["section"]:
            errors.append(f"{iid}: paper_anchor {r.get('paper_anchor')!r} != H03 section {h3node['section']!r}")
        if r.get("title") != h3node["title"]:
            errors.append(f"{iid}: title drifted from H03")
        if kind != "auxiliary" and r.get("number") != h3node["number"]:
            errors.append(f"{iid}: number drifted from H03")
        if r.get("treatment") != disp["treatment"]:
            errors.append(f"{iid}: treatment {r.get('treatment')!r} != H04 {disp['treatment']!r}")
        for field in H04_COPIED:
            if r.get(f"h04_{field}") != disp[field]:
                errors.append(f"{iid}: h04_{field} drifted from H04")
        # dependencies = direct H03 edges into this node
        depends = sorted({e["source"] for e in h03["edges"] if e["target"] == iid})
        if r.get("depends_on") != depends:
            errors.append(f"{iid}: depends_on {r.get('depends_on')} != H03-derived {depends}")
        # vocabulary and readiness
        if r.get("delivery_status") not in DELIVERY_VOCAB:
            errors.append(f"{iid}: delivery_status {r.get('delivery_status')!r} outside blueprint vocabulary")
        if r.get("evidence_state") not in EVIDENCE_VOCAB:
            errors.append(f"{iid}: evidence_state {r.get('evidence_state')!r} outside blueprint vocabulary")
        if r.get("evidence_state") in ("proved", "tested", "passed") \
                and r.get("delivery_status") not in ("in_progress", "completed"):
            inferred.append(iid)
    if inferred:
        errors.append(f"inferred readiness (proved/tested/passed without in_progress/completed delivery): {sorted(inferred)}")

    # report
    if errors:
        print("VALIDATION FAILED:")
        for e in errors:
            print(f"  - {e}")
        return 1
    print("Definition-Ledger validation: PASS")
    print(f"  82/82 covered; duplicates 0; unknown 0")
    print(f"  H03 source hash OK: {h03_hash[:16]}...")
    print(f"  H04 source hash OK: {h04_hash[:16]}...")
    print("  no inferred transitive readiness")
    return 0


if __name__ == "__main__":
    sys.exit(main())
