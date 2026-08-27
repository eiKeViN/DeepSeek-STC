#!/usr/bin/env python3
"""One-off generator for docs/status/Definition-Ledger.json (P0-T03).

Derives the mechanical content from the frozen H03/H04 baselines and layers on
hand-curated P0 status fields.  Do not edit H03/H04; edit the curation tables
below instead and regenerate.

Usage:  python scripts/gen_definition_ledger.py
"""
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
H03_PATH = ROOT / "docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json"
H04_PATH = ROOT / "docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json"
OUT_PATH = ROOT / "docs/status/Definition-Ledger.json"

FROZEN_H03 = "8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8"
FROZEN_H04 = "63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db"

DELIVERY_VOCAB = ["planned", "in_progress", "completed", "blocked", "deferred"]
EVIDENCE_VOCAB = ["pending", "aligned", "passed", "proved", "tested", "seam_only", "deferred", "not_applicable"]


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# Hand-curated status tables (the only non-mechanical input).
# Defaults: delivery "planned", evidence "pending", module from ITEM_MODULE,
# deferred_reason "", notes "".
# ---------------------------------------------------------------------------

ITEM_MODULE = {
    # EFFECT-CORE (Section 3.1)
    "D1": "STC/Core/Effect.lean", "D2": "STC/Core/Effect.lean", "D3": "STC/Core/Effect.lean",
    "T4": "STC/Core/Effect.lean", "T5": "STC/Core/Effect.lean", "D6": "STC/Core/Effect.lean",
    "T7": "STC/Core/Effect.lean", "D8": "STC/Core/Effect.lean", "D9": "STC/Core/Effect.lean",
    "T10": "STC/Core/Effect.lean", "T11": "STC/Core/Effect.lean", "D12": "STC/Core/Effect.lean",
    "T13": "STC/Core/Effect.lean", "T14": "STC/Core/Effect.lean", "T15": "STC/Core/Effect.lean",
    "T16": "STC/Core/Effect.lean", "D17": "STC/Core/Effect.lean", "L18": "STC/Core/Effect.lean",
    "D19": "STC/Core/Partial.lean", "T20": "STC/Core/Partial.lean", "C21": "STC/Core/Partial.lean",
    # COEFFECT (Section 3.2)
    "D22": "STC/Prelude/Finite.lean",
    "D23": "STC/Core/Partial.lean", "D24": "STC/Core/Partial.lean",
    "D25": "STC/Core/Partial.lean", "D26": "STC/Core/Partial.lean",
    "D27": "STC/State/Observation.lean", "D28": "STC/State/Observation.lean",
    "D29": "STC/State/Observation.lean", "D30": "STC/State/Observation.lean",
    "D31": "STC/State/Observation.lean",
    # OBSERVATIONAL (Section 3.3)
    "D32": "STC/State/Like.lean", "D33": "STC/State/Like.lean",
    "D34": "STC/Core/Partial.lean", "L35": "STC/Core/Partial.lean",
    "D36": "STC/Foundation/Relation.lean", "D37": "STC/Foundation/Relation.lean",
    "L38": "STC/Foundation/Relation.lean", "D39": "STC/Core/Partial.lean",
    "T40": "STC/Core/Partial.lean", "D41": "STC/Core/Partial.lean",
    "T42": "STC/Core/Partial.lean",
    # CALCULUS-SHELL (Section 4.1-4.2)
    "D43": "STC/State/FinmapAdapter.lean",
    "D44": "STC/State/RegistryLike.lean", "D45": "STC/State/RegistryLike.lean",
    "D46": "STC/State/RegistryLike.lean", "D47": "STC/State/RegistryLike.lean",
    "D48": "",
    # CALCULUS-EXTENDED (Section 4.3)
    "D49": "", "D50": "",
    "D51": "STC/Core/Iterator.lean", "D52": "STC/Core/Iterator.lean",
    # METATHEORY (Section 4.4)
    "D53": "STC/Alpha/Transport.lean", "L54": "", "L55": "", "L56": "STC/Alpha/Transport.lean",
    "L57": "", "D58": "STC/State/FinmapAdapter.lean", "T59": "", "D60": "STC/Core/Iterator.lean",
    "T61": "", "C62": "", "T63": "", "T64": "", "D65": "", "T66": "STC/Core/Iterator.lean",
    "D67": "", "L68": "", "D69": "", "L70": "", "L71": "", "L72": "",
    "T73": "STC/Alpha/Transport.lean",
    # IMPLEMENTATION-REFINEMENT (Section 5)
    "D74": "STC/Adapter.lean",
    # Auxiliary
    "SAT": "STC/Core/Partial.lean",
    "R.base": "", "R.withdraw": "", "R.iter": "STC/Core/Iterator.lean", "A.async": "",
    "R.fail": "STC/Foundation/Result.lean", "R.full": "", "Table1": "",
}

DEFERRED_ITEMS = {
    "D27": ("deferred", "not_applicable",
            "EXPOSITORY per H04: realization/refinement concern; no core theorem declaration"),
    "D28": ("deferred", "deferred",
            "BD-SCOPED deferred: typed realms/interception outside the first slice"),
    "D29": ("deferred", "deferred",
            "BD-SCOPED deferred: typed realms/interception outside the first slice"),
    "D30": ("deferred", "deferred",
            "BD-SCOPED deferred: typed realms/interception outside the first slice"),
    "D31": ("deferred", "deferred",
            "BD-SCOPED deferred: typed realms/interception outside the first slice"),
    "D49": ("deferred", "deferred",
            "BD-STAGING and BD-CONTROL deferred; extended lifecycle forward-refers to iterator/failure machinery"),
    "L54": ("deferred", "deferred",
            "BD-CONTROL deferred: labelled lifecycle semantics not in the first slice"),
    "L55": ("deferred", "deferred", "BD-CONTROL deferred"),
    "L57": ("deferred", "deferred", "BD-CONTROL deferred"),
    "T59": ("deferred", "deferred", "BD-CONTROL deferred: trace-level preservation not in the first slice"),
    "T61": ("deferred", "deferred", "BD-CONTROL deferred"),
    "C62": ("deferred", "deferred", "BD-CONTROL deferred"),
    "T63": ("deferred", "deferred", "BD-CONTROL deferred"),
    "T64": ("deferred", "deferred", "BD-CONTROL deferred"),
    "D67": ("deferred", "deferred",
            "BD-SUPPORT deferred: support recursion/well-foundedness needs a separate treatment"),
    "L68": ("deferred", "deferred",
            "BD-SUPPORT deferred; F-L68-CYCLE counterexample to mechanize first"),
    "L70": ("deferred", "deferred", "BD-SUPPORT and BD-CONTROL deferred"),
    "L71": ("deferred", "deferred", "BD-CONTROL deferred"),
    "L72": ("deferred", "deferred", "BD-SUPPORT and BD-CONTROL deferred"),
    "D74": ("deferred", "deferred",
            "H04 DEFER: implementation-refinement phase; only the P8 R0 seam is planned"),
    "R.base": ("deferred", "deferred",
               "SUBSUMED derived base view; BD-STAGING and BD-CONTROL deferred"),
    "R.withdraw": ("deferred", "deferred",
                   "SUBSUMED rule subfamily of R.full; BD-CONTROL deferred"),
    "A.async": ("deferred", "deferred",
                "BD-CONTROL deferred; needs an in-flight semantic carrier (H04 replacement repair)"),
    "R.full": ("deferred", "deferred",
               "Authoritative labelled semantics; BD-CONTROL/BD-STAGING deferred"),
    "Table1": ("deferred", "deferred",
               "SUBSUMED as derived per-constructor facts; BD-CONTROL deferred"),
}

DEFERRED_SUBPART = {
    "D53": "lifecycle/control trace decomposition deferred (BD-CONTROL); name-neutral transport planned P6",
    "L56": "name-bearing control-payload variant deferred (P6-T03, BD-CONTROL)",
    "D60": "lifecycle-level independence deferred (BD-CONTROL); iteration reach/length planned P4",
    "T66": "global lifecycle-termination suffix deferred (BD-CONTROL); rank termination planned P4",
    "T73": "support-order/confluence component deferred (BD-SUPPORT, BD-CONTROL); name-neutral equivariance planned P6",
    "R.iter": "L-Begin/L-Iter/L-Finish rule constructors deferred (BD-CONTROL); execution slice planned P4",
    "R.fail": "L-Raise rule constructor deferred (BD-CONTROL); failure outcome/prefix undo planned P3-P4",
}

NOTES = {
    "T4": "provisional module: tracking-family items not individually task-mapped; part of the P2 effect kernel",
    "T5": "provisional module: tracking-family items not individually task-mapped; part of the P2 effect kernel",
    "D6": "provisional module: tracking-family items not individually task-mapped; part of the P2 effect kernel",
    "T7": "provisional module: tracking-family items not individually task-mapped; part of the P2 effect kernel",
    "D8": "F-D8-WITNESS repair: let-bound/output-indexed witness, not the displayed vacuous pair",
    "D17": "provisional module: no dedicated task row; part of the P2 effect kernel",
    "L18": "provisional module: no dedicated task row; part of the P2 effect kernel",
    "D22": "blueprint DAG logical layer STC/Prelude/Finite; ADR-02 authoritative dependent Finmap store",
    "D27": "in-place vs derived realization note lives with the P5-T04 store/registry boundary doc",
    "D28": "P5-T04 keeps only the store/registry boundary note while BD-SCOPED is deferred",
    "D29": "P5-T04 keeps only the store/registry boundary note while BD-SCOPED is deferred",
    "D30": "P5-T04 keeps only the store/registry boundary note while BD-SCOPED is deferred",
    "D31": "P5-T04 keeps only the store/registry boundary note while BD-SCOPED is deferred",
    "D32": "abstract StateLike first; ADR-03 RawState/ValidState adapter seam in P5-T03",
    "D33": "primary state-level relation in State/Like; result relators in Foundation/Result (P1-T02)",
    "L35": "F-L35-INVERSE repair: corrected universal property plus countermodel for the rejected combination",
    "D37": "F-L35-INVERSE: must identify the inverse actually returned by the run",
    "L38": "SUBSUMED per H04: instantiated by the relation-parametric core, not duplicated",
    "D43": "provisional: no dedicated task; ADR-03 closure/FinmapAdapter territory",
    "D44": "fiber shell: action codes, not State→State closures inside State (ADR-03)",
    "D48": "no dedicated task; confinement predicate unassigned (BD-STATE/BD-EQUIV/BD-ITER resolved)",
    "D50": "no dedicated task; provisional (BD-STATE resolved via ADR-03)",
    "D58": "provisional: WellFormed territory of the ADR-03 FinmapAdapter seam (P5-T03)",
    "D65": "no dedicated task; BD-NAMES resolved via ADR-04",
    "D69": "no dedicated task; BD-ITER/BD-COEFFECT resolved",
    "T66": "F-T66-ORIGIN repair: lifecycle-only suffix from reachable states, not full traces",
    "SAT": "provisional: expected with the D25/D26 specification family; F-D26-DECIDE repair",
    "L56": "F-NAME-REUSE: equivariance over incarnations or trace-global freshness",
    "L68": "F-L68-CYCLE counterexample (late registration after provider removal) to mechanize first",
    "D74": "P8-T02 R0 adapter seam only; R1+ refinement deferred",
}

# Blueprint task -> (paper_refs, adr_refs).  P8-T01 (catch-all) and P7-T06
# (report task) are excluded from ADR derivation to avoid over-broad refs.
TASKS = [
    ("P1-T01", ["D36", "D37", "L38"], ["ADR-01", "ADR-06-CLOSURE"]),
    ("P1-T02", ["D33", "D36-D39"], ["ADR-02", "ADR-06-CLOSURE"]),
    ("P1-T03", ["D36-D42", "L38"], ["ADR-01", "ADR-06-CLOSURE"]),
    ("P2-T01", ["D1-D3", "D8-D10"], ["ADR-01", "ADR-05"]),
    ("P2-T02", ["D8", "T11", "T15", "T16"], ["ADR-01", "ADR-06-CLOSURE"]),
    ("P2-T03", ["T10-T16"], ["ADR-01", "ADR-06-CLOSURE"]),
    ("P2-T04", ["D8-D12"], ["ADR-03", "ADR-05"]),
    ("P3-T01", ["D23-D26", "D34", "D39"], ["ADR-02", "ADR-06-CLOSURE"]),
    ("P3-T02", ["D19", "T20", "C21", "D36-D42"], ["ADR-01", "ADR-06-CLOSURE"]),
    ("P3-T03", ["R.fail"], ["ADR-05", "ADR-06-CLOSURE"]),
    ("P3-T04", ["R.fail"], ["ADR-05"]),
    ("P4-T01", ["D51", "D52", "D60"], ["ADR-05", "ADR-06-CLOSURE"]),
    ("P4-T02", ["D52", "T66", "R.iter", "R.fail"], ["ADR-05"]),
    ("P4-T03", ["D51", "D52"], ["ADR-01", "ADR-05", "ADR-06-CLOSURE"]),
    ("P4-T04", ["D51", "D52", "R.iter", "R.fail"], ["ADR-05", "ADR-06-CLOSURE"]),
    ("P5-T01", ["D32", "D33"], ["ADR-01", "ADR-03", "ADR-06-CLOSURE"]),
    ("P5-T02", ["D44-D47"], ["ADR-03", "ADR-03-CLOSURE"]),
    ("P5-T03", ["D32-D34"], ["ADR-03", "ADR-03-CLOSURE"]),
    ("P5-T04", ["D22-D31", "D44-D47"], ["ADR-02", "ADR-03"]),
    ("P6-T01", ["D53", "L56", "T73"], ["ADR-04", "ADR-06-CLOSURE"]),
    ("P6-T02", ["D45", "D53"], ["ADR-04", "ADR-06-CLOSURE"]),
    ("P6-T03", ["D53", "L56", "T73"], ["ADR-04", "ADR-06-CLOSURE"]),
    ("P7-T01", ["D8", "D19", "T15", "T16", "T20", "C21"], ["ADR-01", "ADR-03", "ADR-06-CLOSURE"]),
    ("P7-T02", ["D51", "D52", "R.iter", "R.fail", "T66"], ["ADR-05", "ADR-06-CLOSURE"]),
    ("P7-T03", ["L56", "T73"], ["ADR-04", "ADR-06-CLOSURE"]),
    ("P7-T04", ["T15", "T16", "T20", "C21", "D52"], ["ADR-01", "ADR-05", "ADR-06-CLOSURE"]),
    ("P7-T05", ["L56", "T73"], ["ADR-04", "ADR-06-CLOSURE"]),
]

# H04 blocking_decisions -> accepted ADRs (from the blueprint decision profile).
BD_ADR_MAP = {
    "BD-STATE": ["ADR-03"],
    "BD-EQUIV": ["ADR-01", "ADR-06-CLOSURE"],
    "BD-COEFFECT": ["ADR-02"],
    "BD-ITER": ["ADR-05"],
    "BD-NAMES": ["ADR-04"],
    "BD-SCOPED": [], "BD-STAGING": [], "BD-CONTROL": [], "BD-SUPPORT": [],
}

RANGE_RE = re.compile(r"^([A-Za-z.]*)(\d+)-([A-Za-z.]*)(\d+)$")


def main() -> None:
    h03 = json.loads(H03_PATH.read_text(encoding="utf-8"))
    h04 = json.loads(H04_PATH.read_text(encoding="utf-8"))

    if sha256_of(H03_PATH) != FROZEN_H03:
        sys.exit(f"ERROR: H03 hash mismatch at {H03_PATH}")
    if sha256_of(H04_PATH) != FROZEN_H04:
        sys.exit(f"ERROR: H04 hash mismatch at {H04_PATH}")

    numbered = h03["numbered_nodes"]
    auxiliary = h03["auxiliary_nodes"]
    num_of = {n["id"]: n["number"] for n in numbered}

    # --- task-derived ADR refs ------------------------------------------
    def expand(ref: str):
        m = RANGE_RE.match(ref)
        if not m:
            return [ref] if ref in num_of or ref in {a["id"] for a in auxiliary} else []
        lo, hi = int(m.group(2)), int(m.group(4))
        return [i for i, n in num_of.items() if lo <= n <= hi]

    task_adrs = {}
    for _task, refs, adrs in TASKS:
        for r in refs:
            for item in expand(r):
                task_adrs.setdefault(item, set()).update(adrs)

    # --- ledger rows ------------------------------------------------------
    def row_of(node, kind):
        iid = node["id"]
        disp = next(d for d in
                    (h04["numbered_dispositions"] if kind != "auxiliary"
                     else h04["auxiliary_dispositions"]) if d["id"] == iid)
        delivery, evidence, reason, notes = "planned", "pending", "", ""
        if iid in DEFERRED_ITEMS:
            delivery, evidence, reason = DEFERRED_ITEMS[iid]
        elif iid in DEFERRED_SUBPART:
            reason = DEFERRED_SUBPART[iid]
        if iid in NOTES:
            notes = NOTES[iid]

        adrs = set(task_adrs.get(iid, set()))
        for bd in disp["blocking_decisions"]:
            adrs.update(BD_ADR_MAP.get(bd, []))

        depends = sorted({e["source"] for e in h03["edges"] if e["target"] == iid})

        row = {
            "id": iid,
            "kind": kind,
            "paper_anchor": node["section"],
            "title": node["title"],
            "target_module": ITEM_MODULE.get(iid, ""),
            "treatment": disp["treatment"],
            "delivery_status": delivery,
            "evidence_state": evidence,
            "depends_on": depends,
            "adr_refs": sorted(adrs),
            "deferred_reason": reason,
            "notes": notes,
            # H03 node identity copies
            "h03_section": node["section"],
            # H04 disposition copies (baseline fields, not overwritten)
            "h04_target_layer": disp["target_layer"],
            "h04_paper_relation": disp["paper_relation"],
            "h04_blocking_decisions": disp["blocking_decisions"],
            "h04_readiness": disp["readiness"],
        }
        if kind != "auxiliary":
            row["number"] = num_of[iid]
        return row

    items = ([row_of(n, n["kind"]) for n in numbered]
             + [row_of(a, "auxiliary") for a in auxiliary])

    ledger = {
        "schema_version": "1.0",
        "plan_id": "DH-P0-EXEC-01",
        "generated_on": datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds"),
        "source_graph": {
            "path": "docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json",
            "sha256": sha256_of(H03_PATH),
        },
        "source_disposition": {
            "path": "docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json",
            "sha256": sha256_of(H04_PATH),
        },
        "delivery_vocabulary": DELIVERY_VOCAB,
        "evidence_vocabulary": EVIDENCE_VOCAB,
        "items": items,
    }

    OUT_PATH.write_text(json.dumps(ledger, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"wrote {OUT_PATH} with {len(items)} rows")


if __name__ == "__main__":
    main()
