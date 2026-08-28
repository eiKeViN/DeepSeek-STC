#!/usr/bin/env python3
"""Generate the deterministic P8 conformance/readiness manifest.

The generator reads frozen H03/H04, the P0 provenance record, the current
derived Definition Ledger, and the Blueprint candidate-ADR register.  It never
writes an input artifact and fails closed when a schema, hash, or coverage
assumption is violated.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
H03_PATH = ROOT / "docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json"
H04_PATH = ROOT / "docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json"
P0_PATH = ROOT / "docs/status/P0-baseline.json"
LEDGER_PATH = ROOT / "docs/status/Definition-Ledger.json"
BLUEPRINT_PATH = ROOT / "docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json"
OUT_PATH = ROOT / "docs/status/P8-conformance-manifest.json"


def read_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        raise SystemExit(f"manifest generation failed: cannot read JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise SystemExit(f"manifest generation failed: {path} is not a JSON object")
    return value


def sha256(path: Path) -> str:
    try:
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        return digest.hexdigest()
    except OSError as exc:
        raise SystemExit(f"manifest generation failed: cannot hash {path}: {exc}") from exc


def git(*args: str) -> str:
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise SystemExit(f"manifest generation failed: git {' '.join(args)}: {exc}") from exc


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"manifest generation failed: {message}")


def source_record(identifier: str, path: Path) -> dict[str, str]:
    require(path.is_file(), f"source artifact is missing: {path}")
    return {"id": identifier, "path": path.relative_to(ROOT).as_posix(), "sha256": sha256(path)}


def references(row: dict[str, Any]) -> list[str]:
    """Return stable declaration/file references without guessing theorem status."""

    result: list[str] = []
    target = row.get("target_module", "")
    if isinstance(target, str) and target:
        result.extend(part.strip() for part in target.split(";") if part.strip())
    notes = row.get("notes", "")
    if isinstance(notes, str):
        for name in re.findall(r"`([^`]+)`", notes):
            if name not in result:
                result.append(name)
    return result


def build_rows(h03: dict[str, Any], h04: dict[str, Any], ledger: dict[str, Any]) -> list[dict[str, Any]]:
    graph_rows = list(h03.get("numbered_nodes", [])) + list(h03.get("auxiliary_nodes", []))
    disposition_rows = list(h04.get("numbered_dispositions", [])) + list(h04.get("auxiliary_dispositions", []))
    graph = {row.get("id"): row for row in graph_rows}
    disposition = {row.get("id"): row for row in disposition_rows}
    require(len(graph_rows) == len(graph), "H03 rows must have unique IDs")
    require(len(disposition_rows) == len(disposition), "H04 rows must have unique IDs")
    rows = ledger.get("items")
    require(isinstance(rows, list), "ledger items must be a list")
    require(len(rows) == 82, f"ledger coverage is {len(rows)}, expected 82")
    ids = [row.get("id") for row in rows if isinstance(row, dict)]
    require(len(ids) == 82 and len(set(ids)) == 82, "ledger IDs must be present and unique")
    expected = set(graph) | set(disposition)
    require(set(ids) == expected, "ledger IDs do not match the frozen H03/H04 item set")

    output: list[dict[str, Any]] = []
    for row in rows:
        require(isinstance(row, dict), "every ledger item must be an object")
        identifier = row["id"]
        h03_row = graph.get(identifier)
        h04_row = disposition.get(identifier)
        require(h03_row is not None and h04_row is not None, f"missing frozen row for {identifier}")
        require(row.get("title") == h03_row.get("title") == h04_row.get("title"),
                f"title mismatch for {identifier}")
        output.append({
            "id": identifier,
            "kind": row.get("kind", h03_row.get("kind", "auxiliary")),
            "number": row.get("number", h03_row.get("number")),
            "section": row.get("section", h03_row.get("section", h04_row.get("section"))),
            "title": row["title"],
            "paper_anchor": row.get("paper_anchor", h04_row.get("section")),
            "target_module": row.get("target_module", ""),
            "references": references(row),
            "delivery_status": row.get("delivery_status"),
            "evidence_state": row.get("evidence_state"),
            "adr_refs": row.get("adr_refs", []),
            "blocking_decisions": row.get("h04_blocking_decisions", h04_row.get("blocking_decisions", [])),
            "deferred_reason": row.get("deferred_reason", ""),
            "notes": row.get("notes", ""),
            "treatment": h04_row.get("treatment"),
            "paper_relation": h04_row.get("paper_relation"),
            "readiness": h04_row.get("readiness"),
        })
    return output


def accepted_artifacts(p0: dict[str, Any]) -> list[dict[str, Any]]:
    artifacts = p0.get("p0_t02_freeze", {}).get("adr_artifacts", [])
    require(isinstance(artifacts, list), "P0 accepted ADR artifact record is missing")
    output = []
    for artifact in artifacts:
        identifier = artifact.get("id")
        path = ROOT / artifact["path"]
        actual = sha256(path)
        expected = artifact.get("workspace_sha256")
        require(actual == expected, f"canonical accepted artifact hash mismatch for {identifier}")
        output.append({
            "id": identifier,
            "path": artifact["path"],
            "record_status": "accepted",
            "canonical_sha256": actual,
            "blueprint_manifest_sha256": artifact.get("blueprint_manifest_sha256"),
            "matches_blueprint_manifest": actual == artifact.get("blueprint_manifest_sha256"),
        })
    return output


def candidate_artifacts(blueprint: dict[str, Any]) -> list[dict[str, Any]]:
    candidates = blueprint.get("source_manifest", {}).get("candidate_adrs", [])
    register = {entry["id"]: entry for entry in blueprint.get("decision_register", [])}
    require(len(candidates) == 4, "expected four candidate ADR packets")
    output = []
    for candidate in candidates:
        identifier = candidate["id"]
        status = register.get(identifier, candidate)
        packet = {
            "id": identifier,
            "record_status": status.get("record_status", candidate.get("record_status")),
            "metadata_status": status.get("metadata_status", candidate.get("metadata_status")),
            "architecture_status": status.get("architecture_status", candidate.get("architecture_status")),
            "formal_acceptance": status.get("formal_acceptance", candidate.get("formal_acceptance")),
            "artifact_completeness": status.get("artifact_completeness", candidate.get("artifact_completeness")),
            "compiler_status": status.get("compiler_status", candidate.get("compiler_status")),
            "compiler_exit_code": status.get("compiler_exit_code", candidate.get("compiler_exit_code")),
            "compiler_warning_count": status.get("compiler_warning_count", candidate.get("compiler_warning_count")),
            "artifacts": {},
        }
        for kind in ("markdown", "json", "lean_spike"):
            descriptor = candidate.get(kind)
            require(isinstance(descriptor, dict), f"{identifier} is missing {kind} descriptor")
            path = ROOT / "docs/blueprint/architecture-decision" / ("md" if kind == "markdown" else "json" if kind == "json" else "lean-spike") / descriptor["filename"]
            actual = sha256(path)
            require(actual == descriptor.get("sha256"), f"{identifier} {kind} hash mismatch")
            packet["artifacts"][kind] = {
                "path": path.relative_to(ROOT).as_posix(),
                "sha256": actual,
            }
        output.append(packet)
    return output


def main() -> None:
    h03 = read_json(H03_PATH)
    h04 = read_json(H04_PATH)
    p0 = read_json(P0_PATH)
    ledger = read_json(LEDGER_PATH)
    blueprint = read_json(BLUEPRINT_PATH)

    require(h03.get("metadata", {}).get("graph_version") == "1.0-frozen", "H03 graph schema/version mismatch")
    require(h04.get("metadata", {}).get("specification_version") == "1.0-baseline", "H04 disposition schema/version mismatch")
    require(ledger.get("schema_version") == "1.0", "Definition Ledger schema mismatch")
    p0_baselines = {item["id"]: item for item in p0.get("p0_t02_freeze", {}).get("frozen_baselines", [])}
    require(set(p0_baselines) == {"H03", "H04"}, "P0 baseline record must contain H03 and H04")
    for identifier, path in (("H03", H03_PATH), ("H04", H04_PATH)):
        baseline = p0_baselines[identifier]
        require(baseline.get("verified") is True, f"P0 {identifier} baseline is not verified")
        require(baseline.get("frozen_sha256") == baseline.get("observed_sha256"),
                f"P0 {identifier} frozen/observed hashes disagree")
        require(sha256(path) == baseline["frozen_sha256"], f"{identifier} hash mismatch")
    require(ledger.get("source_graph", {}).get("sha256") == sha256(H03_PATH),
            "ledger H03 source hash mismatch")
    require(ledger.get("source_disposition", {}).get("sha256") == sha256(H04_PATH),
            "ledger H04 source hash mismatch")

    rows = build_rows(h03, h04, ledger)
    deferred = [
        {"id": identifier, "reason": reason, "evidence_boundary": boundary}
        for identifier, reason, boundary in [
            ("BD-CONTROL", "ADR-07 remains proposed despite a compiler-validated spike; lifecycle/control production and theorem evidence are pending.", "A/I candidate evidence only; no production/K claim"),
            ("BD-STAGING", "ADR-08 remains proposed and its base/extended staging contracts are not production-integrated.", "A/I candidate evidence only; no simulation/adequacy K claim"),
            ("BD-SUPPORT", "ADR-09 remains proposed; support well-foundedness and confluence are not established.", "A/I candidate evidence only; no support/K claim"),
            ("BD-SCOPED", "ADR-10 remains proposed; scoped realm/coeffect semantics are acceptance-gated.", "A/I candidate evidence only; no production/K claim"),
            ("BD-COEFFECT", "Finite coeffect store interfaces exist, but the complete satisfaction/specification calculus remains pending.", "P5 interface/seam evidence; no complete Section 3.2 theorem claim"),
            ("RUNTIME-REFINEMENT", "No concrete Cordis carrier or executable refinement theorem is present in the metatheory package.", "R0 seam only; R1+ is deferred"),
        ]
    ]
    output = {
        "schema_version": "1.0",
        "manifest_id": "P8-conformance-manifest",
        "plan_id": "DH-P7-P8-EXEC-01",
        "repository": {
            "commit": git("rev-parse", "HEAD"),
            "branch": git("branch", "--show-current"),
            "working_tree": "clean" if not git("status", "--porcelain") else "dirty",
        },
        "sources": {
            "h03": source_record("H03", H03_PATH),
            "h04": source_record("H04", H04_PATH),
            "ledger": source_record("Definition-Ledger", LEDGER_PATH),
            "p0_provenance": source_record("P0-baseline", P0_PATH),
        },
        "coverage": {"numbered_items": 74, "auxiliary_items": 8, "total_items": 82},
        "status_vocabulary": {
            "delivery": ledger.get("delivery_vocabulary", []),
            "evidence": ledger.get("evidence_vocabulary", []),
            "typed_evidence": ["A", "I", "K", "E", "R0", "R1+"],
        },
        "accepted_adr_artifacts": accepted_artifacts(p0),
        "candidate_adr_packets": candidate_artifacts(blueprint),
        "items": rows,
        "deferred_obligations": deferred,
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with OUT_PATH.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(output, handle, indent=2, ensure_ascii=True)
        handle.write("\n")
    print(f"generated {OUT_PATH.relative_to(ROOT)} ({len(rows)}/82 items)")


if __name__ == "__main__":
    main()
