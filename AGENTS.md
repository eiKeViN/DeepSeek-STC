# DeepSeek-STC Repository Instructions

These instructions govern the paper-first Lean formalization of the Spatiotemporal Composability (STC) metatheory.


## Authority model

Authority is question-relative, not one total ordering:

- The paper is authoritative for the literal claims made by the source.
- The Formal Reference and frozen H03/H04 baselines are audited interpretation and provenance records; they preserve claims and defects but do not make defective claims true.
- Accepted ADRs and superseding ADRs are normative for the repaired formal target selected by this project.
- The Lean kernel is authoritative for validity of elaborated declarations and checked proof terms, but compilation alone is only interface evidence.
- The Blueprint, execution plans, and AGENTS.md govern implementation workflow and remain subordinate to the accepted semantic decisions.
- STC.Adapter and future Cordis artifacts provide only explicit abstraction or refinement evidence; they do not define the metatheory retroactively.

When sources conflict, preserve the literal source claim, classify the issue, record the approved repair in an ADR, and implement only the ADR-approved target. Never silently rewrite a frozen baseline or treat a successful build as proof of semantic alignment.

**Provenance ruling (2026-08-27).** Repository bytes are canonical for ADR-01, ADR-02, and the ADR-06 spike: they intentionally differ from the hashes recorded in the Blueprint companion manifest. The full hash record and the lead ruling live in `docs/status/P0-baseline.json`; a Blueprint hash revision is a pending lead follow-up. Do not "fix" these files or re-report the mismatch.


## Paper fidelity and proof integrity

- Keep literal paper statements distinct from repaired Lean targets.
- Record false, vacuous, ill-typed, non-computable, or under-specified claims before selecting a repair.
- Do not hide missing hypotheses in an oversized `WellFormed` predicate.
- Distinguish semantic propositions from executable data and algorithms.
- Do not claim that a metatheory theorem verifies the Cordis runtime without a separate refinement theorem.
- Production Lean must not contain `sorry`, `admit`, project-defined unchecked `axiom`, or `unsafe` declarations.
- Never manufacture a proof with an empty relation, impossible invariant, degenerate transition, or behavior-erasing observation.  If a statement is not proved, preserve a precise blocked obligation or counterexample.


## Repository map and boundaries

The metatheory namespace is `STC`.  Use the module families prescribed by the Blueprint:

```text
STC/Foundation
STC/Core
STC/State
STC/Alpha
STC/Examples
STC/Conformance
STC/Adapter
```

- `STC.Adapter` is the reserved abstract R0 abstraction/simulation seam.  Do not put concrete Cordis implementation declarations into the metatheory namespace; the `Cordis` name and its namespaces are reserved for a future runtime-side integration/refinement project.
- Frozen inputs (read-only): `docs/blueprint/baseline/` (H03 graph, H04 disposition, Formal Reference) and `docs/blueprint/architecture-decision/json/` (accepted ADRs).
- `docs/blueprint/architecture-decision/lean-spike/` is historical and read-only: never import it from production modules and never edit it.
- Derived status records live in `docs/status/` (`P0-baseline.json` provenance; `Definition-Ledger.json` traceability).  They are reports generated from frozen inputs, never sources of truth.  Execution plans live in `docs/plans/`.

The current accepted architecture includes relation-parametric laws, explicit partiality and failure results, the positive finite state/registry shell, lifetime-safe `IncarnationId` with explicit alpha actions, ranked iterators, and the ADR-06 equivalence/transport contracts.  Do not reopen these decisions implicitly.


## Working loop

Before and after each major task or critical checkpoint, run the narrowest applicable checks and record their outputs:

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/<changed-file>.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
```

- Use the pinned Lean 4.33.0 / Mathlib v4.33.0 toolchain.
- `lake env lean` does not read lakefile `leanOptions`; pass the `-D` flags above explicitly or single-file checks disagree with the IDE and with `lake build`.
- `scripts/scan_lean.py` exit codes: 0 = lexical match found (inspect and classify; a comment/string match is not a live declaration), 1 = clean, 2 = scan error.  A clean scan covers current files only, not future code.
- Keep the Definition Ledger current after each task: edit rows in place using the Blueprint vocabulary (delivery: `planned/in_progress/completed/blocked/deferred`; evidence: `pending/aligned/passed/proved/tested/seam_only/deferred/not_applicable`) and rerun the validator.  
- Do not rerun `gen_definition_ledger.py` after P0 — it regenerates from its P0 curation tables and would wipe later evidence.
- Keep commits focused, do not overwrite other agents' work, and report any baseline/hash or namespace mismatch instead of silently normalizing it.
