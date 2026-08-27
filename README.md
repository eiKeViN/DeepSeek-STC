# DeepSeek-STC

Lean 4 formalization and audit workspace for the metatheory of *A Programming
Paradigm for Spatiotemporal Composability*.  The project builds a paper-facing
STC kernel first, with a deliberately separate future refinement boundary for
the Cordis implementation.

The current plan does not claim end-to-end verification of the TypeScript
Cordis runtime, the complete Section 4 lifecycle/control calculus, deep effect
DSL semantics, scoped realms/interception, or full runtime refinement. These
remain explicit later obligations rather than assumed consequences of a
successful package build.

## Current status

P0 (baseline, provenance, Definition Ledger, and bootstrap hygiene) is complete
and recorded in [`docs/status`](docs/status/).  The 82-item ledger and its
validator are part of the repository, and the minimal bootstrap builds under
the pinned Lean 4.33.0 / Mathlib v4.33.0 environment.

P1 is the next execution step: relation and result foundations.  A compiling
file is an interface result, not automatically a semantic proof; the project
records `A`, `I`, `K`, `E`, `R0`, and `R1+` evidence separately.

## Authoritative material

The executable plan and paper/architecture baseline live under
[`docs/blueprint`](docs/blueprint/).  The current P0 plan and handoff are:

- [`docs/plans/P0-Execution-Plan.md`](docs/plans/P0-Execution-Plan.md)
- [`docs/status/P0-handoff-report.md`](docs/status/P0-handoff-report.md)

The formalization inputs are the paper, the Formal Reference, H03/H04, and the
accepted ADRs.  

## Namespace and planned modules

All metatheory declarations use the `STC` namespace:

```text
STC/Foundation/
STC/Core/
STC/State/
STC/Alpha/
STC/Examples/
STC/Conformance/
STC/Adapter.lean
```

`STC.Adapter` is an abstract R0 abstraction/simulation seam only.  The name
`Cordis` and its namespaces are reserved for future runtime-side code and do
not identify the STC metatheory kernel.  Concrete runtime verification requires
an explicit source audit and an R1+ simulation/refinement theorem.

The first substantive slice is intended to contain two disjoint counters,
reversible effects, an explicit failure path, a ranked iterator, and an alpha
transport test.  The current `STC/Bootstrap.lean` remains intentionally small
until P1/P2 production modules are extracted from the historical spikes.

## Validation

From the repository root, use the pinned toolchain and the focused checks:

```bash
lake env lean STC/<changed-file>.lean
lake build
```

Historical ADR spikes under `docs/blueprint/architecture-decision/lean-spike/`
are read-only compiler fixtures.  They are not production imports.  See
[`AGENTS.md`](AGENTS.md) for the complete authority order, proof-integrity
rules, and contribution workflow.
