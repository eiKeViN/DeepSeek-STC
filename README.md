# DeepSeek-STC

Lean 4 formalization and audit workspace for the metatheory of [*A Programming
Paradigm for Spatiotemporal Composability*](https://arxiv.org/abs/2608.25512)
(arXiv:2608.25512).  The project builds a paper-facing
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

P1 (relation and result foundations) and P2 (the shallow reversible effect
kernel, its R0 interpreter seam, and finite executable fixtures) are complete
and merged: `STC/Foundation/`, `STC/Core/`, and `STC/Examples/` now follow the
mathlib module style recorded in [`AGENTS.md`](AGENTS.md), and `lake build` is
green.

The next steps run in parallel: the P3→P4 workstream (partial operations and
failure, then the ranked iterator — sequential within the workstream, per
[`docs/plans/P3-P4-Execution-Plan.md`](docs/plans/P3-P4-Execution-Plan.md)) and
the P5 workstream (abstract state, observation, registry, and ADR-03 adapter
interfaces, per [`docs/plans/P5-Execution-Plan.md`](docs/plans/P5-Execution-Plan.md)).
The two tracks must not edit each other's work.

A compiling file is an interface result, not automatically a semantic proof;
the project records `A`, `I`, `K`, `E`, `R0`, and `R1+` evidence separately.

## Authoritative material

Execution plans live under [`docs/plans`](docs/plans/) and the paper/architecture
baseline under [`docs/blueprint`](docs/blueprint/).

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
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/<changed-file>.lean
lake build
```

Historical ADR spikes under `docs/blueprint/architecture-decision/lean-spike/`
are read-only compiler fixtures.  They are not production imports.  See
[`AGENTS.md`](AGENTS.md) for the complete authority order, proof-integrity
rules, and contribution workflow.
