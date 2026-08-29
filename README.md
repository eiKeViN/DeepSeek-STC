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

P0 through P9 are complete and merged: the repository contains the frozen
provenance record, 82-item Definition Ledger and validator, relation/result
foundations, reversible effect/iterator/state kernels, alpha transport, R0 seam,
finite fixtures, and accepted ADR-07..10 status records under the pinned Lean
4.33.0 / Mathlib v4.33.0 environment.

P3 through P8 (partial operations/failure, ranked iterator, state/registry,
alpha transport, vertical slice, and conformance) are complete.  Their detailed
evidence is recorded in the
[`P3`](docs/status/P3-handoff-report.md),
[`P4`](docs/status/P4-handoff-report.md), and
[`P5`](docs/status/P5-handoff-report.md), [`P8`](docs/status/P8-handoff-report.md),
and [`P9`](docs/status/P9-handoff-report.md) handoffs.

P10 Control, P11 Staging/Support, and P12 Scoped plus their integration closeouts
are merged; P13 global metatheory is the current execution lane. Earlier execution
plans remain historical records and are not renumbered.

ADR-07 through ADR-10 have explicit accepted status records.  P10 Control, P11
Staging, and P11 Support Core are merged, and the P11 integration closeout adds
the cross-module closure, alpha, trace, and macro bridges.  Acceptance and
compilation remain distinct from kernel theorem strength or runtime refinement;
Scoped production is a completed independent P12 layer. Global Section-4 results
are being delivered under the P13 gates; Cordis refinement remains pending. The
historical audit record is in
[`docs/status/ADR-07-10-reconciliation.md`](docs/status/ADR-07-10-reconciliation.md).

A compiling file is an interface result, not automatically a semantic proof;
the project records `A`, `I`, `K`, `E`, `R0`, and `R1+` evidence separately.

## Authoritative material

Execution plans live under [`docs/plans`](docs/plans/) and the paper/architecture
baseline under [`docs/blueprint`](docs/blueprint/).

The formalization inputs are the paper, the Formal Reference, H03/H04, and ADRs
with an explicit accepted status.  Directory location alone does not establish
acceptance; see [`AGENTS.md`](AGENTS.md) and the Blueprint's ADR status register.

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

The merged fixtures contain two disjoint counters, reversible effects, explicit
failure paths, ranked iterators, labelled Control traces, derived Staging macros,
and support certificate transport.  Name-bearing runtime payload refinement and
global Section-4 theorems remain open.

The current production families include Control, Staging, and Support:

```text
STC/Control/**
STC/Staging/**
STC/State/Support.lean
STC/State/Support/Closure.lean
STC/State/Support/Alpha.lean
STC/Control/Support.lean
STC/Staging/Support.lean
STC/Examples/SupportTrace.lean
STC/Scoped/**
```

`STC/Scoped/**` is the completed independent ADR-10 P12 lane. P13 adds the
old-paper single-realm global state/rule/metatheory families and a separate
conformance manifest; realm-aware generalization and Cordis R1+ remain outside.

## Validation

From the repository root, use the pinned toolchain and the focused checks:

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/<changed-file>.lean
lake build
```

### Git worktrees and Lake

`.lake` is intentionally ignored by Git, so a newly created worktree does not
inherit build artifacts.  Initialize a worktree from an existing checkout with
the pinned dependencies as follows:

```bash
python scripts/prepare_worktree_lake.py
lake build
```

The helper links only `.lake/packages` when the manifest and `lean-toolchain`
match.  Each worktree keeps its own `.lake/build`, so branch-specific `STC`
OLean files cannot overwrite one another.  When no populated compatible
worktree exists, run `lake update` once in a checkout and rerun the helper.

Historical ADR spikes under `docs/blueprint/architecture-decision/lean-spike/`
are read-only compiler fixtures.  They are not production imports.  See
[`AGENTS.md`](AGENTS.md) for the complete authority order, proof-integrity
rules, and contribution workflow.
