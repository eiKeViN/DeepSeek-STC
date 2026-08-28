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

P0 through P2 are complete and merged: the repository contains the frozen
provenance record, 82-item Definition Ledger and validator, relation/result
foundations, shallow reversible effect kernel, R0 interpreter seam, and finite
fixtures under the pinned Lean 4.33.0 / Mathlib v4.33.0 environment.

P3 and P4 (partial operations/failure and the ranked iterator) are complete and
merged through PR #7; P5 (abstract state, observation, registry, dependent
coeffect facade, and ADR-03 state seam) is complete and merged through PR #6.
Their detailed evidence is recorded in the
[`P3`](docs/status/P3-handoff-report.md),
[`P4`](docs/status/P4-handoff-report.md), and
[`P5`](docs/status/P5-handoff-report.md) handoffs.  The central Definition
Ledger is still the P5-derived snapshot, so the exact P3/P4 row patches remain
an integration follow-up even though their code is merged.

The next first-kernel wave is P6 alpha transport, followed by the P7 integrated
vertical slice and P8 conformance/R0 work.  P0-P5 execution plans remain
historical records and are not renumbered.

ADR-07 (control), ADR-08 (staging), and ADR-09 (support) currently have
proposed/compiler-pending packets, but their standalone spikes fail the pinned
compiler checks.  ADR-10 (scoped coeffects) has only a failing spike and lacks
its companion Markdown/JSON packet.  None is an accepted normative input yet;
production integration and Section-4 `K` theorems remain pending.

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

The merged fixtures already contain two disjoint counters, reversible effects,
an explicit failure path, and a ranked iterator.  P6/P7 still own the genuine
name-bearing alpha transport and integrated vertical-slice evidence.

After P8, these module families are reserved only for explicitly accepted ADRs:

```text
STC/Control/**
STC/Staging/**
STC/State/Support.lean
STC/Scoped/**
```

They do not exist yet and must not be created from the current proposed or
incomplete packets.

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
