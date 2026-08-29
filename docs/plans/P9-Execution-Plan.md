# STC P9 Execution Plan: ADR Promotion Gates

| Field | Value |
|---|---|
| Plan ID | `DH-P9-EXEC-01` |
| Depends on | P8 (`DH-P7-P8-EXEC-01`) |
| Scope | Architecture-decision status documentation only |
| Toolchain | Lean 4.33.0 / Mathlib v4.33.0 |
| Status | Completed |

## Objective

Promote the compiler-validated ADR-07, ADR-08, ADR-09, and ADR-10 candidate
packets through an explicit lead acceptance record. The candidate Markdown,
JSON, and Lean spike files remain historical inputs and are not rewritten.

Acceptance closes only the named architecture/interface question. It does not
claim production integration, a checked Section-4 theorem, executable runtime
refinement, or Cordis verification.

## Tasks and gates

| Task | Deliverable | Result |
|---|---|---|
| P9-T01 | Audit P8 manifest, candidate completeness, and companion hashes | Passed |
| P9-T02 | Record explicit acceptance for ADR-07 through ADR-10 | Passed |
| P9-T03 | Record downstream gates and evidence boundaries | Passed |
| P9-T04 | Run JSON, hash, focused Lean, and repository integrity checks | Passed |

## Acceptance rule

The explicit acceptance instruction for this run is recorded in each status
packet under `acceptance_basis`. Compiler success remains `I` evidence only.
The accepted records are the normative status source; candidate packet
`formal_acceptance` fields and historical spike bytes are preserved.

## Downstream gates

* ADR-07 acceptance authorizes planning/implementation of `STC/Control/**`;
  each concrete guard, preservation, recovery, and progress result still needs
  its own `K` evidence.
* ADR-08 and ADR-09 acceptance authorizes their respective staging/support
  integration only after the control dependencies are available.
* ADR-10 acceptance authorizes planning/implementation of `STC/Scoped/**`;
  no runtime or Section-4 generalization follows without explicit refinement.

The Definition Ledger is not rewritten by P9. Production modules remain
acceptance-gated by the records in `docs/blueprint/architecture-decision/status/`.
