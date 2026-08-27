# STC Metatheory: P1 Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P1-EXEC-01` |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Baseline | P0 accepted on `origin/main` at `72bdbcd`; this branch also contains guidance patch `eacdb47` (not yet pushed) |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Prerequisite | P0 handoff merged and accepted; option 2 (workspace ADR copies are canonical) is the lead decision |
| Namespace | `STC` |
| Adapter boundary | `STC.Adapter` (R0 only) |
| Scope | `P1-T01`, `P1-T02`, `P1-T03` |
| Status | ready for implementation after preflight |

## 1. Objective

Build the first production foundation for the metatheory: an explicit,
relation-parametric vocabulary and field-preserving result relators. The wave
must produce at least one substantive, placeholder-free generic theorem and a
small executable positive/negative test suite.

This is a production realization of the accepted ADR-01/ADR-06 contracts. It
does not reopen `BD-EQUIV`, `BD-COEFFECT`, or any other blocker, and it does not
claim that all affected paper rows are already proved.

## 2. Required preflight

The executing agent must work from a branch based on the accepted current
`main`, preserve unrelated changes, and record the actual starting commit and
worktree status.

Read, without modifying, these inputs:

```text
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json
docs/blueprint/architecture-decision/json/*.json
docs/status/P0-baseline.json
docs/status/Definition-Ledger.json
docs/status/P0-handoff-report.md
AGENTS.md
README.md
lean-toolchain
lakefile.toml
lake-manifest.json
STC.lean
STC/Bootstrap.lean
```

The paper PDF is a read-only mathematical source. Do not copy it into the
repository. Do not use the Project Guide or Research Ledger as formalization
dependencies. Do not import any Lean file under
`docs/blueprint/architecture-decision/lean-spike/`.

Run and record the P0 gate before changing production code:

```bash
git status --short --branch
git log -1 --oneline
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC  # acceptance requires exit code 1 (clean)
lake env lean STC/Bootstrap.lean
lake build
```

The Python scan's exit code is part of its contract: `1` means clean, `0` means
matches were found, and `2` means a scan error. A missing `lake`/`lean` binary
is `blocked`, not a successful interface check.

Verify that:

1. H03 and H04 bytes remain the frozen values recorded by P0.
2. `docs/status/P0-baseline.json` records reconciliation option 2 and the
   workspace-canonical ADR-01, ADR-02, and ADR-06-spike hashes.
3. The Blueprint/hash revision remains a provenance follow-up; do not edit it
   during P1.
4. No active production file uses `CordisADR*`, `DeepSeekHarness`, or
   `Adapters.Cordis`.

Record the preflight in the P1 handoff (or a derived
`docs/status/P1-preflight.json`). Do not rewrite the P0 report.

## 3. P1-DEC-01 — Canonical ownership and dependency decision

The Blueprint has an overlap between its module table and later wave
descriptions. P1 fixes the following representational ownership to prevent
duplicate declarations:

| Declaration family | Sole P1 owner | Later users |
|---|---|---|
| `RelSpec`, relation liftings, `OptionRel` | `STC/Foundation/Relation.lean` | all later layers |
| `EffectResult`, `Failure`, `ExecResult` and their relators | `STC/Foundation/Result.lean` | P2 Effect, P3 partiality, P4 iterator |
| `Effect`, `IsLawfulEffect`, sequential execution | not P1; P2 `STC/Core/Effect.lean` | P2 onward |
| `PartialOp` and operation semantics | not P1; P3 `STC/Core/Partial.lean` | P3 onward |
| `StageResult`, ranked iterator and execution | not P1; P4 `STC/Core/Iterator.lean` | P4 onward |
| concrete `StateLike`/`ValidState`/`Finmap` instances | not P1; P5 / ADR-02–03 work | P5 onward |

The intended import direction is:

```text
STC.Foundation.Relation → STC.Foundation.Result → later Core/State modules
```

`Result.lean` may import `Relation.lean`. No reverse import or duplicate
relation vocabulary is permitted. This is an execution-level clarification of
the Blueprint's conceptual DAG; it does not edit the frozen Blueprint.

Recommended result representation:

```lean
structure EffectResult (S : Type u) where
  state : S
  undo : S → S

structure Failure (S : Type u) (E : Type v) where
  error : E
  boundary : S
  prefixUndo : S → S

inductive ExecResult (S : Type u) (E : Type v) where
  | success (result : EffectResult S)
  | failure (failure : Failure S E)
```

The constructor layout may use direct fields instead of payload wrappers if
Lean ergonomics require it, but there must be one canonical carrier, named
access to all three failure fields, and no redeclaration in P2–P4. In either
layout, a failure is not `Option.none` and must retain its error, boundary, and
prefix inverse.

## 4. Task breakdown

### P1-T01 — Relation vocabulary

Target: `STC/Foundation/Relation.lean`.

Port the ADR-06 canonical names under `namespace STC`:

```lean
structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def RespectsOn (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) : Prop := ...

def Respects (R : RelSpec α) (f : α → α) : Prop := ...

def PointwiseRel (R : RelSpec α) (f g : α → α) : Prop := ...

def CrossRel (R : RelSpec α) (f g : α → α) : Prop := ...
```

The names have fixed meanings:

- `PointwiseRel` compares two maps at the same input;
- `CrossRel` compares outputs of two maps at related inputs;
- `RespectsOn` is the heterogeneous preservation predicate.

If a genuinely heterogeneous same-input helper is needed, give it a distinct
name such as `SamePointwiseRel` or `PointwiseRelOn`. Do not overload the
canonical endomap names, and do not import the old ADR-05 naming.

`Relation.lean` also owns the tag-strict generic `OptionRel` and its equivalence
shell. Add a generic pullback relation for an observation map if convenient,
and an explicit equality/`Eq` `RelSpec` specialization (with a named helper
that later tests can use). Do not define the concrete P5 observation family or
dependent coeffect store here.

### P1-T02 — Result carriers and relators

Target: `STC/Foundation/Result.lean`, importing only the production Relation
module.

Define field-preserving relators:

```text
EffectResultRel R
FailureRel R E
ExecRel R E
```

For related states:

- success relates success when successor states are related and selected undo
  maps satisfy same-input `PointwiseRel`;
- failure relates failure when error payloads satisfy an explicitly supplied
  error relation, boundary states satisfy the state relation, and prefix undo
  maps satisfy `PointwiseRel`;
- success/failure and failure/success are false.

Provide equivalence shells such as `effectResultRelSpec`, `failureRelSpec`, and
`execRelSpec` when the state and error relations are `RelSpec` values. Ordinary
errors/outcomes use equality only through an explicit helper; do not infer an
observation relation from the state relation.

Do not define `Effect`, `PartialOp`, `StageResult`, iterator execution,
coeffect-key lifts, or concrete `StateLike` instances in this task.

### P1-T03 — Generic proofs, tests, and integration

Prove the reusable relation kernel in `Relation.lean` and `Result.lean`. The
minimum theorem family is:

```text
crossRel_of_respects_pointwise
pointwiseRel_of_crossRel
respects_of_crossRel_self
respects_left_of_crossRel
respects_right_of_crossRel
respects_id
respects_comp
pointwiseRel_refl
pointwiseRel_symm
pointwiseRel_trans
compose_pointwiseRel
optionRelSpec
effectResultRelSpec
failureRelSpec
execRelSpec
```

The two `respects_*_of_crossRel` endpoint theorems are valid for `RelSpec`
(reflexive/symmetric/transitive relations). They must not be generalized to a
future directed simulation relation without a separate relation package.

Add a small test module, preferably
`STC/Examples/RelationResult.lean`, and import it from
`STC/Bootstrap.lean`. It must include:

1. an orientation example distinguishing same-input `PointwiseRel` from
   related-input `CrossRel`;
2. a finite positive relation/relator check using an explicitly decidable
   fixture (for example, `decide` or a small `#eval` wrapper);
3. a negative mixed-constructor check for `OptionRel` or `ExecRel`;
4. an equality-specialization check;
5. at least one nontrivial generic theorem whose proof is checked by Lean.

The executable E fixture must use finite, decidable relations and record the
observed result; a Prop-valued example that merely elaborates is I evidence,
not E evidence. Do not satisfy a proof target with an empty relation,
`True`-only law, an impossible invariant, or an observation that erases the
relevant fields.

Finally update `STC/Bootstrap.lean` to import the canonical production modules
and tests. Keep the root `STC.lean` as the package entrypoint; do not import
historical spikes.

## 5. Paper and ADR boundary

P1 provides infrastructure for the following rows, but its completion status
must remain granular:

| Rows | P1 contribution | What remains later |
|---|---|---|
| D36 | canonical relation-respecting/pointwise/cross definitions and proofs | none at the generic vocabulary level |
| D33 | generic pullback/observation shell | concrete state/coeffect observation in P5 |
| D37 | result-relator shape and selected-inverse field contract | lawful effects and recovery in P2 |
| L38 | relation-parametric theorem hook/specialization infrastructure | full theorem manifest and effect instances across P2+ |
| D39, T40, D41, T42 | no concrete operation/coeffect theorem in P1 | P3/P5 and BD-COEFFECT |

Do not mark D37 or L38 globally proved merely because their shells compile.
Do not edit the frozen H04 readiness values. Update only derived ledger fields
after actual evidence exists, retaining explicit notes for deferred dependencies.

At minimum, a successful P1 handoff may promote the generic D36 vocabulary and
its checked relation lemmas. D33 may receive only a generic-shell evidence note;
D37 and L38 remain staged until their P2/P5 dependencies are implemented.
D39/T40/D41/T42 remain planned or blocked by their coeffect/partiality
dependencies. Preserve the H03 dependency lists and H04 readiness fields
exactly; do not infer transitive readiness from a compiling shell.

P1 does not address:

```text
BD-CONTROL, BD-STAGING, BD-SUPPORT, BD-SCOPED
typed D34 tests or L35 coeffect countermodels
tracked-context/accumulator recovery
concrete ValidState/WellFormed/provider preservation
ranked iterator execution or lifecycle rules
alpha actions on named control/ambient payloads
Cordis runtime code or R1+ refinement
```

## 6. Validation and evidence gates

For each task, record the exact command and output. The minimum gate is:

```bash
lake env lean STC/Foundation/Relation.lean
lake env lean STC/Foundation/Result.lean
lake env lean STC/Examples/RelationResult.lean
lake env lean STC/Bootstrap.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
```

Preserve the scan output at `docs/status/P1-scan-raw.txt` or the repository's
established derived-status path. If `lake` or `lean` is unavailable, record
`not_run`/`blocked` with the exact error.

| Gate | Required evidence | Does not establish |
|---|---|---|
| G-A | paper ↔ ADR ↔ API mapping; explicit scope and repair notes | theorem truth |
| G-I | changed files and package build elaborate; imports are acyclic | semantic lawfulness |
| G-K | substantive generic proof terms, no placeholders/custom axioms/unsafe | Cordis correspondence |
| G-E | finite positive and tag-mismatch tests with recorded output | generic theorem validity by itself |
| G-H | H03/H04 and ADR provenance unchanged; ledger validator passes | correctness of frozen paper claims |

For the final scan, exit code `1` is the required clean result; exit `0` means
matches were found and exit `2` means a scan error, either of which blocks
acceptance until classified and resolved. P1 earns no `R0` or `R1+` evidence.
A compiled interface is `I`, not `K`.

## 7. Execution order and collaboration

Use one API owner for `Relation.lean` and one for `Result.lean`, but integrate
sequentially:

1. P1-T01 freezes the relation API and commits it.
2. P1-T02 ports the result carriers/relators against that API.
3. P1-T03 proves the combined theorem family, adds tests, updates Bootstrap,
   and updates derived status.

Two agents may work on separate files, but neither should edit
`STC.lean`, `STC/Bootstrap.lean`, or the ledger concurrently. An integration
owner performs the final import and status update.

Suggested commits:

```text
p1: add explicit relation foundation
p1: add result carriers and relators
p1: prove relation/result laws and finite tests
p1: integrate bootstrap and derived evidence
```

## 8. Handoff and stop conditions

The P1 handoff must contain:

1. task IDs and subtask ownership;
2. base commit, final commit, branch, and worktree status;
3. changed paths and public declarations;
4. exact compiler, build, validator, and scan commands/results;
5. H03/H04/ADR hash confirmation;
6. theorem list with separate `I` and `K` evidence;
7. finite test inputs and outputs (`E`);
8. updated ledger rows and deferred reasons;
9. assumptions, counterexamples, vacuity checks, and unresolved API issues;
10. confirmation that no frozen input, ADR, or historical spike was modified.

Stop and request review if:

- a proposed signature requires a global `Setoid` or quotient execution carrier;
- result relators erase constructor tags, failure boundaries, or selected inverses;
- a theorem needs a missing hypothesis that would alter an accepted ADR;
- the Blueprint's stale documentation path (`Adapters.Cordis`) would be copied
  into production. If it appears only in archival Blueprint prose, record it as
  a separate editorial documentation issue and continue;
- a hash mismatch is found outside the P0-recorded option-2 reconciliation.

The preferred handoff path is `docs/status/P1-handoff-report.md`. The intended
next wave after an accepted P1 handoff is P2's shallow reversible
Effect kernel. P1 should leave that layer with a stable, relation-aware
foundation rather than pre-implementing it.
