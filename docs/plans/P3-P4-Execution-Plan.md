# STC Metatheory: P3 → P4 Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P3-P4-EXEC-01` |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Prepared | 2026-08-28 |
| Baseline | `origin/main` at `9969ec5` (P0, P1, and P2 merged) |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Scope | P3 partial operations/failure, then P4 ranked iterator |
| Ownership | One agent, sequentially: P3 gate must pass before P4 starts |
| Parallel track | P5 may run independently and must not edit this workstream |
| Namespace | `STC` |
| Adapter boundary | `STC.Adapter` remains reserved; no runtime refinement is claimed |
| Status | Ready after preflight |

Fork this branch and the P5 branch from the same `origin/main` commit. P3/P4
and P5 may merge in either order after their independent gates; P6 waits for
both handoffs.

## 1. Mission

This workstream turns the merged shallow `Effect` kernel into an explicit
partial-operation and iterator layer. One agent owns both waves so that the
meaning of definedness, failure boundaries, selected inverses, and prefix undo
does not change at the handoff between P3 and P4.

The work implements accepted ADR-01/02/05/06 contracts. It does not reopen an
ADR, edit frozen H03/H04, or claim the full Section 4 lifecycle calculus.

## 2. Baseline and preflight

Start from the current remote main, not an older local branch:

```bash
git fetch origin --prune
git switch -c <p3-p4-branch> origin/main
git status --short --branch
git log -1 --oneline
```

Read without modifying:

```text
AGENTS.md
README.md
lean-toolchain
lakefile.toml
lake-manifest.json
STC.lean
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json
docs/blueprint/architecture-decision/json/*.json
docs/status/P0-baseline.json
docs/status/P1-handoff-report.md
docs/status/P2-handoff-report.md
docs/status/Definition-Ledger.json
STC/Foundation/Relation.lean
STC/Foundation/Result.lean
STC/Core/Effect.lean
STC/Core/EffectCode.lean
STC/Bootstrap.lean
```

Do not use the Project Guide or Research Ledger as formalization dependencies.
Historical Lean spikes are read-only and must never be imported into production.

Run and record the P2 baseline gate before production edits:

```bash
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
```

Scanner exit codes are part of the protocol: `1` clean, `0` lexical match,
`2` scan error. Missing Lean/Lake is `blocked`, not a pass. Verify H03/H04
and accepted ADR hashes against the P0 option-2 provenance record.

## 3. Dependency and ownership gates

The required order is:

```text
P3-PREP (D17/L18 check or explicit defer)
  → P3-T01 partial result carrier
  → P3-T02 operation laws and independence contracts
  → P3-T03 failure bridge
  → P3-T04 finite failure example
  → P3 handoff gate
  → P4-T01 ranked stage/continuation carrier
  → P4-T02 well-founded execution and prefix undo
  → P4-T03 relation/witness interfaces
  → P4-T04 nested success/failure tests
  → P4 handoff
```

P5 may run in parallel, but neither workstream may edit these integration-owned
paths concurrently:

```text
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/P3-scan-raw.txt
docs/status/P4-scan-raw.txt
docs/status/P3-handoff-report.md
docs/status/P4-handoff-report.md
```

P1/P2 public APIs are stable dependencies. Do not redeclare or semantically
alter `RelSpec`, `PointwiseRel`, `CrossRel`, `EffectResult`, `Failure`,
`ExecResult`, `Effect`, `seqRun`, or `IsLawfulEffect`.

## 4. P3 — partial operations and failure

### P3-PREP — residual dependencies and carrier check

P2 left D17/L18 (generated transformation closure and its generic commutation
lemmas) as a residual ledger obligation. Before using D19/T20/C21, inspect
whether the existing `Transformation` API is sufficient. The preferred repair
is a small additive completion in a new narrowly named companion such as
`STC/Core/Generated.lean`, importing `STC/Core/Effect.lean`. Do not edit the
P2-owned `Effect.lean` by default; if a declaration genuinely must be added
there, obtain integration-owner review and preserve every existing declaration
and theorem statement.

The non-vacuity shell is mandatory before an independence contract is accepted:
provide `TransformationMonoidProfile` identity/composition closure and a
`GeneratedEffectProfile` recording the effect forward map and every returned
undo as members. If the completion would require a new semantic decision or
become large, leave only the paper's least-generated-monoid equality (D17/L18)
deferred and implement the relation-level contracts against the explicit
profiles. The handoff must state which case occurred; never mark T20/C21
proved on an unimplemented generated-closure assumption.

Before adding `OpResult`, also check the partiality boundary against ADR-02 and
ADR-06. `Option` is the mathematical undefinedness/`Option`-Kleisli layer;
`Failure`/`ExecResult` is the diagnostic iterator layer. They are related by
explicit bridges, not by treating `none` as a failure with invented data. The
minimal P3 carrier should follow the accepted ADR-06 shape below. If an
operation needs a guarded/partial inverse from ADR-02, expose a `PartialMap`
adapter or a proof-indexed totalization explicitly; do not silently change the
meaning of the selected `undo` field.

### P3-T01 — explicit partial outcomes

Primary file: `STC/Core/Partial.lean`. Use one canonical Option-tagged
carrier. A suitable shape (with `Option` as the mathematical undefinedness
tag) is:

```lean
structure OpResult (S : Type u) (A : Type v) where
  state : S
  undo : S → S
  outcome : A

abbrev PartialOp (S : Type u) (A : Type v) :=
  S → Option (OpResult S A)

abbrev PartialMap (α : Type u) (β : Type v) := α → Option β

def pcomp (f : PartialMap α β) (g : PartialMap β γ) :
    PartialMap α γ := fun x => (f x).bind g
```

Names may be adjusted for Lean ergonomics, but definedness, outcome, successor,
and selected undo must remain explicit. `none` relates only to `none`; two
`some` values relate through an explicit state relation, a selected-inverse
relator, and an outcome relation (equality by default). Do not introduce a
second inductive undefined/success semantics unless it is a proved view of this
`Option` carrier with round-trip and bind-compatibility lemmas.

The ADR-06 `OpResult` above is the minimal success payload used by the current
closure API. Do not silently alias ADR-02's `PartialResult` if its `undo` field
has type `PartialMap S S`: implement that as a separate explicit layer, or add
a proof-indexed total-undo specialization and a round-trip/refinement theorem.
A protocol-guarded partial inverse must remain a `PartialMap` until a visible
precondition proves that a total `undo : S → S` is legitimate. The total P2
`EffectResult` embedding is a separate, explicit success-only specialization.

Do not introduce a concrete dependent coeffect store in this task.

### P3-T02 — respect, stability, and independence contracts

Define the smallest reusable predicates/law records for:

- common definedness on related inputs;
- outcome stability under an explicitly supplied outcome relation;
- relation-respecting partial operations and selected inverses;
- foreign-transformation inverse stability;
- operation/effect independence and commutative-key premises.

Prefer the ADR-06 names `WeakOperationRespects`,
`SelectedInverseCoherent`, `OperationRecovers`, `OperationRespects`,
`DefinedAt`, `DefinednessStable`, `OutcomeStable`,
`SelectedInverseStableOp`, `OperationForeignStability`, and
`OperationIndependenceContract` (or document exact equivalent names). If the
D17/L18 companion is created, use explicit `TransformationMonoidProfile` and
`GeneratedEffectProfile` membership/closure evidence rather than a bare
predicate that could be vacuous.

Use P1's `OptionRel` for definedness and tag preservation, and use
`PointwiseRel`/`CrossRel` with the canonical meanings fixed by ADR-06. The
default successful-result relator should expose related successor states,
pointwise-related selected inverses, inverse properness, and exact outcomes;
do not replace it with P2's total `EffectResultRel` unless the operation has
first been explicitly embedded into the total fragment.

Keep related-input coherence (P2's `run_respects`) distinct from D19 foreign
stability. Prove at least one nontrivial generic closure/commutation theorem
against the non-vacuous generated profiles and one finite counterexample. The
least-generated-monoid identification may remain deferred, but the contract
must not be detached from its generators. Concrete coeffect independence is
still deferred beyond the P5 dependent-store façade until the ADR-02 operation
layer is implemented.

### P3-T03 — failure bridge

Primary file: `STC/Core/Partial.lean` for partial carriers and any
`OpResult`/diagnostic adapter. If a generic success-only helper is useful, add
it additively to `STC/Foundation/Result.lean`; that Foundation file must not
import `Core.Partial`, so the import graph stays acyclic.
Reuse the merged `Failure` and `ExecResult` carriers. Do not define a second
`Failure` or `ExecResult`; add only bridge/helper declarations needed to embed
successful `EffectResult` values (or an explicit, documented outcome-erasure
projection of `OpResult`) into them. The projection must state whether the
outcome is observationally irrelevant; otherwise retain it in a separate
diagnostic payload. A `none` partial result alone does not contain an error,
boundary, or undo and therefore must not be converted to `ExecResult.failure`
without an explicit diagnostic handler supplying those fields.

Every failure retains:

```text
error       : E
boundary    : S
prefixUndo  : S → S
```

Failure is not `Option.none`, an identity effect, or an input-state rewrite.
The general carrier permits an observably different boundary; atomicity is only
the Toy specialization selected by G6.

### P3-T04 — finite Toy failure

Primary file: `STC/Examples/TwoCounter.lean`. Add the minimal P3 failure
fixture without editing Bootstrap. This file is a staged example path: P3 owns
only the failure declarations and checks; the later P7 owner extends it after
P6, with no concurrent edit. Include a `failIfZero`-style atomic Toy
specialization, a nontrivial successful prefix, and an evaluated finite report
showing preservation of error, boundary, and prefix undo. Use decidable data for
E evidence; elaboration alone is I evidence.

### P3 gate

P3 is ready for handoff when the Option-based partial API elaborates, its
relators and laws preserve the undefined/success distinction, the failure
bridge reuses P1/P2 carriers without inventing diagnostics, generic proofs are
honestly classified, finite positive/negative checks distinguish
undefined/success/failure, and no shared, frozen, or historical file was
modified.

## 5. P4 — ranked iterator

P4 starts only after the P3 handoff records the final partial/failure API. It
must reuse `Failure` and `ExecResult`; it must not introduce a parallel failure
carrier.

### P4-T01 — ranked continuation machine

Primary file: `STC/Core/Iterator.lean`. Use ADR-05's ranked continuation
architecture. A suitable stage shape is:

```lean
inductive StageResult (S E Q : Type u) where
  | halt (result : EffectResult S)
  | yield (result : EffectResult S) (next : Q)
  | raise (error : E)

structure RankedIterator (S E Q : Type u) where
  root : Q
  rank : Q → Nat
  run : Q → S → StageResult S E Q
  next_lt : ∀ {q s result q'},
    run q s = .yield result q' → rank q' < rank q
```

The exact certificate syntax may be refined for Lean ergonomics, but every
yielded continuation must have strictly smaller rank. `Q` and iterator code
remain external data; they do not enter the P2 state carrier and no
`State → State` closure is stored in a registry cell.

### P4-T02 — well-founded execution and prefix undo

Define execution by well-founded recursion on the rank certificate, not by an
unexplained arbitrary fuel bound and not by an unguarded coinductive loop. The
result is the existing `ExecResult`:

- `halt` returns the final state and the composition of successful-stage undos;
- `yield` executes the strictly smaller continuation and composes inverses in
  reverse execution order;
- `raise` returns the error, boundary, and undo for the successful prefix only.

If an earlier stage returns `u₁` and a later stage returns `u₂`, the accumulated
inverse is `u₁ ∘ u₂`, so `u₂` runs first. Prove a nontrivial prefix-recovery
theorem under explicit local recovery/properness hypotheses. Do not claim
arbitrary-order recovery or full lifecycle termination from rank alone.

On a `raise error`, the executor constructs `Failure error boundary prefixUndo`
from the current boundary and the successful-prefix undo. The stage itself
does not smuggle in a second boundary/undo carrier. If a partial operation is
used as a stage, its `Option.none` branch must be handled by an explicit
diagnostic policy before it becomes a `raise`.

### P4-T03 — relation, witness, and transport interfaces

Add relation-parametric `StageRelC`, `IteratorSimulation`, `IteratorBisim`,
`StageWitness`, and `IteratorWitness` interfaces (or documented equivalent
names) using P1's explicit relation vocabulary. Keep directional simulation
and converse/bisimulation statements separate. These interfaces must not
install a global `Setoid` or identify the distinct paper relations `≃`, `≈`,
support order, and control erasure. The same task must expose the
`IteratorInverseProper`/`StageInverseProper` hypotheses consumed by recovery,
plus an `execFrom_rel`-style directional execution-transport theorem using a
sum-of-ranks induction measure; equal ranks must not be assumed.

### P4-T04 — nested and failure transport tests

Primary file: `STC/Examples/VerticalSlice.lean`. Create the minimal P4
nested-iterator fixture without editing Bootstrap. This is another staged path:
P4 owns the iterator/failure transport checks; the later P7 owner extends it
after P6, with no concurrent edit. It evaluates:

1. a multi-stage successful iterator;
2. a nested continuation whose rank decreases at every yield;
3. a failing stage with a visibly retained prefix undo;
4. a finite Boolean/decidable negative check for an invalid/mixed result or
   rank condition (do not attempt to `#eval` an arbitrary malformed
   function-valued `RankedIterator` proof);
5. a relation/equality specialization where relevant.

### P4 gate

P4 is ready for handoff when the ranked carrier and strict-successor certificate
compile, execution is structurally well founded, canonical failure fields are
returned, LIFO/prefix recovery has checked theorem proofs (`K`), and finite
success/failure traces are evaluated (`E`). Do not claim `BD-CONTROL`,
`BD-STAGING`, `BD-SUPPORT`, or full lifecycle theorems.
The gate also requires the explicit inverse-properness and recovery witness
theorems, execution transport under directional simulation, and a T66 rank
bound such as `stageCountFrom_le`; these are not optional interface evidence.

## 6. Validation and evidence

Run focused checks after P3 and again after P4, using the repository's explicit
Lean options:

If P3-PREP creates `STC/Core/Generated.lean`, run the corresponding focused
check as well.

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Core/Partial.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Core/Iterator.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/TwoCounter.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/VerticalSlice.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
```

Every focused check and `lake build` must finish with zero errors and zero
warnings. The explicit `-D` options above are required even when the package
build succeeds.

The clean scanner result is exit `1`; preserve raw output at the integration
path. Classify evidence separately:

| Evidence | This workstream may earn | Does not establish |
|---|---|---|
| `A` | paper/ADR mapping and repair rationale | theorem truth |
| `I` | elaboration, acyclic imports, package build | semantic lawfulness |
| `K` | checked generic partial/iterator theorems | Cordis correspondence |
| `E` | finite evaluated traces/counterexamples | all abstract propositions |
| `R0` | none unless separately approved | runtime correctness |
| `R1+` | never in P3/P4 | — |

## 7. Handoff and stop rules

The agent must provide separate P3 and P4 handoff sections (or reports) with:

```text
task IDs and ownership
base/final commits and branch
changed files and public declarations
exact compiler/build/validator/scan outcomes
D17/L18 disposition
I versus K theorem inventory
finite E inputs and outputs
deferred rows and reasons
counterexamples and vacuity checks
confirmation that shared/frozen files were not modified
```

The AGENTS.md ledger rule still applies. Because `Definition-Ledger.json` and
the scan/report files are locked integration paths during the parallel work,
the implementation agent supplies the exact derived-row patch and raw scan
output in the handoff; the integration owner applies those changes after the
branch is reviewed. No ledger evidence is silently omitted or rewritten.

Stop and request review if:

- completing D17/L18 requires changing an accepted semantic decision;
- a failure/result carrier is redeclared or constructor tags/undo fields erased;
- iterator execution needs arbitrary fuel in place of the ranked certificate;
- a theorem silently assumes concrete coeffect/state/provider facts from P5;
- a proof uses an empty relation, impossible invariant, `sorry`, `admit`,
  unchecked project axiom, or `unsafe`;
- a baseline/hash or namespace mismatch appears outside the P0 option-2
  reconciliation.

Suggested commits are:

```text
p3: add partial operation and failure contracts
p3: add finite failure evidence
p4: add ranked iterator and prefix recovery
p4: add nested iterator evidence
```

The P5 workstream may merge independently. The user/integration owner performs
the cumulative Bootstrap, ledger, scan artifacts, and final merge review.
