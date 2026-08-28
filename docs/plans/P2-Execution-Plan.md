# STC Metatheory: P2 Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P2-EXEC-01` |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Prepared | 2026-08-28 |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Actual inspected P1 head | `7502f6e` (`origin/codex/p1-relation-result`, `codex/p1-relation-result`) |
| Actual inspected main | `02b50d2` (`origin/main`, `main`) |
| Required P2 branch | `codex/p2-effect-kernel`, created from exactly `7502f6e` |
| Namespace | `STC` |
| Scope | `P2-T01` through `P2-T04` |
| Status | ready for implementation under the explicit unmerged-P1 authorization below |

## 1. Objective and authorization ruling

P2 delivers a generic, shallow, reversible Effect kernel over an arbitrary state type
`S`. It reuses P1's canonical `EffectResult`, exposes the exact raw algebra separately
from relation-indexed correctness laws, proves lawful sequential composition and LIFO
recovery, supplies an equality specialization and finite executable fixtures, and reserves
only a type-parametric shallow/deep interpreter seam.

At planning time P1 is not merged into `main`: the current P1 production head is
`7502f6e`, while `origin/main` is `02b50d2`. The original orchestration brief treated that
as an implementation blocker. The user has explicitly superseded that workflow condition
for this run: **P2 may execute even though P1 is not merged**. This authorization changes
only the branch dependency policy; it does not relax any semantic, proof-integrity,
review, or merge gate.

The implementation branch therefore starts at exactly `7502f6e` and treats
`STC/Foundation/Relation.lean` and `STC/Foundation/Result.lean` at that commit as frozen
P1 dependencies. The final P2 PR must target `main`, state that it is stacked on P1, and
identify `7502f6e` as its logical review base while P1 remains unmerged. Reviewers should
review the P2 commit range `7502f6e..codex/p2-effect-kernel`. Once P1 merges, GitHub may
recompute the PR diff naturally; do not rewrite or merge unrelated branches merely to
make the diff smaller. Never automatically merge the P2 PR.

## 2. Authority, source anchors, and fixed interpretation

The repository authority model in `AGENTS.md` applies. Literal paper claims remain
distinct from repaired production targets; accepted ADRs govern the repairs; Lean checks
proof terms but does not establish source alignment by compilation alone.

| Source | P2 anchor | Binding consequence |
|---|---|---|
| `AGENTS.md` | authority model; paper fidelity; module boundaries; working loop | No hidden `WellFormed`, no concrete Cordis state, no placeholders, and no mutation of frozen artifacts. |
| Executable Blueprint §§1, 2, 4, 5/P2, 6, 8–10 | G4 shallow hybrid; A/I/K/E/R0 meanings; `Foundation → Core.Effect`; `P2-T01`–`P2-T04`; initial `Effect` sketch | Raw shallow execution first, explicit laws, finite tests, and an R0 seam only. |
| P1 plan §§3–6 and P1 handoff | P1-DEC-01; canonical relation/result ownership; P1 theorem and relator inventory | P2 imports P1 declarations and does not redeclare or edit them. |
| Current P1 production | `RelSpec`, `RespectsOn`, `Respects`, `PointwiseRel`, `CrossRel`, `EffectResult`, `EffectResultRel` | P2 law signatures use these exact meanings and names. |
| Formal Reference §§1–6 | D1–D16; right-to-left function composition; D8 repair; D9 operand convention; exact T15 statement; T16 LIFO | The selected inverse is the inverse returned by the actual run; local, not global, invertibility is sufficient. |
| Frozen H03 §3.1 | direct dependencies for D1–D16 | Ledger dependencies are not rewritten or inferred transitively. |
| Frozen H04 §3.1 | D1–D16 treatments and repairs | D8 and T15 use their approved logical repairs; frozen readiness remains unchanged. |
| ADR-01 §§5.1–5.6, 7, 9, 11 | raw exact layer; explicit `RelSpec`; canonical `IsLawfulEffect`; equality specialization; L38 manifest | Raw computation stays exact. Semantic laws expose `R`. No quotient carrier or global `Setoid`. |
| ADR-02 §§1, 5.5–5.6 | total Effect remains intact; partial effects and failure are separate | P2 has no `Option`/`Except` failure and performs no default totalization. |
| ADR-03 §§1, 5.1, 5.7, 10 | state is positive/data-only; action code is interpreted externally | The P2 code seam is external and generic; no `RawState`/registry closure is stored. |
| ADR-05 §§1, 3.3–3.4, 3.7 | iterator undo is `outer ∘ inner`; failure retains prefix undo; code stays external | P2's LIFO convention must be reusable unchanged by P4. P2 does not implement the iterator. |
| ADR-06 §§3–6, 8, 12 | canonical Pointwise/Cross orientation; three independent lawful fields; `seqRun_lawful`; equality iff; tracked bridge remains implementation work | ADR-06 corrects ADR-05's historical cross-input spelling. P2 uses `PointwiseRel` only for same-input map agreement. |
| `docs/status/Definition-Ledger.json` | current P1-derived delivery/evidence states | Only derived fields for actually delivered P2 rows may change; do not regenerate the ledger. |

Historical Lean spikes under
`docs/blueprint/architecture-decision/lean-spike/` may be inspected for provenance but
must never be imported, edited, or copied wholesale into production. The Markdown and
JSON ADR records supply the normative contracts.

## 3. Exact P2 scope

### P2-T01 — raw shallow Effect algebra

Implement in `STC/Core/Effect.lean`:

1. the D1 forward/undo transformation pair and twisted composition;
2. the D2 effect context, D3 tracking operation, and D6 recovery operation;
3. `Effect S := S → EffectResult S`, reusing P1's result carrier;
4. the identity effect and `seqRun first second` in programmer execution order;
5. exact computation/orientation lemmas for state and undo fields;
6. exact identity and associativity laws, and the uniform transformation-pair embedding;
7. the D12 shallow lift of an effect to its effect context, with exact T13–T15
   computation/projection lemmas required by the theorem minimum below.

### P2-T02 — explicit law records

Define `IsLawfulEffect R e` with exactly the three independent ADR-01/06 fields:

1. `run_respects`: related inputs produce `EffectResultRel R` results;
2. `undo_respects`: every inverse returned by an actual run preserves `R`;
3. `recovers`: that actual returned inverse maps that run's successor back to the run
   input modulo `R`.

An optional `LawfulEffect R` boundary bundle may pair a raw `Effect` with this predicate.
It must not replace the raw carrier or force proof fields into execution.

### P2-T03 — generic theorems and finite evidence

Prove:

- the identity effect is lawful;
- lawful effects are closed under `seqRun`;
- the composed undo is LIFO by an exact field equation;
- the composed inverse recovers the original input modulo the selected relation;
- a finite sequence of lawful effects is lawful and recovers in reverse execution order;
- the equality specialization is equivalent to the repaired, run-indexed D8 witness;
- the tracked/lifted exact and relational theorem family listed in Section 8;
- at least one nontrivial finite lawful effect and composition;
- at least one finite counterexample that rejects a missing law or wrong undo order.

### P2-T04 — shallow/deep seam only

Add a separate, type-parametric `STC/Core/EffectCode.lean` interface. `EffectCode` is a
type parameter supplied by a later language; P2 does not choose constructors. The seam
contains an interpreter signature and same-state shallow/deep agreement/refinement
contract phrased through `EffectResultRel`. It may contain a lawfulness-preservation
contract, but no automatic inhabitant is claimed.

This is `R0` interface evidence only. It is not a deep DSL, an evaluator for Cordis,
a cross-carrier simulation, or an R1+ theorem.

## 4. Explicit non-goals

P2 does not implement or claim completion of:

- D17/L18 generated transformation monoids or their leastness/closure theorems;
- D19/T20/C21 independence, selective removal, or arbitrary-order recovery;
- foreign-transformation selected-inverse stability from D19;
- partial operations, outcomes, `Option`/`Except`, failure, or totalization (P3);
- `StageResult`, ranked iterators, prefix failure, or iterator execution (P4);
- `StateLike`, `RegistryLike`, `RawState`, `ValidState`, `WellFormed`, provider tables,
  coeffect stores, lifecycle state, or P5 implementation;
- alpha actions or name-bearing transport (P6);
- the two-counter vertical slice, independence proof, or failing trace (P7);
- a concrete `EffectCode` datatype, compiler, optimizer, serialization, or deep DSL;
- concrete Cordis declarations, runtime closures, adapters, simulation, or R1+ evidence;
- a quotient execution carrier, a global `[Setoid S]`, or a giant predicate that hides
  the three law obligations;
- changes to P1's Relation/Result APIs, frozen H03/H04/Formal Reference, accepted ADRs,
  historical spikes, toolchain files, or unrelated branches.

P2 may mention deferred D17–C21 rows in the handoff, but it must not promote them merely
because D8–T16 compile.

## 5. Canonical orientations and semantic invariants

This section is normative for implementation and review.

### 5.1 Relation orientation

For a run `r := e input`, local recovery is always stated as:

```lean
R.rel (r.undo r.state) input
```

The restored/recovered state is the left endpoint and the original input is the right
endpoint. `RelSpec` is symmetric, but proofs and APIs must not silently reverse this
orientation. Equality specialization therefore reads `r.undo r.state = input`.

For `R.rel x y`, `run_respects` yields:

```lean
EffectResultRel R (e x) (e y)
```

which unfolds to related successors and:

```lean
PointwiseRel R (e x).undo (e y).undo
```

P1's `PointwiseRel` compares the two selected inverses at the same third argument. P1's
`CrossRel` compares outputs at related arguments and is only a derived proof tool. No P2
law field uses `CrossRel` as a substitute for same-input selected-inverse coherence or for
individual inverse properness.

### 5.2 Which “selected-inverse stability” P2 implements

P2's selected-inverse stability is **related-input coherence**: the `run_respects` field
requires related runs to return pointwise-related inverse functions. It is indexed by the
two actual run results and cannot be discharged by choosing another inverse.

This is distinct from D19's **foreign-transformation inverse stability**, which compares
the inverse selected at `h input` with the inverse selected at `input` for a transformation
`h` from another effect's generated monoid. ADR-01 explicitly says that D19 obligation is
not implied by `run_respects`, because `h input` need not be related to `input`. P2 must not
introduce a misleading `SelectedInverseStable` declaration that claims D19; that name and
contract remain downstream.

### 5.3 Undo properness is independent

`PointwiseRel R u v` does not imply `Respects R u` or `Respects R v` without additional
hypotheses. Each returned inverse therefore has its own `undo_respects` proof. Sequential
recovery uses this field for the earlier inverse after the later inverse recovers only
modulo `R`.

### 5.4 LIFO and operand convention

`seqRun first second` executes `first` and then `second`:

```lean
let rFirst := first input
let rSecond := second rFirst.state
{ state := rSecond.state
  undo := rFirst.undo ∘ rSecond.undo }
```

Applying the returned undo to the final state runs `rSecond.undo` first and
`rFirst.undo` second. This is LIFO. Reversing the stored composition to
`rSecond.undo ∘ rFirst.undo` is a semantic error even if a commutative toy happens to
pass.

The Formal Reference writes `(later ⋄ earlier)` with the **right operand executed first**.
Therefore:

```text
later ⋄ earlier  =  seqRun earlier later
```

For D1, `twisted later earlier` similarly executes `earlier.forward` before
`later.forward` and stores `earlier.undo ∘ later.undo`. The API and docstrings must name
operands (`first`/`second` or `later`/`earlier`) rather than relying on an unexplained
infix.

### 5.5 Immediate LIFO versus arbitrary removal

LIFO recovery needs only the local lawful-effect obligations: every inverse is applied at
the successor for which its local witness was returned, modulo properness. Independence is
needed only when an inverse crosses later foreign effects or executes out of LIFO order.
No P2 theorem may add independence to ordinary sequential recovery, and no P2 theorem may
claim arbitrary-order recovery without D19–C21.

### 5.6 Tracked lift and recovery target

For an effect run `e γ = (δ, g)`, forward projection `f := fun x => (e x).state`, and
accumulator `φ`, the lift follows the Formal Reference:

```text
liftEffect e (γ, φ)
  state = (δ, φ ∘ g)
  undo  = track (g, f)
```

Applying the lifted inverse computes the raw pair whose state is `g δ` and whose
accumulator is extensionally `φ ∘ g ∘ f`. Under local recovery the state returns only
modulo `R`; it is not globally exact unless `R` is equality. Preserving the recovery
target requires the explicit premise `Respects R φ`. The accumulator function itself is
not generally equal to `φ`. P2 must expose these as different theorems and must not hide a
global inverse premise in `IsLawfulEffect`.

## 6. Proposed files and ownership

| File | Owner | Work | Concurrent-edit rule |
|---|---|---|---|
| `STC/Core/Effect.lean` | single production API owner | D1–D16 raw definitions, law records, generic proofs | No other agent edits this file. All theorem-statement changes return to the API owner. |
| `STC/Core/EffectCode.lean` | same production API owner after `Effect.lean` API freeze | P2-T04 type-parametric seam | Must import `Core.Effect`; no reverse import. |
| `STC/Examples/Effect.lean` | example/test worker | finite positive, LIFO-order negative, selected-inverse-coherence negative, exact output report | May begin only after the public Effect API is frozen. |
| `STC/Bootstrap.lean` | integration/orchestration owner | import the two production files and example | Central file; no concurrent edits. |
| `docs/status/Definition-Ledger.json` | integration/orchestration owner | derived P2 evidence only | Central file; edit rows in place and never regenerate. |
| `docs/status/P2-scan-raw.txt` | integration/orchestration owner | exact final scanner stdout/stderr record | Create only at final integration. |
| `docs/status/P2-handoff-report.md` | integration/orchestration owner | final evidence and review handoff | Write after implementation and independent review stabilize. |

`STC.lean`, `lakefile.toml`, `lean-toolchain`, P1 Foundation modules, frozen inputs, and
accepted ADR files are not planned edits. If package discovery shows that a root import
must change beyond `STC/Bootstrap.lean`, stop and classify the reason before editing it.

Import direction:

```text
STC.Foundation.Relation
        ↓
STC.Foundation.Result
        ↓
STC.Core.Effect
        ↓
STC.Core.EffectCode

STC.Core.Effect ──> STC.Examples.Effect
all P2 modules ───> STC.Bootstrap
```

## 7. Declaration and API sketches

Names may receive a small syntactic adjustment during implementation, but the semantic
signatures and orientations are fixed. Any material signature change requires theorem
architecture review before code proceeds.

### 7.1 Raw transformation/tracking layer

```lean
structure Transformation (S : Type u) where
  forward : S → S
  undo : S → S

def Transformation.identity : Transformation S :=
  ⟨id, id⟩

-- `earlier` executes first, then `later`; later is the left paper operand.
def Transformation.twisted
    (later earlier : Transformation S) : Transformation S :=
  ⟨later.forward ∘ earlier.forward, earlier.undo ∘ later.undo⟩

abbrev EffectContext (S : Type u) := S × (S → S)

def track (t : Transformation S) : EffectContext S → EffectContext S :=
  fun ctx => (t.forward ctx.1, ctx.2 ∘ t.undo)

def recover : EffectContext S → EffectContext S :=
  fun ctx => (ctx.2 ctx.1, id)
```

The raw layer needs named projection and composition equations. If a `Monoid`
instance for `Transformation` would create instance ambiguity, explicit identity and
associativity theorems are sufficient; do not add an orphan instance merely to shorten a
statement.

### 7.2 Raw Effect layer

```lean
abbrev Effect (S : Type u) := S → EffectResult S

def identityEffect : Effect S :=
  fun state => { state := state, undo := id }

def seqRun (first second : Effect S) : Effect S :=
  fun input =>
    let rFirst := first input
    let rSecond := second rFirst.state
    { state := rSecond.state
      undo := rFirst.undo ∘ rSecond.undo }

def effectForward (e : Effect S) : S → S :=
  fun input => (e input).state

def uniformEffect (t : Transformation S) : Effect S :=
  fun input => { state := t.forward input, undo := t.undo }
```

No new `EffectResult` is declared. Field equations should be `[simp]` only when their
orientation is stable and cannot cause looping; use named computation theorems otherwise.

### 7.3 Law record and equality specialization

```lean
structure IsLawfulEffect (R : RelSpec S) (e : Effect S) : Prop where
  run_respects : RespectsOn R.rel (EffectResultRel R) e
  undo_respects : ∀ input, Respects R (e input).undo
  recovers : ∀ input, R.rel ((e input).undo (e input).state) input

structure LawfulEffect (R : RelSpec S) where
  run : Effect S
  lawful : IsLawfulEffect R run
```

The equality bridge should be one theorem, not a duplicate exact-law record:

```lean
theorem lawful_equality_iff (e : Effect S) :
    IsLawfulEffect (equality S) e ↔
      ∀ input, (e input).undo (e input).state = input
```

`run_respects` and `undo_respects` are automatic only after specializing to equality;
they remain explicit for a general `R`.

### 7.4 Finite sequencing

Use one unambiguous list execution order. Recommended:

```lean
def runSequence : List (Effect S) → Effect S
  | [] => identityEffect
  | first :: rest => seqRun first (runSequence rest)
```

The list head executes first. Its returned undo becomes the outermost function, so the
tail's undo runs before the head's undo. If implementation uses a fold instead, prove a
named equation showing it is extensionally this recursion before relying on it.

### 7.5 Effect-context lift

```lean
def liftEffect (e : Effect S) : Effect (EffectContext S) :=
  fun ctx =>
    let result := e ctx.1
    { state := (result.state, ctx.2 ∘ result.undo)
      undo := track
        { forward := result.undo
          undo := effectForward e } }
```

The final field name on the `Transformation` pair may make this code read as
`{ forward := result.undo, undo := effectForward e }`; document that the pair's second
map is the candidate inverse of the returned disposer. Do not assert it is globally an
inverse.

### 7.6 Shallow/deep seam

`EffectCode` is deliberately a parameter, not a new inductive language:

```lean
structure EffectInterpreter (EffectCode : Type u) (S : Type v) where
  interpret : EffectCode → Effect S

structure ShallowDeepRefinementSeam
    (R : RelSpec S)
    (interpreter : EffectInterpreter EffectCode S)
    (code : EffectCode)
    (shallow : Effect S) : Prop where
  run_related : ∀ input,
    EffectResultRel R (interpreter.interpret code input) (shallow input)

structure InterpreterLawful
    (R : RelSpec S)
    (interpreter : EffectInterpreter EffectCode S) : Prop where
  lawful : ∀ code, IsLawfulEffect R (interpreter.interpret code)
```

The exact orientation of `run_related` is interpreted-code result on the left and shallow
specification result on the right. Because `R` is an equivalence, this is observational
agreement, not a directed concrete-to-abstract simulation. A future heterogeneous or
directed runtime relation belongs in `STC.Adapter` and requires its own relation package;
P2 must not pretend this same-state seam is R1+ refinement.

## 8. Minimum theorem inventory

The implementation may choose idiomatic final names, but the handoff must map every
entry below to an actual declaration.

### 8.1 Raw exact algebra (`K` for checked equalities)

1. `Transformation.twisted_identity_left` and `_right`.
2. `Transformation.twisted_assoc`.
3. `track_state` (T4 projection).
4. `track_twisted` (T5 homomorphism with exact operand order).
5. `recover_state` and `recover_accumulator` (D6 equations).
6. `identityEffect_state` / `_undo`.
7. `seqRun_state` and `seqRun_undo`; `_undo` must expose
   `firstUndo ∘ secondUndo`.
8. `seqRun_identity_left`, `seqRun_identity_right`, and `seqRun_assoc` as extensional
   equality of raw effects.
9. `seqRun_uniformEffect`, matching paper D1 and D9 operand conventions.
10. `liftEffect_state_projection` and `liftEffect_undo_projection` (T14).
11. `liftEffect_seqRun` (T13).
12. `liftEffect_undo_apply` (T15 raw computation equation, without pretending local
    recovery is exact for general `R`).

### 8.2 Relation-law theorems

1. `identityEffect_lawful`.
2. `seqRun_lawful` (T11/D37 closure).
3. `seqRun_recovers` or a named projection of `seqRun_lawful.recovers` that makes the
   recovery chain and relation orientation visible.
4. `runSequence_lawful` under an explicit per-element lawfulness premise.
5. `runSequence_recovers`, giving generic finite LIFO recovery modulo `R` (T16).
6. `lawful_equality_iff`, the repaired D8 exact specialization.
7. `recover_track_rel` (T7) with explicit `Respects R accumulator` and local recovery
   premises; an exact corollary is obtained by `equality S`.
8. `liftEffect_recovers_state` (T15 relational state consequence).
9. `liftEffect_preserves_recovery_target` (T15 soundness consequence) with the explicit
   `Respects R φ` premise.
10. `liftEffect_lawful_equality_iff` or an equivalent globally quantified criterion:
    the lifted effect is exactly lawful iff every run-selected inverse composed with
    `effectForward e` is globally identity. The theorem must quantify over every input;
    it must not generalize one fixed returned inverse to all runs.

For items 7–10, if the exact statement needed for Lean reveals an extra hypothesis, the
API owner must return to the Formal Reference T15 text and ADR-01 §9. Do not silently put
the hypothesis into `IsLawfulEffect`, and do not weaken the theorem to a vacuous relation.

### 8.3 Proof architecture for `seqRun_lawful`

The proof should visibly follow the accepted law split:

- use the two `run_respects` premises to relate the two successor stages;
- relate composed selected inverses with P1's `compose_pointwiseRel`, using properness of
  the earlier selected inverse;
- prove composite undo properness with `respects_comp`;
- recover through the later inverse, transport that relation through the earlier inverse
  using `undo_respects`, then use the earlier `recovers` field and transitivity.

A proof that succeeds only because `R` is equality, the example relation is universal,
or the effects commute does not satisfy this theorem.

## 9. Executable and negative fixtures

Target: `STC/Examples/Effect.lean`.

### 9.1 Positive finite instance

Use a finite state with at least three values, such as `Fin 3`. Define a state-dependent
`setTo target` effect:

```text
input old ↦ state target, undo (constant old)
```

It is exact-lawful because the returned closure remembers the actual old state. Prove it
lawful at equality and, preferably, at a nontrivial finite equivalence partition. Compose
two different `setTo` effects and record the final state and recovered state. This tests a
genuinely run-selected inverse rather than a uniform global inverse.

The same report must also apply a nontrivial `Transformation.twisted`, `track`, `recover`,
and `liftEffect` result to concrete finite inputs. Record only observable finite values
(for example, apply an accumulated function to a chosen state); do not attempt to print
function closures. This gives executable coverage to D1–D3, D6, and D12 instead of
promoting those rows from compilation alone.

The fixture must execute a concrete report with `#eval` or `decide`, and a theorem must
pin the expected report value. Merely elaborating `IsLawfulEffect` earns I/K as
appropriate, not E.

### 9.2 Wrong-order LIFO negative

Choose input `0`, then run `setTo 1`, then `setTo 2`. With the closures selected by those
runs:

```text
correct: undo₁ (undo₂ final) = 0
wrong:   undo₂ (undo₁ final) = 1
```

Record both outputs. This prevents a commutative or identity-only fixture from masking a
reversed composition bug.

### 9.3 Selected-inverse-coherence negative

Use a finite equivalence with one nontrivial class `{0,1}` and a separate class `{2}`.
Construct a raw effect whose runs at related inputs `0` and `1`:

- have related successors;
- return inverses that each preserve the relation;
- locally recover their own input;
- but return inverse functions that are not `PointwiseRel` at argument `2`.

Prove or decide that the weak two-field package (individual properness plus local
recovery) holds while `run_respects`/`IsLawfulEffect` fails. This fixture is not admitted
as lawful. It demonstrates that selected-inverse coherence is independent and guards
against dropping the P2 `run_respects` field.

### 9.4 Optional simple recovery negative

If useful for diagnostics, add a raw effect with an incorrect undo and decide that its
local recovery proposition is false. This cannot replace the coherence counterexample or
the wrong-order LIFO fixture.

No negative proof may use an empty relation, an impossible input, an uninhabited state,
or a behavior-erasing observation.

## 10. Evidence plan

| Evidence | P2 deliverable | Acceptance boundary |
|---|---|---|
| `A` | This plan, source-to-declaration mapping, explicit D8/T15 repairs, orientation notes, non-goals, finite counterexamples, reviewer semantic audit | Does not prove Lean propositions. |
| `I` | `Core.Effect`, `Core.EffectCode`, examples, Bootstrap, and full package elaborate with the pinned toolchain | Does not by itself establish lawfulness. |
| `K` | The theorem inventory in Section 8 has checked, placeholder-free proof terms; law fields are discharged for concrete fixtures | Does not establish Cordis correspondence. |
| `E` | Finite report evaluates the exact final/recovered/wrong-order/coherence values and is pinned by a theorem | Does not replace the generic proofs. |
| `R0` | Generic `EffectCode` parameter, interpreter, same-state shallow/deep seam, and optional lawfulness contract compile | No concrete code language, adapter, simulation, or runtime theorem. |
| `R1+` | Not earned and must be recorded as such | Reserved for later concrete refinement. |

## 11. Definition Ledger changes

Edit rows in place only after their evidence exists. Do not run
`scripts/gen_definition_ledger.py`, do not change `depends_on` or any `h04_*` field, and
do not turn accepted ADR resolution into a mutation of frozen H04 readiness.

Expected promotions if the complete theorem minimum passes:

| Row | Expected delivery | Expected evidence | P2 note |
|---|---|---|---|
| D1, D2, D3, D6, D9, D12 | `completed` | `tested` | Raw exact definitions and tracked computations implemented and exercised by the required finite report; note exact declaration names. |
| T4, T5, T7, T10, T11, T13, T14, T15, T16 | `completed` | `proved` | Map each row to checked theorems; T15 note must distinguish raw equation, relational target, and global criterion. |
| D8 | `completed` | `proved` | Raw Effect plus non-vacuous, run-indexed `IsLawfulEffect` and equality iff. |
| D37 | `completed` | `proved` | Generic relation-parametric lawful-effect record and closure now supplied using P1 relators. No concrete P5 observation is claimed. |
| L38 | `in_progress` | `proved` | Notes must scope proof evidence to the D8/T7/T11/T15/T16 generic/Eq manifest; D17–C21 and concrete observation specializations remain, so delivery is not complete. |

Rows D17, L18, D19, T20, and C21 remain `planned/pending` unless a separately approved
scope change assigns and proves them. D33 remains a P5 observation task. D36 remains the
completed P1 relation foundation. P2's seam has no separate numbered paper row; record R0
in the P2 handoff rather than manufacturing a ledger ID.

Update top-level `plan_id` to `DH-P2-EXEC-01` and `generated_on` only as part of final
derived-status integration. The validator must pass after every ledger edit.

## 12. Dependency assumptions and downstream compatibility

### 12.1 Frozen P1 dependencies

P2 assumes exactly these P1 facts at `7502f6e`:

- `PointwiseRel` is same-input; `CrossRel` is related-input;
- `compose_pointwiseRel` has the current P1 signature;
- `EffectResult S` has fields `state : S` and `undo : S → S`;
- `EffectResultRel R` relates the state and same-input selected inverse;
- `equality S`, `respects_comp`, and the relation equivalence laws remain available.

No P2 worker edits either Foundation file. If a proof needs an additional reusable lemma
but not a signature change, first prove it privately in `Core.Effect`. Moving it into P1
Foundation still counts as a frozen-API change and requires the blocker procedure below.

### 12.2 P3 compatibility

P3 may import the total `Effect` and embed it into ADR-02's partial layer. It must preserve
the same success undo order and explicitly wrap total results in `some`. P2 must not add
failure or outcomes to `EffectResult`; doing so would blur P3's definedness and exact-tag
contracts. `IsLawfulEffect` field names and semantics should remain stable so P3's
lawfulness bridge can reuse them.

### 12.3 P4 compatibility

P4's one-stage/plain-effect embedding should call the P2 raw effect and return a `halt`.
For a current stage inverse `u` and recursive continuation inverse `inner`, P4 must produce
`u ∘ inner`, the same outer-after-inner/LIFO convention as `seqRun`. P4 owns failures and
prefix undo through P1's `ExecResult`; P2 must not create a second result carrier.

### 12.4 P7 compatibility

P7 counter effects should instantiate `IsLawfulEffect` and reuse `seqRun_lawful`, the
equality bridge, and list/LIFO theorems. P2's finite `setTo` fixture is not the P7
two-counter vertical slice. P7-T03 additionally needs D17–D19 independence/commutation
work not delivered by P2; the existence of P2 LIFO theorems does not discharge
independence or arbitrary-order removal.

### 12.5 P5 and adapter independence

P2 is generic over `S` and an explicit `RelSpec S`; no concrete state, registry, or P5
import is allowed. Later P5 observation profiles may instantiate `R` without changing the
P2 API. A concrete or heterogeneous runtime abstraction belongs in `STC.Adapter`, not in
`Core.EffectCode`.

## 13. Execution order and checkpoints

1. **Preflight and branch**
   - confirm detached/current head and refs;
   - create `codex/p2-effect-kernel` at exactly `7502f6e`;
   - verify a clean worktree and rerun the P1 baseline gates;
   - record the user's unmerged-P1 authorization in the handoff.
2. **API checkpoint — raw Effect**
   - implement D1–D9 raw definitions/equations;
   - run the single-file Core check;
   - review both operand conventions before continuing.
3. **Law checkpoint**
   - implement `IsLawfulEffect`, identity law, equality iff, and `seqRun_lawful`;
   - run the single-file check;
   - inspect theorem statements for all three independent fields.
4. **Tracked/lift checkpoint**
   - implement D12–T16 theorem family and finite sequence result;
   - run the Core check;
   - if T15 needs a new hypothesis, stop for theorem-architecture review.
5. **R0 checkpoint**
   - add the external, type-parametric EffectCode interpreter seam;
   - run its single-file check;
   - confirm there are no code constructors, concrete states, or runtime claims.
6. **Example checkpoint**
   - add finite positive and both required negative fixtures;
   - run the example and record exact `#eval` output.
7. **Integration checkpoint**
   - integration owner updates Bootstrap and the derived Ledger;
   - run full validation and preserve scanner output.
8. **Independent review**
   - dispatch a fresh Sol reviewer with no reliance on the implementer summary;
   - fix all `PASS_WITH_FIXES` findings, rerun validation, and obtain a fresh re-review.
9. **Handoff and PR**
   - write the P2 handoff, commit focused changes, push the P2 branch, and open/update a
     review-ready PR to `main` marked as stacked on P1 if necessary;
   - stop before merge.

Suggested focused commits:

```text
p2: add shallow effect algebra and laws
p2: prove tracked lift and lifo recovery
p2: reserve effect code refinement seam
p2: add finite effect and counterexample checks
p2: integrate bootstrap and derived evidence
p2: finalize reviewed handoff
```

Do not force this exact commit count if a proof checkpoint is cleaner as one focused
commit. Never combine unrelated P1 or other-wave changes.

## 14. Proof risks and escalation rules

| Risk | Required response |
|---|---|
| `PointwiseRel`/`CrossRel` conflation due to ADR-05 historical spelling | ADR-06 and current P1 API win. Rewrite the proof around same-input `PointwiseRel`; do not modify P1 names. |
| Undo composed in execution order instead of application/LIFO order | Check `seqRun_undo` and the noncommuting finite fixture before proving lawfulness. |
| Composition recovery stalls after later recovery modulo `R` | Use the earlier selected inverse's `undo_respects`; do not strengthen local recovery to equality. |
| Selected inverse coherence appears derivable from individual properness | Use the required finite counterexample; keep `run_respects` independent. |
| T15 accidentally claims the accumulator function returns exactly to `φ` | Split raw equation, state recovery, recovery-target preservation, and global criterion. Add `Respects R φ` only to the target theorem that needs it. |
| Equality specialization proof appears to require extra laws | For Eq, prove run/undo properness by substitution; the only semantic premise must be the repaired local witness. A failure here may indicate a signature defect. |
| Exact associativity is obstructed by function-valued result fields | Use `funext`/structure extensionality. Do not replace exact algebra by observational equality. |
| A theorem passes only on an indiscrete/empty relation or identity effect | Reject as non-evidence; test a nontrivial finite partition and state-dependent inverse. |
| Deep seam needs a heterogeneous or directed relation | Stop at the same-state R0 signature and defer the cross-carrier simulation to `STC.Adapter`; do not weaken `RelSpec`. |
| Need to store closures in future `RawState` or make code mention `RawState` | Stop; this violates ADR-03 lexical/positivity boundaries. |
| P1 API seems insufficient | Apply `BLOCKER-P2-P1-API`; do not patch Foundation. |

Routine Lean syntax, decidability, finite examples, and straightforward proof repair may
remain with the default implementation worker. Escalate theorem architecture immediately
when a theorem appears false, needs a new semantic hypothesis, crosses P2/P3/P4/P5, or
would alter an accepted ADR. The escalation response must be one of: a proof strategy, a
corrected reviewed theorem statement, a named missing hypothesis, a counterexample, or an
explicit blocker.

## 15. Stop conditions and blocker format

Stop dependent work and record a `BLOCKER-P2-*` finding if any of the following occurs:

- P1's frozen Relation/Result signature must change;
- `7502f6e` is not available or the checked P1 bytes differ from the recorded branch;
- a source/hash mismatch occurs outside the P0 provenance ruling;
- lawful sequential composition, equality specialization, or the result relation fails
  with exactly the ADR-01 obligations;
- T15/T16 requires a global inverse, independence, or hidden accumulator invariant not in
  the accepted source;
- the only proof uses a vacuous relation, impossible invariant, degenerate transition, or
  behavior-erasing observation;
- P2 would need partiality, iterator failure, concrete state/registry, alpha payload, deep
  DSL, or runtime semantics;
- the R0 seam would be described as a concrete simulation or R1+ result;
- a production scan finds a live placeholder, project axiom, or unsafe declaration;
- ledger validation or full build cannot be restored without changing frozen inputs;
- independent review returns `BLOCK`.

Each blocker report must contain:

```text
ID: BLOCKER-P2-<short-name>
source/theorem anchor:
minimal reproducer or failed signature:
why the current accepted contract is insufficient or false:
minimal proposed API/hypothesis change:
affected files and downstream P3/P4/P7 consequences:
counterexample or compiler output:
work stopped and safe work still completed:
required decision owner:
```

For a P1 API blocker, show the exact minimal Foundation signature change but do not apply
it. Stop every P2 theorem that depends on that change while preserving independently valid
work.

## 16. Validation commands and expected interpretation

### 16.1 Preflight

```bash
git status --short --branch
git log -1 --oneline --decorate
git rev-parse HEAD origin/main origin/codex/p1-relation-result
git diff --name-status origin/main..HEAD
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Relation.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Result.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
```

The scanner's clean result is exit code `1` with no live matches. Exit `0` requires match
inspection and classification; exit `2` is a scan error. A missing tool is a blocker, not
a successful gate.

### 16.2 Narrow P2 checks

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Core/Effect.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Core/EffectCode.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Effect.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
```

Record the exact output of the example file, including its evaluated report.

### 16.3 Final integration gate

```bash
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
git diff --check
git status --short --branch
git diff --stat 7502f6e..HEAD
git diff --name-status 7502f6e..HEAD
```

Preserve the final scanner output in `docs/status/P2-scan-raw.txt`. The final report must
include exit codes, not just prose such as “passed.” Compilation supplies I; only the
specific checked theorem proofs supply K.

Before final delivery, inspect the P2 diff for accidental edits to:

```text
STC/Foundation/Relation.lean
STC/Foundation/Result.lean
docs/blueprint/baseline/
docs/blueprint/architecture-decision/json/
docs/blueprint/architecture-decision/lean-spike/
```

Any such edit blocks P2 unless it is solely a separately approved blocker-resolution
change on a different branch.

## 17. Independent review gate

Use a fresh GPT-5.6 Sol context (or the closest available fresh high-reasoning context) as
a read-only reviewer after final validation. It must read the authoritative sources,
actual P1 files, P2 files, ledger, validation outputs, and full diff; it must not trust the
implementer's handoff summary.

The reviewer checks:

1. literal paper versus repaired ADR target is accurately recorded;
2. every theorem is non-vacuous and hypotheses are visible;
3. no hypothesis is hidden in a catch-all predicate;
4. `PointwiseRel` and `CrossRel` use the P1/ADR-06 orientations;
5. `seqRun first second` executes first then second and stores
   `first.undo ∘ second.undo`;
6. sequential recovery genuinely uses later recovery, earlier inverse properness, and
   earlier recovery;
7. related-input selected-inverse coherence is not confused with D19 foreign stability;
8. T15 separates exact computation, relational recovery target, and global criterion;
9. P3/P4/P7 can reuse the API without redefining result carriers or undo order;
10. no concrete state, registry, coeffect, provider, or Cordis dependency entered P2;
11. the EffectCode seam contains no unnecessary deep DSL and earns only R0;
12. finite positive and both required negative fixtures execute and observe relevant
    fields;
13. ledger promotions exactly match delivered evidence;
14. placeholder/unsafe scan and final diff are clean;
15. no R1+ or runtime-verification wording appears.

The verdict is exactly one of:

```text
PASS
PASS_WITH_FIXES
BLOCK
```

`PASS_WITH_FIXES` must include file/line, severity, source anchor, semantic consequence,
and required correction for every finding. Return those findings to the owning worker,
rerun all affected narrow and final gates, update the handoff, and obtain a fresh Sol
re-review. The orchestrator may not self-approve because `lake build` passes.

If exact model routing is unavailable, preserve a fresh context and role separation and
record the limitation in the P2 handoff.

## 18. Handoff and PR requirements

Create `docs/status/P2-handoff-report.md` containing:

1. plan/task IDs and owner assignment;
2. user authorization to proceed atop unmerged P1;
3. base `7502f6e`, branch, final commit, target `main`, and worktree status;
4. every changed file and confirmation that P1/frozen inputs were untouched;
5. public definition and theorem inventory mapped to D1–D16/D37/L38;
6. explicit relation and LIFO orientation;
7. A/I/K/E/R0/R1+ classification, with R1+ stated as not earned;
8. exact finite inputs and evaluated outputs;
9. negative counterexamples and what invalid inference each rejects;
10. deferred D17–C21, P3/P4/P5/P7, deep DSL, and runtime obligations;
11. blockers and failed proof attempts, even if resolved;
12. downstream assumptions for P3, P4, and P7;
13. exact per-file, build, ledger, scan, and diff-check outputs with exit codes;
14. independent reviewer identity/context separation, findings, fixes, and final verdict;
15. PR URL/number, stacked-P1 dependency note if still applicable, and remaining risks.

After a final `PASS`:

- commit only focused P2 files;
- show the exact staged file set before each commit;
- push `codex/p2-effect-kernel`;
- open or update a review-ready PR to `main`;
- state prominently that the P2 branch contains/depends on P1 through `7502f6e` until P1
  is merged;
- summarize remaining semantic and downstream risks;
- **stop before merge**.

No agent is authorized to merge the PR automatically.
