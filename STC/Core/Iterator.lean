module

public import STC.Core.Partial

/-!
# The ranked continuation iterator

The ADR-05 ranked continuation machine: an external control-code carrier `Q` with a
strict-successor rank certificate, execution by well-founded recursion on the rank
(no fuel, no coinductive loop), failure that retains the error, boundary state, and the
successful-prefix inverse, and the relation/witness interfaces of the ADR-06 contract.

## Main declarations

* `StageResult`, `RankedIterator`: the ranked continuation machine;
* `execFrom`: well-founded execution into `ExecResult`;
* `execFrom_halt`, `execFrom_raise`, `execFrom_yield_success`, `execFrom_yield_failure`;
* `execFrom_recovers`, `execFrom_success_recovers`, `execFrom_failure_recovers`: the
  generic prefix-recovery theorems (`K`);
* `stageCountFrom`, `stageCountFrom_le`: the ADR-05 stage bound;
* `StageRelC`, `IteratorSimulation`, `IteratorBisim`, `ContinuationStable`;
* `StageWitness`, `IteratorWitness`, `iteratorWitness_of_stageWitness`, `execFrom_rel`.
-/

universe u

namespace STC

variable {S : Type u} {E : Type u} {Q : Type u}

@[expose] public section

/-! ### The ranked continuation machine -/

section RankedMachine

/-- One iterator stage: halt with a successful result, yield with a state-dependent
continuation, or raise an error at the current boundary. -/
inductive StageResult (S E Q : Type u) where
  | halt (result : EffectResult S)
  | yield (result : EffectResult S) (next : Q)
  | raise (error : E)

/-- The ranked iterator: every yielded continuation has strictly smaller rank than its
predecessor.  `Q` is external control data and does not enter the state carrier. -/
structure RankedIterator (S E Q : Type u) where
  root : Q
  rank : Q → Nat
  run : Q → S → StageResult S E Q
  next_lt : ∀ {q s result q'}, run q s = .yield result q' → rank q' < rank q

/-- Execute a ranked iterator from a control code and input by well-founded recursion
on the rank certificate.  A `halt` returns the final result; a `yield` runs the strictly
smaller continuation and composes inverses in reverse execution order; a `raise` returns
the error, the boundary state, and the undo of the successful prefix only. -/
def execFrom (it : RankedIterator S E Q) (q : Q) (input : S) : ExecResult S E :=
  match _hrun : it.run q input with
  | .halt result => .success result
  | .raise error => .failure { error := error, boundary := input, prefixUndo := id }
  | .yield result next =>
      match execFrom it next result.state with
      | .success final =>
          .success { state := final.state, undo := result.undo ∘ final.undo }
      | .failure inner =>
          .failure ⟨inner.error, inner.boundary, result.undo ∘ inner.prefixUndo⟩
termination_by it.rank q
decreasing_by
  simp_wf
  exact it.next_lt _hrun

end RankedMachine

/-! ### Execution equations -/

section Execution

/-- A `halt` stage returns its result. -/
theorem execFrom_halt (it : RankedIterator S E Q) {q : Q} {input : S}
    {result : EffectResult S} (h : it.run q input = .halt result) :
    execFrom it q input = .success result := by
  unfold execFrom
  rw [h]

/-- A `raise` stage fails at the input boundary with the identity prefix undo. -/
theorem execFrom_raise (it : RankedIterator S E Q) {q : Q} {input : S} {error : E}
    (h : it.run q input = .raise error) :
    execFrom it q input =
      .failure { error := error, boundary := input, prefixUndo := id } := by
  unfold execFrom
  rw [h]

/-- A successful `yield` composes the stage inverse outside the continuation inverse,
so the continuation inverse applies first. -/
theorem execFrom_yield_success (it : RankedIterator S E Q) {q : Q} {input : S}
    {result : EffectResult S} {next : Q} {inner : EffectResult S}
    (hyield : it.run q input = .yield result next)
    (hinner : execFrom it next result.state = .success inner) :
    execFrom it q input =
      .success { state := inner.state, undo := result.undo ∘ inner.undo } := by
  unfold execFrom
  rw [hyield]
  simp only []
  rw [hinner]

/-- A failing `yield` retains the continuation failure and prepends the stage inverse
to the successful-prefix undo. -/
theorem execFrom_yield_failure (it : RankedIterator S E Q) {q : Q} {input : S}
    {result : EffectResult S} {next : Q} {f : Failure S E}
    (hyield : it.run q input = .yield result next)
    (hinner : execFrom it next result.state = .failure f) :
    execFrom it q input =
      .failure ⟨f.error, f.boundary, result.undo ∘ f.prefixUndo⟩ := by
  unfold execFrom
  rw [hyield]
  simp only []
  rw [hinner]

/-- Count the stages of a run, including the current stage. -/
def stageCountFrom (it : RankedIterator S E Q) (q : Q) (input : S) : Nat :=
  match _hrun : it.run q input with
  | .halt _ => 1
  | .raise _ => 1
  | .yield result next => 1 + stageCountFrom it next result.state
termination_by it.rank q
decreasing_by
  simp_wf
  exact it.next_lt _hrun

/-- Every run of a ranked iterator uses at most `rank q + 1` stages. -/
theorem stageCountFrom_le (it : RankedIterator S E Q) (q : Q) (input : S) :
    stageCountFrom it q input ≤ it.rank q + 1 := by
  let P : Nat → Prop := fun n => ∀ q input,
    it.rank q ≤ n → stageCountFrom it q input ≤ it.rank q + 1
  have hAll : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro q input hle
        cases hrun : it.run q input with
        | halt _ =>
            unfold stageCountFrom
            rw [hrun]
            simp only []
            omega
        | raise _ =>
            unfold stageCountFrom
            rw [hrun]
            simp only []
            omega
        | yield result next =>
            have hlt : it.rank next < it.rank q := it.next_lt hrun
            omega
    | succ n ih =>
        intro q input hle
        cases hrun : it.run q input with
        | halt _ =>
            unfold stageCountFrom
            rw [hrun]
            simp only []
            omega
        | raise _ =>
            unfold stageCountFrom
            rw [hrun]
            simp only []
            omega
        | yield result next =>
            unfold stageCountFrom
            rw [hrun]
            simp only []
            have hlt : it.rank next < it.rank q := it.next_lt hrun
            have hnext := ih next result.state (by omega)
            omega
  exact hAll (it.rank q) q input (Nat.le_refl (it.rank q))

end Execution

/-! ### Prefix recovery -/

section Recovery

/-- Every execution recovers its input up to the relation: successful runs through the
composed inverse, failing runs through the successful-prefix inverse at the boundary.
The only hypotheses are per-stage local recovery and inverse properness. -/
theorem execFrom_recovers (R : RelSpec S) (it : RankedIterator S E Q)
    (hstage : ∀ q input,
      match it.run q input with
      | .halt result => R.rel (result.undo result.state) input ∧ Respects R result.undo
      | .yield result _ => R.rel (result.undo result.state) input ∧ Respects R result.undo
      | .raise _ => True) :
    ∀ q input,
      match execFrom it q input with
      | .success final => R.rel (final.undo final.state) input
      | .failure f => R.rel (f.prefixUndo f.boundary) input := by
  intro q input
  let P : Nat → Prop := fun n => ∀ q input,
    it.rank q ≤ n →
      match execFrom it q input with
      | .success final => R.rel (final.undo final.state) input
      | .failure f => R.rel (f.prefixUndo f.boundary) input
  have hAll : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro q input hle
        cases hrun : it.run q input with
        | halt result =>
            unfold execFrom
            rw [hrun]
            have hs := hstage q input
            simp only [hrun] at hs
            exact hs.1
        | raise _ =>
            unfold execFrom
            rw [hrun]
            exact R.refl input
        | yield result next =>
            have hlt : it.rank next < it.rank q := it.next_lt hrun
            omega
    | succ n ih =>
        intro q input hle
        cases hrun : it.run q input with
        | halt result =>
            unfold execFrom
            rw [hrun]
            have hs := hstage q input
            simp only [hrun] at hs
            exact hs.1
        | raise _ =>
            unfold execFrom
            rw [hrun]
            exact R.refl input
        | yield result next =>
            unfold execFrom
            rw [hrun]
            simp only []
            have hs := hstage q input
            simp only [hrun] at hs
            have hlt : it.rank next < it.rank q := it.next_lt hrun
            cases hinner : execFrom it next result.state with
            | success inner =>
              have hrec := ih next result.state (by omega)
              have hinnerRec : R.rel (inner.undo inner.state) result.state := by
                simpa only [hinner] using hrec
              have hstep : R.rel (result.undo (inner.undo inner.state))
                  (result.undo result.state) := hs.2 hinnerRec
              simpa only [Function.comp_apply] using (R.trans hstep hs.1)
            | failure f =>
              have hrec := ih next result.state (by omega)
              have hinnerRec : R.rel (f.prefixUndo f.boundary) result.state := by
                simpa only [hinner] using hrec
              have hstep : R.rel (result.undo (f.prefixUndo f.boundary))
                  (result.undo result.state) := hs.2 hinnerRec
              simpa only [Function.comp_apply] using (R.trans hstep hs.1)
  exact hAll (it.rank q) q input (Nat.le_refl (it.rank q))

/-- The explicit recovery statement for successful runs. -/
theorem execFrom_success_recovers (R : RelSpec S) (it : RankedIterator S E Q)
    (hstage : ∀ q input,
      match it.run q input with
      | .halt result => R.rel (result.undo result.state) input ∧ Respects R result.undo
      | .yield result _ => R.rel (result.undo result.state) input ∧ Respects R result.undo
      | .raise _ => True) {q : Q} {input : S} {final : EffectResult S}
    (h : execFrom it q input = .success final) :
    R.rel (final.undo final.state) input := by
  have hrec := execFrom_recovers R it hstage q input
  simpa only [h] using hrec

/-- The explicit recovery statement for failing runs: the successful-prefix inverse
recovers the boundary state. -/
theorem execFrom_failure_recovers (R : RelSpec S) (it : RankedIterator S E Q)
    (hstage : ∀ q input,
      match it.run q input with
      | .halt result => R.rel (result.undo result.state) input ∧ Respects R result.undo
      | .yield result _ => R.rel (result.undo result.state) input ∧ Respects R result.undo
      | .raise _ => True) {q : Q} {input : S} {f : Failure S E}
    (h : execFrom it q input = .failure f) :
    R.rel (f.prefixUndo f.boundary) input := by
  have hrec := execFrom_recovers R it hstage q input
  simpa only [h] using hrec

end Recovery

/-! ### Relation and witness interfaces -/

section Interfaces

/-- The tagged stage relation: related payloads, equal continuations, and never-mixed
constructor tags. -/
def StageRelC (R : RelSpec S) (errorRel : E → E → Prop) :
    StageResult S E Q → StageResult S E Q → Prop
  | .halt left, .halt right => EffectResultRel R left right
  | .yield left leftNext, .yield right rightNext =>
      EffectResultRel R left right ∧ leftNext = rightNext
  | .raise leftError, .raise rightError => errorRel leftError rightError
  | _, _ => False

/-- A one-way simulation between two ranked iterators over the same control carrier:
stages on related inputs relate, and yielded continuations agree. -/
structure IteratorSimulation (R : RelSpec S) (T : RelSpec E)
    (left right : RankedIterator S E Q) : Prop where
  run_related : ∀ q s t, R.rel s t →
    StageRelC R T.rel (left.run q s) (right.run q t)

/-- A bisimulation is a simulation in both directions. -/
structure IteratorBisim (R : RelSpec S) (T : RelSpec E)
    (left right : RankedIterator S E Q) : Prop where
  forward : IteratorSimulation R T left right
  backward : IteratorSimulation R T right left

/-- Continuation stability: successful stages on related states yield equal
continuation codes. -/
def ContinuationStable (R : RelSpec S) (it : RankedIterator S E Q) : Prop :=
  ∀ {q s t r r' n n'}, R.rel s t →
    it.run q s = .yield r n → it.run q t = .yield r' n' → n = n'

/-- The per-stage witness package: every successful stage recovers locally and every
selected stage inverse preserves the relation. -/
structure StageWitness (R : RelSpec S) (it : RankedIterator S E Q) : Prop where
  stage : ∀ q input,
    match it.run q input with
    | .halt result => R.rel (result.undo result.state) input ∧ Respects R result.undo
    | .yield result _ => R.rel (result.undo result.state) input ∧ Respects R result.undo
    | .raise _ => True

/-- The iterator witness: the stage package plus the derived execution-level recovery
conclusions. -/
structure IteratorWitness (R : RelSpec S) (it : RankedIterator S E Q) : Prop where
  stage : StageWitness R it
  success_recovers : ∀ q input final, execFrom it q input = .success final →
    R.rel (final.undo final.state) input
  failure_recovers : ∀ q input f, execFrom it q input = .failure f →
    R.rel (f.prefixUndo f.boundary) input

/-- Every stage witness yields the full iterator witness: the execution-level recovery
conclusions are derived, not assumed. -/
theorem iteratorWitness_of_stageWitness (R : RelSpec S) (it : RankedIterator S E Q)
    (hw : StageWitness R it) : IteratorWitness R it where
  stage := hw
  success_recovers := by
    intro q input final h
    exact execFrom_success_recovers R it hw.stage h
  failure_recovers := by
    intro q input f h
    exact execFrom_failure_recovers R it hw.stage h

end Interfaces

/-! ### Relation transport -/

section RelationTransport

/-- Related iterators produce related executions: a simulation transports through
`execFrom` once the left iterator carries a stage witness. -/
theorem execFrom_rel (R : RelSpec S) (T : RelSpec E)
    (left right : RankedIterator S E Q)
    (hsim : IteratorSimulation R T left right)
    (hw : StageWitness R left) :
    ∀ q s t, R.rel s t →
      ExecRel R T.rel (execFrom left q s) (execFrom right q t) := by
  let P : Nat → Prop := fun n => ∀ q s t, R.rel s t → left.rank q ≤ n →
    ExecRel R T.rel (execFrom left q s) (execFrom right q t)
  have hAll : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro q s t hst hle
        cases hrunL : left.run q s with
        | halt resultL =>
          cases hrunR : right.run q t with
          | halt resultR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
            unfold execFrom
            rw [hrunL, hrunR]
            simpa only [ExecRel] using hrel
          | yield resultR nextR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | raise errorR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
        | raise errorL =>
          cases hrunR : right.run q t with
          | halt resultR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | yield resultR nextR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | raise errorR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
            unfold execFrom
            rw [hrunL, hrunR]
            simpa only [ExecRel, FailureRel] using
              (⟨hrel, hst, pointwiseRel_refl R id⟩ : FailureRel R T.rel
                { error := errorL, boundary := s, prefixUndo := id }
                { error := errorR, boundary := t, prefixUndo := id })
        | yield resultL nextL =>
          have hlt : left.rank nextL < left.rank q := left.next_lt hrunL
          omega
    | succ n ih =>
        intro q s t hst hle
        cases hrunL : left.run q s with
        | halt resultL =>
          cases hrunR : right.run q t with
          | halt resultR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
            unfold execFrom
            rw [hrunL, hrunR]
            simpa only [ExecRel] using hrel
          | yield resultR nextR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | raise errorR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
        | raise errorL =>
          cases hrunR : right.run q t with
          | halt resultR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | yield resultR nextR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | raise errorR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
            unfold execFrom
            rw [hrunL, hrunR]
            simpa only [ExecRel, FailureRel] using
              (⟨hrel, hst, pointwiseRel_refl R id⟩ : FailureRel R T.rel
                { error := errorL, boundary := s, prefixUndo := id }
                { error := errorR, boundary := t, prefixUndo := id })
        | yield resultL nextL =>
          cases hrunR : right.run q t with
          | halt resultR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
          | yield resultR nextR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
            have hpropL : Respects R resultL.undo := by
              have hs := hw.stage q s
              simp only [hrunL] at hs
              change ∀ {x y}, R.rel x y → R.rel (resultL.undo x) (resultL.undo y)
              exact hs.2
            have hlt : left.rank nextL < left.rank q := left.next_lt hrunL
            have hrec := ih nextL resultL.state resultR.state hrel.1.1 (by omega)
            have hrec' : ExecRel R T.rel (execFrom left nextL resultL.state)
                (execFrom right nextR resultR.state) := by
              simpa only [hrel.2] using hrec
            cases hinnerL : execFrom left nextL resultL.state with
            | success innerL =>
              cases hinnerR : execFrom right nextR resultR.state with
              | success innerR =>
                have hrelInner : EffectResultRel R innerL innerR := by
                  simpa only [ExecRel, hinnerL, hinnerR] using hrec'
                unfold execFrom
                rw [hrunL, hrunR]
                simp only []
                rw [hinnerL, hinnerR]
                simpa only [ExecRel, EffectResultRel] using
                  (⟨hrelInner.1, compose_pointwiseRel hpropL hrel.1.2 hrelInner.2⟩ :
                    R.rel innerL.state innerR.state ∧
                      PointwiseRel R (resultL.undo ∘ innerL.undo)
                        (resultR.undo ∘ innerR.undo))
              | failure _ =>
                have hfalse : False := by
                  simp only [ExecRel, hinnerL, hinnerR] at hrec'
                cases hfalse
            | failure innerFailure =>
              cases hinnerR : execFrom right nextR resultR.state with
              | success _ =>
                have hfalse : False := by
                  simp only [ExecRel, hinnerL, hinnerR] at hrec'
                cases hfalse
              | failure innerR =>
                have hrelInner : FailureRel R T.rel innerFailure innerR := by
                  simpa only [ExecRel, hinnerL, hinnerR] using hrec'
                unfold execFrom
                rw [hrunL, hrunR]
                simp only []
                rw [hinnerL, hinnerR]
                simpa only [ExecRel, FailureRel] using
                  (⟨hrelInner.1, hrelInner.2.1,
                    compose_pointwiseRel hpropL hrel.1.2 hrelInner.2.2⟩ :
                    T.rel innerFailure.error innerR.error ∧
                      R.rel innerFailure.boundary innerR.boundary ∧
                        PointwiseRel R (resultL.undo ∘ innerFailure.prefixUndo)
                          (resultR.undo ∘ innerR.prefixUndo))
          | raise errorR =>
            have hrel := hsim.run_related q s t hst
            simp only [StageRelC, hrunL, hrunR] at hrel
  intro q s t hst
  exact hAll (left.rank q) q s t hst (Nat.le_refl (left.rank q))

end RelationTransport

end

end STC
