module

public import STC.Control.Rules
public import STC.Examples.GlobalModel

/-!
# Global rule witnesses

The finite fixture inhabits every concrete constructor of the authoritative
rules: a linear trace over two acting fibers with a nonempty requirement and
provision, nested registration, async diversion (both branches admissible
under the A.async policy), and a real raise/cleanup path; plus the ADR-09
three-edge cycle-trace candidate (r = 0, c = 1, n = 2; former provider p = 3)
ending in the corrected cyclic support projection with an acyclic precedence
fragment and a well-formed endpoint.
-/

namespace STC.Examples.GlobalRules

open STC STC.State STC.Control

@[expose] public section

abbrev Cell := FiberCell Nat Nat Nat Unit Nat Nat Unit Unit
abbrev State := GlobalState Nat Nat Nat Unit Nat Nat Unit Unit Nat
abbrev Sem := ComponentSemantics State Nat Unit Nat Nat Unit Unit
abbrev OLabel := GlobalOrchestrationLabel Nat Cell
abbrev LLabel := GlobalLifecycleLabel Nat Nat State Nat Nat Unit Unit

/-! ### The external semantics -/

/-- The fixture's stage: a real yield/halt guarded by a positive ambient
counter, consuming one unit of ambient per executed stage; raising otherwise. -/
def fixtureStage (n : Nat) (state : State) : Option (State.StageResult State Nat Nat Unit) :=
  if _hpos : 0 < state.ambient then
    if _hn : n = 0 then some (.halt { state with ambient := state.ambient - 1 } (1 : Nat))
    else some (.yield { state with ambient := state.ambient - 1 } (1 : Nat) (n - 1))
  else some (.raise state ())

/-- The fixture's accumulator: adds the recorded inverse count to the ambient
counter. -/
def fixtureAccumulator (k : Nat) (state : State) : Option State :=
  some { state with ambient := state.ambient + k }

/-- The concrete external semantics instantiation. -/
def rulesSem : Sem :=
  { action := fun (_ : Unit) (state : State) => some state
    stage := fixtureStage
    composeInverse := fun (a b : Nat) => a + b
    identityAccumulator := 0
    accumulator := fixtureAccumulator
    launch := fun (_ : State) => some ()
    flight := fun (_ : Unit) (state : State) => some state
    failure := fun (_ : Unit) (state : State) => some state
    undo := fun (state : State) => some state
    observes := fun (_ _ : State) => True
    writesWithinProvision := fun (_ _ : State) => True
    continuationStable := fun (_ _ : State) => True
    rank := fun (state : State) => state.ambient
    accumulatorFrame := fun (_ : Nat) (_ _ : State) => True
    noWriteOutside := by intro code before after h; trivial
    action_frame := by intro code before after h; trivial
    stage_frame := by intro code before result h; trivial
    inverse_law := by intro code before after h; cases h; rfl
    stage_inverse := by
      intro code before result inverse hstage hinverse
      by_cases hpos : 0 < before.ambient
      · unfold fixtureStage at hstage
        rw [dif_pos hpos] at hstage
        by_cases hn : code = 0
        · rw [dif_pos hn] at hstage
          simp at hstage
          subst result
          cases hinverse
          unfold fixtureAccumulator
          simp [State.StageResult.state]
          rw [Nat.sub_add_cancel hpos]
        · rw [dif_neg hn] at hstage
          simp at hstage
          subst result
          cases hinverse
          unfold fixtureAccumulator
          simp [State.StageResult.state]
          rw [Nat.sub_add_cancel hpos]
      · unfold fixtureStage at hstage
        rw [dif_neg hpos] at hstage
        cases hstage
        simp [State.StageResult.inverse?] at hinverse
    relation_respect := by intro code left right left' right' hlr hl hr; trivial
    rank_law := by
      intro code before result hstage hnone
      by_cases hpos : 0 < before.ambient
      · unfold fixtureStage at hstage
        rw [dif_pos hpos] at hstage
        by_cases hn : code = 0
        · rw [dif_pos hn] at hstage
          simp at hstage
          subst result
          simp [hnone] at hnone
          simp [State.StageResult.state]
          omega
        · rw [dif_neg hn] at hstage
          simp at hstage
          subst result
          simp [hnone] at hnone
          simp [State.StageResult.state]
          omega
      · unfold fixtureStage at hstage
        rw [dif_neg hpos] at hstage
        cases hstage
        simp [State.StageResult.failure?] at hnone
    continuation_stable := by intro code before after h; trivial
    flight_frame := by intro code before after h; trivial
    failure_frame := by intro code before after h; trivial
    composeInverse_law := by
      intro a b before mid after hb ha
      unfold fixtureAccumulator at hb ha
      simp at hb ha
      subst mid
      subst after
      unfold fixtureAccumulator
      simp
      grind only
    identityAccumulator_law := by
      intro state
      unfold fixtureAccumulator
      grind only
    accumulator_frame := by intro code before after h; trivial }

abbrev model := globalControlModel rulesSem

/-! ### Main fixture: cells and states -/

abbrev coeffects0 : Finmap (fun _ : Nat => Nat) :=
  Finmap.insert 10 (0 : Nat) (Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)))

abbrev s0 : State :=
  { ambient := 10, registry := ∅, coeffects := coeffects0,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

abbrev cell1 : Cell :=
  { incarnation := 1, parent := none, birth := 0,
    component := { key := 1, requires := ∅, provides := {10}, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cell2 : Cell :=
  { incarnation := 2, parent := some 1, birth := 1,
    component := { key := 2, requires := {10}, provides := {20}, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cell3 : Cell :=
  { incarnation := 3, parent := none, birth := 2,
    component := { key := 3, requires := {10}, provides := ∅, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cell4 : Cell :=
  { incarnation := 4, parent := none, birth := 3,
    component := { key := 4, requires := {10}, provides := ∅, actionCode := (), iteratorCode := 0, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev s1 : State := allocate s0 1 cell1
abbrev s2 : State := beginState rulesSem s1 1 ∅ ()
abbrev s3 : State := iterState rulesSem { s2 with ambient := 9 } 1 1 0
abbrev s4 : State := finishState { s3 with ambient := 8 } 1
abbrev s5 : State := allocate s4 2 cell2
abbrev s6 : State := beginState rulesSem s5 2 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) ()
abbrev s7 : State := iterState rulesSem { s6 with ambient := 7 } 2 1 0
abbrev s8 : State := retireState s7 2
abbrev s9 : State := allocate s8 3 cell3
abbrev s10 : State := beginState rulesSem s9 3 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) ()
abbrev s11 : State := allocate s10 4 cell4
abbrev s12 : State := beginState rulesSem s11 4 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) ()
abbrev s13 : State := finishState { s12 with ambient := 6 } 4
abbrev s14 : State := retireState s13 1
abbrev s15 : State := raiseState s14 1 ()
abbrev s16 : State := divertAbortState s15 3
abbrev s17 : State := unloadState s16 3
abbrev s18 : State := retireState s17 3
abbrev s19 : State := removeState s18 3
abbrev s20 : State := divertLandState rulesSem s19 2 1
abbrev s21 : State := unloadState { s20 with ambient := s20.ambient + 2 } 2
abbrev s22 : State := leaveState s21 4
abbrev s23 : State := unloadState s22 4
abbrev s24 : State := unloadState { s23 with ambient := s23.ambient + 1 } 1

/-! ### Per-state cell facts -/

theorem lookup_s1_1 : Finmap.lookup 1 s1.registry = some cell1 := by
  congr

theorem lookup_s2_1 : Finmap.lookup 1 s2.registry = some { cell1 with phase := .reloading, committedView := ∅, payload := { cell1.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } } := by
  congr

theorem lookup_s3_1 : Finmap.lookup 1 s3.registry = some { cell1 with phase := .reloading, committedView := ∅, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } } := by
  congr

theorem lookup_s4_1 : Finmap.lookup 1 s4.registry = some { cell1 with phase := .active, committedView := ∅, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } } := by
  congr

theorem lookup_s4_2_none : Finmap.lookup 2 s4.registry = none := by
  congr

theorem lookup_s5_2 : Finmap.lookup 2 s5.registry = some cell2 := by
  congr

theorem lookup_s6_2 : Finmap.lookup 2 s6.registry = some { cell2 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell2.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } } := by
  congr

theorem lookup_s7_2 : Finmap.lookup 2 s7.registry = some { cell2 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell2.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } } := by
  congr

theorem lookup_s8_2 : Finmap.lookup 2 s8.registry = some { cell2 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), retired := true, payload := { cell2.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } } := by
  congr

theorem lookup_s15_1 : Finmap.lookup 1 s15.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem lookup_s6_1 : Finmap.lookup 1 s6.registry = some { cell1 with phase := .active, committedView := ∅, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } } := by
  congr

theorem providesNow_s6 : ProvidesNow s6 1 10 := by
  refine ⟨_, lookup_s6_1, ?_, rfl⟩
  decide

/-! ### The main trace witnesses -/

theorem step_insert1 : OrchestrationRule (.insert none 1 cell1) s0 s1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 1) (child := cell1)
    (by decide) (by decide) (⟨by decide, by decide⟩) (by intro name cell' h; simp at h)

theorem step_begin1 : LifecycleRule rulesSem (.begin 1 ∅ ()) s1 s2 := by
  exact LifecycleRule.begin (sem := rulesSem) (hlook := rfl) (hphase := rfl) (hretired := rfl)
    (hlaunch := rfl) (htarget := ⟨cell1, rfl, rfl, by intro _ _ hkv; cases hkv⟩)

theorem step_iter1 : LifecycleRule rulesSem (.iter 1 0 1 { s2 with ambient := 9 }) s2 s3 := by
  exact LifecycleRule.iter (sem := rulesSem) (hlook := lookup_s2_1)
    (hphase := rfl)
    (htarget := by
      refine ⟨_, lookup_s2_1, ?_, ?_⟩
      · decide
      · intro key provider hkv
        change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv)
    (hstage := rfl)
    (hrank := by decide)

theorem step_finish1 : LifecycleRule rulesSem (.finish 1 { s3 with ambient := 8 }) s3 s4 := by
  exact LifecycleRule.finish (sem := rulesSem) (hlook := lookup_s3_1)
    (hphase := rfl)
    (htarget := by
      refine ⟨_, lookup_s3_1, ?_, ?_⟩
      · simp [Finmap.keys_empty]
      · intro key provider hkv
        change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv)
    (hstage := by
      change fixtureStage 0 s3 = some (.halt { s3 with ambient := 8 } 1)
      unfold fixtureStage
      simp [s3, s2, s1, iterState, beginState, editCell, updateFiber, allocate, iterPayload,
        beginPayload, rulesSem, cell1])

theorem providesNow_s4 : ProvidesNow s4 1 10 :=
  ⟨_, lookup_s4_1, by
    change 10 ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys
    rw [Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem s4_history : s4.allocationHistory = [1] := by
  congr

theorem step_insert2 : OrchestrationRule (.insert (some 1) 2 cell2) s4 s5 := by
  exact OrchestrationRule.insert (registrar := some 1) (fresh := 2) (child := cell2)
    (by simp [finishState, iterState, beginState, editCell, updateFiber, allocate])
    (by simp [finishState, iterState, beginState, editCell, updateFiber, allocate])
    (by
      simp [CanonicalInitialCell, Registered, finishState, iterState, beginState, editCell,
        updateFiber, allocate, Finmap.lookup_insert]; decide)
    (by intro name cell' h
        simp [finishState, iterState, beginState, editCell, updateFiber, allocate] at h
        by_cases hname : name = 1
        · subst name
          have hcell' : cell' = { cell1 with phase := .active, committedView := ∅, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } } := by
            simpa [finishState, iterState, beginState, editCell, updateFiber, allocate,
              iterPayload, beginPayload, rulesSem, cell1, Finmap.lookup_insert] using h.symm
          subst cell'
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
          subst key
          simp
        · rw [Finmap.lookup_insert_of_ne (a := 1) (a' := name) (s := s0.registry) hname,
            Finmap.lookup_empty] at h
          cases h)

theorem targetViewAt_s5_2 : TargetViewAt s5 2 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) := by
  refine ⟨cell2, lookup_s5_2, ?_, ?_⟩
  · change (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))).keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s4
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem step_begin2 : LifecycleRule rulesSem
    (.begin 2 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) ()) s5 s6 := by
  exact LifecycleRule.begin (sem := rulesSem) (hlook := lookup_s5_2) (hphase := rfl)
    (hretired := rfl) (htarget := targetViewAt_s5_2) (hlaunch := rfl)

theorem targetViewAt_s6_2 : TargetViewAt s6 2 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) := by
  refine ⟨_, lookup_s6_2, ?_, ?_⟩
  · change (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))).keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s4
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem step_iter2 : LifecycleRule rulesSem (.iter 2 0 1 { s6 with ambient := 7 }) s6 s7 := by
  exact LifecycleRule.iter (sem := rulesSem) (hlook := lookup_s6_2) (hphase := rfl)
    (htarget := targetViewAt_s6_2) (hstage := rfl) (hrank := by decide)

abbrev cell2reloading : Cell := { cell2 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell2.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } }

theorem step_retire2 : OrchestrationRule (.retire 2 cell2reloading) s7 s8 := by
  exact OrchestrationRule.retire lookup_s7_2

theorem step_insert3 : OrchestrationRule (.insert none 3 cell3) s8 s9 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 3) (child := cell3)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, s8, s7, s6, s5, s4, s3, s2, s1,
        retireState, iterState, beginState, finishState, editCell, updateFiber, allocate,
        iterPayload, beginPayload, rulesSem, cell1, cell2, Finmap.lookup_insert]
      decide)
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem targetViewAt_s9_3 : TargetViewAt s9 3 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) := by
  refine ⟨cell3, by simp [s9, s8, allocate], ?_, ?_⟩
  · change (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))).keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s4
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem step_begin3 : LifecycleRule rulesSem
    (.begin 3 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) ()) s9 s10 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell3)
    (hlook := by simp [s9, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl) (htarget := targetViewAt_s9_3) (hlaunch := by rfl)

theorem step_insert4 : OrchestrationRule (.insert none 4 cell4) s10 s11 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 4) (child := cell4)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        retireState, iterState, beginState, finishState, editCell, updateFiber, allocate,
        iterPayload, beginPayload, rulesSem, cell1, cell2, cell3, Finmap.lookup_insert]
      decide)
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin4 : LifecycleRule rulesSem
    (.begin 4 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) ()) s11 s12 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell4)
    (hlook := by simp [s11, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl)
    (htarget := by
      refine ⟨cell4, by simp [s11, allocate, Finmap.lookup_insert], ?_, ?_⟩
      · change (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))).keys = {10}
        apply Finset.ext
        intro key
        rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
        change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
        by_cases hkey : key = 10 <;> simp [hkey]
      · intro key provider hkv
        change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
        by_cases hkey : key = 10
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have hp : provider = 1 := (Option.some.inj hkv).symm
          subst provider
          exact providesNow_s4
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
            Finmap.lookup_empty] at hkv
          cases hkv)
    (hlaunch := by rfl)

abbrev cell4reloading : Cell := { cell4 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell4.payload with iteratorCode := 0, accumulatorCode := 0, flightCode := some () } }

theorem step_finish4 : LifecycleRule rulesSem (.finish 4 { s12 with ambient := 6 }) s12 s13 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell4reloading)
    (hlook := by congr)
    (hphase := rfl)
    (htarget := by
      refine ⟨cell4reloading, by congr, ?_, ?_⟩
      · change (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))).keys = {10}
        apply Finset.ext
        intro key
        rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
        change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
        by_cases hkey : key = 10 <;> simp [hkey]
      · intro key provider hkv
        change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
        by_cases hkey : key = 10
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have hp : provider = 1 := (Option.some.inj hkv).symm
          subst provider
          exact providesNow_s4
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
            Finmap.lookup_empty] at hkv
          cases hkv)
    (hstage := rfl)

abbrev cell1active : Cell := { cell1 with phase := .active, committedView := ∅, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some () } }

theorem step_retire1 : OrchestrationRule (.retire 1 cell1active) s13 s14 := by
  exact OrchestrationRule.retire (by congr)

abbrev cell1retired : Cell := { cell1active with retired := true }

theorem step_raise1 : LifecycleRule rulesSem (.raise 1 ()) s14 s15 := by
  exact LifecycleRule.raise (sem := rulesSem) (cell := cell1retired) (hlook := by congr)
    (hphase := by right; rfl) (hreal := rfl)

abbrev cell3reloading : Cell := { cell3 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell3.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }
abbrev cell4active : Cell := { cell4reloading with phase := .active }

theorem lookup_s15_2 : Finmap.lookup 2 s15.registry = some { cell2reloading with retired := true } := by
  congr

theorem lookup_s15_3 : Finmap.lookup 3 s15.registry = some cell3reloading := by
  congr

theorem lookup_s15_4 : Finmap.lookup 4 s15.registry = some cell4active := by
  congr

theorem noProvides10_s15 : ∀ p, ¬ ProvidesNow s15 p 10 := by
  intro p h
  rcases h with ⟨cell, hlook, htable, hphase⟩
  by_cases hp1 : p = 1
  · subst p
    rw [lookup_s15_1] at hlook
    cases hlook with | refl
    simp at hphase
  · by_cases hp2 : p = 2
    · subst p
      rw [lookup_s15_2] at hlook
      cases hlook with | refl
      simp at hphase
    · by_cases hp3 : p = 3
      · subst p
        rw [lookup_s15_3] at hlook
        cases hlook with | refl
        simp at hphase
      · by_cases hp4 : p = 4
        · subst p
          rw [lookup_s15_4] at hlook
          cases hlook with | refl
          simp at htable
        · have hmem : p ∈ s15.registry.keys := by
            rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
            rw [hlook]
            rfl
          simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
            raiseState, retireState, finishState, beginState, iterState, editCell, updateFiber,
            allocate, iterPayload, beginPayload, rulesSem, Finmap.lookup_insert,
            Finmap.mem_keys, Finmap.mem_insert] at hmem
          rcases hmem with h1' | h4' | h3' | h2' | h1'' | hempty
          · omega
          · omega
          · omega
          · omega
          · omega
          · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
            simp at hempty

theorem targetAbsent_s15_3 : TargetAbsent s15 3 := by
  intro ω h
  rcases h with ⟨cell, hlook, hkeys, hall⟩
  rw [lookup_s15_3] at hlook
  cases hlook with | refl
  have hmem : 10 ∈ ω.keys := by
    rw [hkeys]
    simp
  have hisome : (Finmap.lookup 10 ω).isSome := by
    rw [Finmap.lookup_isSome, ← Finmap.mem_keys]
    exact hmem
  cases hlook10 : Finmap.lookup 10 ω with
  | none => simp [hlook10] at hisome
  | some provider =>
      have hprov : ProvidesNow s15 provider 10 := hall 10 provider hlook10
      exact noProvides10_s15 provider hprov

theorem step_divertAbort3 : LifecycleRule rulesSem (.divertAbort 3 .absent) s15 s16 := by
  exact LifecycleRule.divertAbort (sem := rulesSem) (cell := cell3reloading)
    (hlook := by congr) (hphase := rfl) (hboundary := targetAbsent_s15_3)

abbrev cell3unloading : Cell := { cell3reloading with phase := .unloading }

theorem lookup_s16_2 : Finmap.lookup 2 s16.registry = some { cell2reloading with retired := true } := by
  congr

theorem lookup_s16_3 : Finmap.lookup 3 s16.registry = some cell3unloading := by
  congr

theorem lookup_s16_4 : Finmap.lookup 4 s16.registry = some cell4active := by
  congr

theorem lookup_s16_1 : Finmap.lookup 1 s16.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem s16_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent s16.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)) := by
  intro hlook
  have hmem : dependent ∈ s16.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
    rw [hlook]
    rfl
  simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
    divertAbortState, raiseState, retireState, finishState, beginState, iterState,
    editCell, updateFiber, allocate, iterPayload, beginPayload, rulesSem,
    Finmap.lookup_insert, Finmap.mem_keys, Finmap.mem_insert] at hmem
  rcases hmem with h3 | h1 | h4 | h3' | h2 | h1'
  · subst dependent
    rw [lookup_s16_3] at hlook
    cases hlook with | refl
    right; rfl
  · subst dependent
    rw [lookup_s16_1] at hlook
    cases hlook with | refl
    left; rfl
  · subst dependent
    rw [lookup_s16_4] at hlook
    cases hlook with | refl
    right; rfl
  · subst dependent
    rw [lookup_s16_3] at hlook
    cases hlook with | refl
    right; rfl
  · subst dependent
    rw [lookup_s16_2] at hlook
    cases hlook with | refl
    right; rfl
  · rcases h1' with h | hempty
    · subst dependent
      rw [lookup_s16_1] at hlook
      cases hlook with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

theorem step_unload3 : LifecycleRule rulesSem (.unload 3 s16) s16 s17 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell3unloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases s16_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 10
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h13 : (1 : Nat) = 3 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem step_retire3 : OrchestrationRule (.retire 3 cell3) s17 s18 := by
  exact OrchestrationRule.retire (by congr)

abbrev cell3retired : Cell := { cell3 with retired := true }

theorem lookup_s17_3 : Finmap.lookup 3 s17.registry = some cell3 := by
  congr

theorem lookup_s18_3 : Finmap.lookup 3 s18.registry = some cell3retired := by
  congr

theorem lookup_s18_1 : Finmap.lookup 1 s18.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem lookup_s18_4 : Finmap.lookup 4 s18.registry = some cell4active := by
  congr

theorem lookup_s18_2 : Finmap.lookup 2 s18.registry = some { cell2reloading with retired := true } := by
  congr

theorem step_remove3 : OrchestrationRule (.remove 3) s18 s19 := by
  exact OrchestrationRule.remove (cell := cell3retired) (hlook := by congr)
    (hretired := rfl) (hphase := by left; rfl) (hnoChild := by
      intro name cell' h hparent
      have hmem : name ∈ s18.registry.keys := by
        rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
        rw [h]
        rfl
      simp [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2,
        s1, retireState, unloadState, divertAbortState, raiseState, finishState,
        beginState, iterState, editCell, updateFiber, allocate, iterPayload, beginPayload,
        rulesSem, Finmap.lookup_insert, Finmap.mem_keys, Finmap.mem_insert] at hmem
      rcases hmem with h18 | h1a | h4 | h3 | h2 | htail
      · subst name
        rw [lookup_s18_3] at h
        cases h with | refl
        cases hparent
      · subst name
        rw [lookup_s18_1] at h
        cases h with | refl
        cases hparent
      · subst name
        rw [lookup_s18_4] at h
        cases h with | refl
        cases hparent
      · subst name
        rw [lookup_s18_3] at h
        cases h with | refl
        cases hparent
      · subst name
        rw [lookup_s18_2] at h
        cases h with | refl
        cases hparent
      · rcases htail with h | hempty
        · subst name
          rw [lookup_s18_1] at h
          cases h with | refl
          cases hparent
        · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
          simp at hempty)

theorem lookup_s19_1 : Finmap.lookup 1 s19.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem targetNot_s19_2 : ¬ TargetViewAt s19 2 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) := by
  intro h
  rcases h with ⟨cell, hlook, _hkeys, hall⟩
  have hprov : ProvidesNow s19 1 10 := hall 10 1 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_s19_1] at hlook'
  cases hlook' with | refl
  simp at hphase

abbrev cell2retired : Cell := { cell2reloading with retired := true }

theorem step_divertLand2 : LifecycleRule rulesSem (.divertLand 2 () 1 s19) s19 s20 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cell2retired)
    (hlook := by congr) (hphase := rfl) (hchanged := targetNot_s19_2) (hland := rfl)

abbrev cell2unloading : Cell := { cell2retired with phase := .unloading, payload := { cell2retired.payload with accumulatorCode := 2 } }

theorem lookup_s20_1 : Finmap.lookup 1 s20.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem lookup_s20_4 : Finmap.lookup 4 s20.registry = some cell4active := by
  congr

theorem lookup_s20_2 : Finmap.lookup 2 s20.registry = some cell2unloading := by
  congr

theorem s20_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent s20.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)) := by
  intro hlook
  by_cases hd2 : dependent = 2
  · subst dependent
    rw [lookup_s20_2] at hlook
    cases hlook with | refl
    right; rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_s20_1] at hlook
      cases hlook with | refl
      left; rfl
    · by_cases hd4 : dependent = 4
      · subst dependent
        rw [lookup_s20_4] at hlook
        cases hlook with | refl
        right; rfl
      · have hnone : Finmap.lookup dependent s20.registry = none := by
          by_cases hd3 : dependent = 3
          · subst dependent
            simp [s20, s19, s18, divertLandState, removeState, editCell, updateFiber,
              lookup_s18_2, Finmap.lookup_insert_of_ne, hd2]
          · simp [s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6,
              s5, s4, s3, s2, s1, divertLandState, removeState, retireState, unloadState,
              divertAbortState, raiseState, finishState, beginState, iterState, editCell,
              updateFiber, allocate, iterPayload, beginPayload, rulesSem,
              Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty,
              hd2, hd1, hd4, hd3]
        rw [hnone] at hlook
        cases hlook

theorem step_unload2 : LifecycleRule rulesSem (.unload 2 { s20 with ambient := s20.ambient + 2 }) s20 s21 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell2unloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases s20_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 10
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h12 : (1 : Nat) = 2 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_s21_4 : Finmap.lookup 4 s21.registry = some cell4active := by
  congr

theorem lookup_s21_1 : Finmap.lookup 1 s21.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem targetNot_s21_4 : ¬ TargetViewAt s21 4 (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) := by
  intro h
  rcases h with ⟨cell, hlook, _hkeys, hall⟩
  have hprov : ProvidesNow s21 1 10 := hall 10 1 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_s21_1] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem step_leave4 : LifecycleRule rulesSem (.leave 4) s21 s22 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cell4active) (hlook := by congr)
    (hphase := rfl) (hchanged := targetNot_s21_4)

abbrev cell4unloading : Cell := { cell4active with phase := .unloading }
abbrev cell2inactive : Cell := { cell2unloading with phase := .inactive, committedView := ∅, payload := { cell2unloading.payload with flightCode := none } }

theorem lookup_s9_3 : Finmap.lookup 3 s9.registry = some cell3 := by
  congr

theorem lookup_s11_4 : Finmap.lookup 4 s11.registry = some cell4 := by
  congr

theorem lookup_s12_4 : Finmap.lookup 4 s12.registry = some cell4reloading := by
  congr

theorem lookup_s14_1 : Finmap.lookup 1 s14.registry = some cell1retired := by
  congr

theorem lookup_s19_2 : Finmap.lookup 2 s19.registry = some cell2retired := by
  congr

theorem lookup_s22_1 : Finmap.lookup 1 s22.registry = some { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } } := by
  congr

theorem lookup_s22_2 : Finmap.lookup 2 s22.registry = some cell2inactive := by
  congr

theorem lookup_s22_4 : Finmap.lookup 4 s22.registry = some cell4unloading := by
  congr

theorem s22_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent s22.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)) := by
  intro hlook
  by_cases hd2 : dependent = 2
  · subst dependent
    rw [lookup_s22_2] at hlook
    cases hlook with | refl
    left; rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_s22_1] at hlook
      cases hlook with | refl
      left; rfl
    · by_cases hd4 : dependent = 4
      · subst dependent
        rw [lookup_s22_4] at hlook
        cases hlook with | refl
        right; rfl
      · have hnone : Finmap.lookup dependent s22.registry = none := by
          by_cases hd3 : dependent = 3
          · subst dependent
            simp [s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9,
              s8, s7, s6, s5, s4, s3, s2, s1, leaveState, unloadState, divertLandState,
              removeState, retireState, divertAbortState, raiseState, finishState,
              beginState, iterState, editCell, updateFiber, allocate, iterPayload,
              beginPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
          · simp [s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9,
              s8, s7, s6, s5, s4, s3, s2, s1, leaveState, unloadState, divertLandState,
              removeState, retireState, divertAbortState, raiseState, finishState,
              beginState, iterState, editCell, updateFiber, allocate, iterPayload,
              beginPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
              Finmap.lookup_empty, hd1, hd2, hd4, hd3]
        rw [hnone] at hlook
        cases hlook

theorem step_unload4 : LifecycleRule rulesSem (.unload 4 s22) s22 s23 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell4unloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases s22_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 10
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h14 : (1 : Nat) = 4 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

abbrev cell1unloading : Cell := { cell1 with phase := .unloading, committedView := ∅, retired := true, payload := { cell1.payload with iteratorCode := 0, accumulatorCode := 1, flightCode := some (), failureData := some () } }
abbrev cell4inactive : Cell := { cell4unloading with phase := .inactive, committedView := ∅, payload := { cell4unloading.payload with flightCode := none } }

theorem lookup_s23_1 : Finmap.lookup 1 s23.registry = some cell1unloading := by
  congr

theorem lookup_s23_2 : Finmap.lookup 2 s23.registry = some cell2inactive := by
  congr

theorem lookup_s23_4 : Finmap.lookup 4 s23.registry = some cell4inactive := by
  congr

theorem s23_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent s23.registry = some cell → cell.committedView = ∅ := by
  intro hlook
  by_cases hd2 : dependent = 2
  · subst dependent
    rw [lookup_s23_2] at hlook
    cases hlook with | refl
    rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_s23_1] at hlook
      cases hlook with | refl
      rfl
    · by_cases hd4 : dependent = 4
      · subst dependent
        rw [lookup_s23_4] at hlook
        cases hlook with | refl
        rfl
      · have hnone : Finmap.lookup dependent s23.registry = none := by
          by_cases hd3 : dependent = 3
          · subst dependent
            simp [s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10,
              s9, s8, s7, s6, s5, s4, s3, s2, s1, unloadState, leaveState, divertLandState,
              removeState, retireState, divertAbortState, raiseState, finishState,
              beginState, iterState, editCell, updateFiber, allocate, iterPayload,
              beginPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne]
          · simp [s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10,
              s9, s8, s7, s6, s5, s4, s3, s2, s1, unloadState, leaveState, divertLandState,
              removeState, retireState, divertAbortState, raiseState, finishState,
              beginState, iterState, editCell, updateFiber, allocate, iterPayload,
              beginPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
              Finmap.lookup_empty, hd1, hd2, hd4, hd3]
        rw [hnone] at hlook
        cases hlook

theorem step_unload1 : LifecycleRule rulesSem (.unload 1 { s23 with ambient := s23.ambient + 1 }) s23 s24 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell1unloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      have hview : cell.committedView = ∅ := s23_views dependent cell hlook
      rw [hview] at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)


/-! ### A.async: admissible divert evidence -/

def rulesPolicy : AsyncPolicy Unit State :=
  { atBoundary := fun (_ : Unit) (state : State) => providersOf state 10 = ∅
    landingWitness := fun (_ : Unit) (_ : State) => True
    allowed := fun (_ : Unit) (state : State) (choice : LandingChoice) =>
      match choice with
      | .land => True
      | .abort => providersOf state 10 = ∅
    mustLand := by intro flight state; trivial
    landSound := by intro flight state h; trivial
    abortGuard := by intro flight state h; exact h }

theorem divertAbort_admissible : divertAdmissible rulesSem rulesPolicy
    (.inr (.divertAbort 3 .absent)) s15 := by
  change ∃ cell flight, Finmap.lookup 3 s15.registry = some cell ∧
    cell.payload.flightCode = some flight ∧ cell.phase = .reloading ∧
      rulesPolicy.allowed flight s15 .abort
  refine ⟨cell3reloading, (), lookup_s15_3, rfl, rfl, ?_⟩
  change providersOf s15 10 = ∅
  decide

theorem divertLand_admissible : divertAdmissible rulesSem rulesPolicy
    (.inr (.divertLand 2 () 1 s19)) s19 := by
  change ∃ cell, Finmap.lookup 2 s19.registry = some cell ∧
    cell.payload.flightCode = some () ∧ cell.phase = .reloading ∧
      rulesPolicy.allowed () s19 .land
  refine ⟨cell2retired, lookup_s19_2, rfl, rfl, ?_⟩
  trivial

/-! ### ADR-09 cycle trace candidate (r = 0, c = 1, n = 2, former provider p = 3) -/

abbrev rc0 : State :=
  { ambient := 10, registry := ∅, coeffects := coeffects0,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

abbrev cellP : Cell :=
  { incarnation := 3, parent := none, birth := 0,
    component := { key := 3, requires := ∅, provides := {20}, actionCode := (), iteratorCode := 0, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cellR : Cell :=
  { incarnation := 0, parent := none, birth := 1,
    component := { key := 0, requires := {20}, provides := {10}, actionCode := (), iteratorCode := 0, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cellC : Cell :=
  { incarnation := 1, parent := some 0, birth := 2,
    component := { key := 1, requires := {20}, provides := ∅, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cellN : Cell :=
  { incarnation := 2, parent := some 1, birth := 3,
    component := { key := 2, requires := {10}, provides := {20}, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev view20p : Finmap (fun _ : Nat => Nat) := Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))

abbrev c1 : State := allocate rc0 3 cellP
abbrev c2 : State := beginState rulesSem c1 3 ∅ ()
abbrev c3 : State := finishState { c2 with ambient := 9 } 3
abbrev c4 : State := allocate c3 0 cellR
abbrev c5 : State := beginState rulesSem c4 0 view20p ()
abbrev c6 : State := finishState { c5 with ambient := 8 } 0
abbrev c7 : State := allocate c6 1 cellC
abbrev c8 : State := beginState rulesSem c7 1 view20p ()
abbrev c9 : State := iterState rulesSem { c8 with ambient := 7 } 1 1 0
abbrev c10 : State := retireState c9 1
abbrev c11 : State := retireState c10 3
abbrev c12 : State := raiseState c11 3 ()
abbrev c13 : State := divertLandState rulesSem c12 1 1
abbrev c14 : State := unloadState { c13 with ambient := c13.ambient + 2 } 1
abbrev c15 : State := leaveState c14 0
abbrev c16 : State := unloadState c15 0
abbrev c17 : State := unloadState c16 3
abbrev c18 : State := removeState c17 3
abbrev c19 : State := allocate c18 2 cellN

theorem cycleStep_insertP : OrchestrationRule (.insert none 3 cellP) rc0 c1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 3) (child := cellP)
    (by decide) (by decide)
    (by simp [CanonicalInitialCell, nextBirth])
    (by intro name cell' h; simp at h)

theorem cycleStep_beginP : LifecycleRule rulesSem (.begin 3 ∅ ()) c1 c2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellP)
    (hlook := by simp [c1, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl)
    (htarget := ⟨cellP, by simp [c1, allocate, Finmap.lookup_insert], rfl, by
      intro key provider hkv
      change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

abbrev cellPbegun : Cell := { cellP with phase := .reloading, committedView := ∅, payload := { cellP.payload with iteratorCode := 0, accumulatorCode := 0, flightCode := some () } }
abbrev cellPactive : Cell := { cellPbegun with phase := .active }

theorem cycleStep_finishP : LifecycleRule rulesSem (.finish 3 { c2 with ambient := 9 }) c2 c3 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellPbegun) (hlook := by congr)
    (hphase := rfl)
    (htarget := ⟨cellPbegun, by congr, rfl, by
      intro key provider hkv
      change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := rfl)

theorem provides20_c3 : ProvidesNow c3 3 20 := by
  refine ⟨cellPactive, by congr, ?_, rfl⟩
  change 20 ∈ (Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys
  rw [Finmap.mem_keys, Finmap.mem_insert]
  simp

theorem cycleStep_insertR : OrchestrationRule (.insert none 0 cellR) c3 c4 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 0) (child := cellR)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, c3, c2, c1, finishState, beginState, editCell,
        updateFiber, allocate, beginPayload, rulesSem, cellP, Finmap.lookup_insert]
      decide)
    (by intro name cell' h
        by_cases hname : name = 3
        · subst name
          simp [c3, c2, c1, finishState, beginState, editCell, updateFiber, allocate,
            beginPayload, rulesSem, cellP, Finmap.lookup_insert] at h
          have hcell' : cell' = cellPactive := h.symm
          subst cell'
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
          subst key
          simp
        · simp [c3, c2, c1, finishState, beginState, editCell, updateFiber, allocate,
            beginPayload, rulesSem, cellP, Finmap.lookup_insert, hname] at h)

theorem cycleTargetViewAt_c4_0 : TargetViewAt c4 0 view20p := by
  refine ⟨cellR, by simp [c4, c3, allocate, Finmap.lookup_insert], ?_, ?_⟩
  · change view20p.keys = {20}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
    by_cases hkey : key = 20 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 20
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 3 := (Option.some.inj hkv).symm
      subst provider
      exact provides20_c3
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem cycleStep_beginR : LifecycleRule rulesSem (.begin 0 view20p ()) c4 c5 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellR)
    (hlook := by simp [c4, c3, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl) (htarget := cycleTargetViewAt_c4_0) (hlaunch := rfl)

abbrev cellRbegun : Cell := { cellR with phase := .reloading, committedView := view20p, payload := { cellR.payload with iteratorCode := 0, accumulatorCode := 0, flightCode := some () } }

theorem cycleStep_finishR : LifecycleRule rulesSem (.finish 0 { c5 with ambient := 8 }) c5 c6 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellRbegun) (hlook := by congr)
    (hphase := rfl)
    (htarget := ⟨cellRbegun, by congr, by
      change view20p.keys = {20}
      apply Finset.ext
      intro key
      rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
      change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
      by_cases hkey : key = 20 <;> simp [hkey], by
      intro key provider hkv
      change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
      by_cases hkey : key = 20
      · subst key
        rw [Finmap.lookup_insert] at hkv
        have hp : provider = 3 := (Option.some.inj hkv).symm
        subst provider
        exact provides20_c3
      · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
          Finmap.lookup_empty] at hkv
        cases hkv⟩)
    (hstage := rfl)

theorem cycleStep_insertC : OrchestrationRule (.insert (some 0) 1 cellC) c6 c7 := by
  exact OrchestrationRule.insert (registrar := some 0) (fresh := 1) (child := cellC)
    (by
      simp [c6, c5, c4, c3, c2, c1, finishState, beginState, editCell, updateFiber,
        allocate, beginPayload, rulesSem, cellP, cellR, Finmap.lookup_insert,
        Finmap.lookup_insert_of_ne, Finmap.lookup_empty])
    (by
      simp [c6, c5, c4, c3, c2, c1, finishState, beginState, editCell, updateFiber,
        allocate, beginPayload, rulesSem, cellP, cellR, Finmap.lookup_insert])
    (by
      simp [CanonicalInitialCell, Registered, c6, c5, c4, c3, c2, c1, finishState,
        beginState, editCell, updateFiber, allocate, beginPayload, rulesSem, cellP,
        cellR, Finmap.lookup_insert]
      decide)
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem cycleTargetViewAt_c7_1 : TargetViewAt c7 1 view20p := by
  refine ⟨cellC, by simp [c7, c6, allocate, Finmap.lookup_insert], ?_, ?_⟩
  · change view20p.keys = {20}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
    by_cases hkey : key = 20 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 20
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 3 := (Option.some.inj hkv).symm
      subst provider
      exact provides20_c3
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

abbrev cellCbegun : Cell := { cellC with phase := .reloading, committedView := view20p, payload := { cellC.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }

theorem cycleStep_beginC : LifecycleRule rulesSem (.begin 1 view20p ()) c7 c8 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellC)
    (hlook := by simp [c7, c6, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl) (htarget := cycleTargetViewAt_c7_1) (hlaunch := rfl)

theorem cycleStep_iterC : LifecycleRule rulesSem (.iter 1 0 1 { c8 with ambient := 7 }) c8 c9 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellCbegun) (hlook := by congr)
    (hphase := rfl)
    (htarget := by
      refine ⟨cellCbegun, by congr, ?_, ?_⟩
      · change view20p.keys = {20}
        apply Finset.ext
        intro key
        rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
        change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
        by_cases hkey : key = 20 <;> simp [hkey]
      · intro key provider hkv
        change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
        by_cases hkey : key = 20
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have hp : provider = 3 := (Option.some.inj hkv).symm
          subst provider
          exact provides20_c3
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
            Finmap.lookup_empty] at hkv
          cases hkv)
    (hstage := rfl)
    (hrank := by decide)

abbrev cellCitered : Cell := { cellCbegun with payload := { cellCbegun.payload with iteratorCode := 0, accumulatorCode := 1 } }
abbrev cellCretired : Cell := { cellCitered with retired := true }
abbrev cellPretired : Cell := { cellPactive with retired := true }
abbrev cellPunloading : Cell := { cellPretired with phase := .unloading, payload := { cellPretired.payload with failureData := some () } }

theorem cycleStep_retireC : OrchestrationRule (.retire 1 cellCitered) c9 c10 := by
  exact OrchestrationRule.retire (by congr)

theorem cycleStep_retireP : OrchestrationRule (.retire 3 cellPactive) c10 c11 := by
  exact OrchestrationRule.retire (by congr)

theorem cycleStep_raiseP : LifecycleRule rulesSem (.raise 3 ()) c11 c12 := by
  exact LifecycleRule.raise (sem := rulesSem) (cell := cellPretired) (hlook := by congr)
    (hphase := by right; rfl) (hreal := rfl)

abbrev cellCunloading : Cell := { cellCretired with phase := .unloading, payload := { cellCretired.payload with accumulatorCode := 2 } }
abbrev cellCinactive : Cell := { cellCunloading with phase := .inactive, committedView := ∅, payload := { cellCunloading.payload with flightCode := none } }
abbrev cellRactive : Cell := { cellRbegun with phase := .active }
abbrev cellRleft : Cell := { cellRactive with phase := .unloading }
abbrev cellRinactive : Cell := { cellRleft with phase := .inactive, committedView := ∅, payload := { cellRleft.payload with flightCode := none } }
abbrev cellPfailed : Cell := { cellPunloading with phase := .failed, committedView := ∅, payload := { cellPunloading.payload with flightCode := none } }

theorem lookup_c12_3 : Finmap.lookup 3 c12.registry = some cellPunloading := by
  congr

theorem cycleTargetNot_c12_1 : ¬ TargetViewAt c12 1 view20p := by
  intro h
  rcases h with ⟨cell, hlook, _hkeys, hall⟩
  have hprov : ProvidesNow c12 3 20 := hall 20 3 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_c12_3] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem cycleStep_divertLandC : LifecycleRule rulesSem (.divertLand 1 () 1 c12) c12 c13 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cellCretired) (hlook := by congr)
    (hphase := rfl) (hchanged := cycleTargetNot_c12_1) (hland := rfl)

theorem lookup_c13_0 : Finmap.lookup 0 c13.registry = some cellRactive := by
  congr

theorem lookup_c13_1 : Finmap.lookup 1 c13.registry = some cellCunloading := by
  congr

theorem lookup_c13_3 : Finmap.lookup 3 c13.registry = some cellPunloading := by
  congr

theorem c13_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent c13.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = view20p := by
  intro hlook
  by_cases hd3 : dependent = 3
  · subst dependent
    rw [lookup_c13_3] at hlook
    cases hlook with | refl
    left; rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_c13_1] at hlook
      cases hlook with | refl
      right; rfl
    · by_cases hd0 : dependent = 0
      · subst dependent
        rw [lookup_c13_0] at hlook
        cases hlook with | refl
        right; rfl
      · have hnone : Finmap.lookup dependent c13.registry = none := by
          simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1,
            divertLandState, raiseState, retireState, iterState, finishState, beginState,
            editCell, updateFiber, allocate, iterPayload, beginPayload, rulesSem,
            Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty,
            hd3, hd1, hd0]
        rw [hnone] at hlook
        cases hlook

theorem cycleStep_unloadC : LifecycleRule rulesSem (.unload 1 { c13 with ambient := c13.ambient + 2 }) c13 c14 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellCunloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases c13_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 20
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h31 : (3 : Nat) = 1 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_c14_0 : Finmap.lookup 0 c14.registry = some cellRactive := by
  congr

theorem lookup_c14_3 : Finmap.lookup 3 c14.registry = some cellPunloading := by
  congr

theorem cycleTargetNot_c14_0 : ¬ TargetViewAt c14 0 view20p := by
  intro h
  rcases h with ⟨cell, hlook, _hkeys, hall⟩
  have hprov : ProvidesNow c14 3 20 := hall 20 3 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_c14_3] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem cycleStep_leaveR : LifecycleRule rulesSem (.leave 0) c14 c15 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cellRactive) (hlook := by congr)
    (hphase := rfl) (hchanged := cycleTargetNot_c14_0)

theorem lookup_c15_0 : Finmap.lookup 0 c15.registry = some cellRleft := by
  congr

theorem lookup_c15_1 : Finmap.lookup 1 c15.registry = some cellCinactive := by
  congr

theorem lookup_c15_3 : Finmap.lookup 3 c15.registry = some cellPunloading := by
  congr

theorem c15_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent c15.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = view20p := by
  intro hlook
  by_cases hd3 : dependent = 3
  · subst dependent
    rw [lookup_c15_3] at hlook
    cases hlook with | refl
    left; rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_c15_1] at hlook
      cases hlook with | refl
      left; rfl
    · by_cases hd0 : dependent = 0
      · subst dependent
        rw [lookup_c15_0] at hlook
        cases hlook with | refl
        right; rfl
      · have hnone : Finmap.lookup dependent c15.registry = none := by
          simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1,
            leaveState, unloadState, divertLandState, raiseState, retireState,
            iterState, finishState, beginState, editCell, updateFiber, allocate,
            iterPayload, beginPayload, rulesSem, Finmap.lookup_insert,
            Finmap.lookup_insert_of_ne, Finmap.lookup_empty, hd3, hd1, hd0]
        rw [hnone] at hlook
        cases hlook

theorem cycleStep_unloadR : LifecycleRule rulesSem (.unload 0 c15) c15 c16 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellRleft) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases c15_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 20
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h30 : (3 : Nat) = 0 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_c16_3 : Finmap.lookup 3 c16.registry = some cellPunloading := by
  congr

theorem lookup_c16_1 : Finmap.lookup 1 c16.registry = some cellCinactive := by
  congr

theorem lookup_c16_0 : Finmap.lookup 0 c16.registry = some cellRinactive := by
  congr

theorem c16_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent c16.registry = some cell → cell.committedView = ∅ := by
  intro hlook
  by_cases hd3 : dependent = 3
  · subst dependent
    rw [lookup_c16_3] at hlook
    cases hlook with | refl
    rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_c16_1] at hlook
      cases hlook with | refl
      rfl
    · by_cases hd0 : dependent = 0
      · subst dependent
        rw [lookup_c16_0] at hlook
        cases hlook with | refl
        rfl
      · have hnone : Finmap.lookup dependent c16.registry = none := by
          simp [unloadState, leaveState, divertLandState, raiseState, retireState,
            iterState, finishState, beginState, editCell, updateFiber, allocate, hd3, hd1, hd0]
        rw [hnone] at hlook
        cases hlook

theorem cycleStep_unloadP : LifecycleRule rulesSem (.unload 3 c16) c16 c17 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellPunloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      have hview : cell.committedView = ∅ := c16_views dependent cell hlook
      rw [hview] at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_c17_3 : Finmap.lookup 3 c17.registry = some cellPfailed := by
  congr

theorem lookup_c17_1 : Finmap.lookup 1 c17.registry = some cellCinactive := by
  congr

theorem lookup_c17_0 : Finmap.lookup 0 c17.registry = some cellRinactive := by
  congr

theorem cycleStep_removeP : OrchestrationRule (.remove 3) c17 c18 := by
  exact OrchestrationRule.remove (cell := cellPfailed) (hlook := by congr)
    (hretired := rfl) (hphase := by right; rfl) (hnoChild := by
      intro name cell' h hparent
      by_cases hd3 : name = 3
      · subst name
        rw [lookup_c17_3] at h
        cases h with | refl
        cases hparent
      · by_cases hd1 : name = 1
        · subst name
          rw [lookup_c17_1] at h
          cases h with | refl
          cases hparent
        · by_cases hd0 : name = 0
          · subst name
            rw [lookup_c17_0] at h
            cases h with | refl
            cases hparent
          · have hnone : Finmap.lookup name c17.registry = none := by
              simp [unloadState, leaveState, divertLandState, raiseState,
                retireState, iterState, finishState, beginState, editCell, updateFiber,
                allocate, hd3, hd1, hd0]
            rw [hnone] at h
            cases h)

theorem cycleStep_insertN : OrchestrationRule (.insert (some 1) 2 cellN) c18 c19 := by
  exact OrchestrationRule.insert (registrar := some 1) (fresh := 2) (child := cellN)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, Registered, removeState, unloadState,
        leaveState, divertLandState, raiseState, retireState, iterState, finishState,
        beginState, editCell, updateFiber, allocate]
      rfl)
    (by intro name cell' h
        by_cases hd1 : name = 1
        · subst name
          simp [removeState, unloadState, leaveState, divertLandState, raiseState,
            retireState, iterState, finishState, beginState, editCell, updateFiber,
            allocate] at h
          have hcell' : cell' = cellCinactive := h.symm
          subst cell'
          apply Finset.disjoint_left.mpr
          grind only [← Finset.notMem_empty]
        · by_cases hd0 : name = 0
          · subst name
            simp [removeState, unloadState, leaveState, divertLandState,
              raiseState, retireState, iterState, finishState, beginState, editCell,
              updateFiber, allocate] at h
            have hcell' : cell' = cellRinactive := h.symm
            subst cell'
            apply Finset.disjoint_left.mpr
            intro key hkey
            simp at hkey
            subst key
            simp
          · have hnone : Finmap.lookup name c18.registry = none := by
              by_cases hd3 : name = 3
              · subst name
                rfl
              · by_cases hd2 : name = 2
                · subst name
                  decide
                · simp [removeState, unloadState, leaveState,
                    divertLandState, raiseState, retireState, iterState, finishState,
                    beginState, editCell, updateFiber, allocate, hd1, hd0, hd3]
            rw [hnone] at h
            cases h)

/-! ### Cycle-trace endpoint facts -/

theorem lookup_c19_0 : Finmap.lookup 0 c19.registry = some cellRinactive := by
  congr

theorem lookup_c19_1 : Finmap.lookup 1 c19.registry = some cellCinactive := by
  congr

theorem lookup_c19_2 : Finmap.lookup 2 c19.registry = some cellN := by
  congr

theorem c19_lookup_none (name : Nat) (hd0 : name ≠ 0) (hd1 : name ≠ 1) (hd2 : name ≠ 2) :
    Finmap.lookup name c19.registry = none := by
  by_cases hd3 : name = 3
  · subst name
    decide
  · simp [allocate, removeState, unloadState, leaveState, divertLandState,
      raiseState, retireState, iterState, finishState, beginState, editCell, updateFiber,
      hd0, hd1, hd2, hd3]

theorem cycleEndpoint_parentEdges :
    (Finmap.lookup 1 c19.registry).isSome ∧
      (∀ cell, Finmap.lookup 1 c19.registry = some cell → cell.parent = some 0) ∧
      (∀ cell, Finmap.lookup 2 c19.registry = some cell → cell.parent = some 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  all_goals
    intro _ h
    cases h with | refl
    rfl
theorem cycleEndpoint_providerEdge :
    (∀ cell, Finmap.lookup 2 c19.registry = some cell →
      20 ∈ cell.component.provides) ∧
      (∀ cell, Finmap.lookup 0 c19.registry = some cell →
        cell.component.requires = {20}) ∧
      ¬ ProvidesNow c19 3 20 := by
  refine ⟨?_, ?_, ?_⟩
  · intro cell h
    cases h with | refl
    simp
  · intro cell h
    cases h with | refl
    rfl
  · rintro ⟨cell, hlook, _htable, _hphase⟩
    cases hlook

theorem cycleEndpoint_precedenceAcyclic :
    (cellR.birth < cellC.birth ∧ cellC.birth < cellN.birth) ∧
      (∀ cell, Finmap.lookup 0 c19.registry = some cell → cell.birth = cellR.birth) ∧
      (∀ cell, Finmap.lookup 1 c19.registry = some cell → cell.birth = cellC.birth) ∧
      (∀ cell, Finmap.lookup 2 c19.registry = some cell → cell.birth = cellN.birth) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro cell h
    rw [lookup_c19_0] at h
    cases h with | refl
    rfl
  · intro cell h
    rw [lookup_c19_1] at h
    cases h with | refl
    rfl
  · intro cell h
    rw [lookup_c19_2] at h
    cases h with | refl
    rfl

theorem cycleEndpoint_lifetimeFresh :
    (∀ name cell, Finmap.lookup name c19.registry = some cell → name ∈ c19.ledger.everIssued) ∧
      c19.allocationHistory.Nodup := by
  refine ⟨?_, ?_⟩
  · intro name cell h
    by_cases hd2 : name = 2
    · subst name
      rw [lookup_c19_2] at h
      cases h with | refl
      decide
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        decide
      · by_cases hd0 : name = 0
        · subst name
          rw [lookup_c19_0] at h
          cases h with | refl
          decide
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · decide

def cycleProfile : WellFormedProfile Nat Nat Nat Unit Nat Nat Unit Unit Nat :=
  { lifecycleCoherent := fun (_ : State) => True
    root := fun (_ : State) => True
    declarations := fun (_ : State) => True }

theorem c19_parentClosed : ParentClosed c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    trivial
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      change 0 ∈ c19.registry.keys
      rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
      rw [lookup_c19_0]
      rfl
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        change 1 ∈ c19.registry.keys
        rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
        rw [lookup_c19_1]
        rfl
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_parentAcyclic : ParentAcyclic c19 := by
  unfold ParentAcyclic
  have acc0 : Acc (ParentStep c19) 0 := by
    constructor
    intro parent hp
    rcases hp with ⟨c, hc, hpar⟩
    rw [lookup_c19_0] at hc
    cases hc with | refl
    cases hpar
  have acc1 : Acc (ParentStep c19) 1 := by
    constructor
    intro parent hp
    rcases hp with ⟨c, hc, hpar⟩
    rw [lookup_c19_1] at hc
    cases hc with | refl
    have h0 : 0 = parent := Option.some.inj hpar
    subst parent
    exact acc0
  have acc2 : Acc (ParentStep c19) 2 := by
    constructor
    intro parent hp
    rcases hp with ⟨c, hc, hpar⟩
    rw [lookup_c19_2] at hc
    cases hc with | refl
    have h1 : 1 = parent := Option.some.inj hpar
    subst parent
    exact acc1
  constructor
  intro name
  by_cases hd2 : name = 2
  · subst name
    exact acc2
  · by_cases hd1 : name = 1
    · subst name
      exact acc1
    · by_cases hd0 : name = 0
      · subst name
        exact acc0
      · constructor
        intro parent hp
        rcases hp with ⟨c, hc, _hpar⟩
        rw [c19_lookup_none name hd0 hd1 hd2] at hc
        cases hc

theorem c19_tableConfined : TableConfined c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    intro key hkey
    change key ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_insert] at hkey
    rcases hkey with hkey | hempty
    · subst key
      simp
    · rw [Finmap.mem_def] at hempty
      change key ∈ (∅ : Multiset Nat) at hempty
      simp at hempty
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key hkey
      change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
      rw [Finmap.mem_keys, Finmap.mem_def] at hkey
      change key ∈ (∅ : Multiset Nat) at hkey
      simp at hkey
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key hkey
        change key ∈ (Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
        rw [Finmap.mem_keys, Finmap.mem_insert] at hkey
        rcases hkey with hkey | hempty
        · subst key
          simp
        · rw [Finmap.mem_def] at hempty
          change key ∈ (∅ : Multiset Nat) at hempty
          simp at hempty
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_provisionDisjoint : ProvisionDisjoint c19 := by
  intro a b ca cb ha hb hab
  by_cases hd0a : a = 0
  · subst a
    rw [lookup_c19_0] at ha
    cases ha with | refl
    by_cases hd1b : b = 1
    · subst b
      rw [lookup_c19_1] at hb
      cases hb with | refl
      apply Finset.disjoint_left.mpr
      intro key hkey
      simp at hkey ⊢
    · by_cases hd2b : b = 2
      · subst b
        rw [lookup_c19_2] at hb
        cases hb with | refl
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey
        subst key
        simp
      · by_cases hd0b : b = 0
        · subst b
          rw [lookup_c19_0] at hb
          cases hb with | refl
          exfalso
          exact hab rfl
        · rw [c19_lookup_none b hd0b hd1b hd2b] at hb
          cases hb
  · by_cases hd1a : a = 1
    · subst a
      rw [lookup_c19_1] at ha
      cases ha with | refl
      by_cases hd0b : b = 0
      · subst b
        rw [lookup_c19_0] at hb
        cases hb with | refl
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey ⊢
      · by_cases hd2b : b = 2
        · subst b
          rw [lookup_c19_2] at hb
          cases hb with | refl
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey ⊢
        · by_cases hd1b : b = 1
          · subst b
            rw [lookup_c19_1] at hb
            cases hb with | refl
            exfalso
            exact hab rfl
          · rw [c19_lookup_none b hd0b hd1b hd2b] at hb
            cases hb
    · by_cases hd2a : a = 2
      · subst a
        rw [lookup_c19_2] at ha
        cases ha with | refl
        by_cases hd0b : b = 0
        · subst b
          rw [lookup_c19_0] at hb
          cases hb with | refl
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
          subst key
          simp
        · by_cases hd1b : b = 1
          · subst b
            rw [lookup_c19_1] at hb
            cases hb with | refl
            apply Finset.disjoint_left.mpr
            intro key hkey
            simp at hkey ⊢
          · by_cases hd2b : b = 2
            · subst b
              rw [lookup_c19_2] at hb
              cases hb with | refl
              exfalso
              exact hab rfl
            · rw [c19_lookup_none b hd0b hd1b hd2b] at hb
              cases hb
      · rw [c19_lookup_none a hd0a hd1a hd2a] at ha
        cases ha

theorem c19_committedViewClosed : CommittedViewClosed c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    intro key provider hkv
    rw [Finmap.lookup_empty] at hkv
    cases hkv
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key provider hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_committedProvidersClosed : CommittedProvidersClosed c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    intro key provider hkv
    rw [Finmap.lookup_empty] at hkv
    cases hkv
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key provider hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_dataCoherent : DataCoherent c19 := by
  unfold DataCoherent
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro name cell h hactive
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      simp at hactive
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        simp at hactive
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          simp at hactive
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · intro name cell h
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      intro key hkey
      change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
      rw [Finmap.mem_keys, Finmap.mem_def] at hkey
      change key ∈ (∅ : Multiset Nat) at hkey
      simp at hkey
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        intro key hkey
        change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
        rw [Finmap.mem_keys, Finmap.mem_def] at hkey
        change key ∈ (∅ : Multiset Nat) at hkey
        simp at hkey
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          intro key hkey
          change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
          rw [Finmap.mem_keys, Finmap.mem_def] at hkey
          change key ∈ (∅ : Multiset Nat) at hkey
          simp at hkey
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · intro name cell h
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      rfl
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        rfl
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          rfl
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · refine ⟨by decide, ?_⟩
    intro name cell h
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      exact ⟨by decide, by decide⟩
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        exact ⟨by decide, by decide⟩
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          exact ⟨by decide, by decide⟩
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · refine ⟨?_, ?_⟩
    · intro name hkey
      by_cases hd0 : name = 0
      · subst name; decide
      · by_cases hd1 : name = 1
        · subst name; decide
        · by_cases hd2 : name = 2
          · subst name; decide
          · have hisome : (Finmap.lookup name c19.registry).isSome := by
              rw [Finmap.lookup_isSome, ← Finmap.mem_keys]
              exact hkey
            rw [c19_lookup_none name hd0 hd1 hd2] at hisome
            simp at hisome
    · intro name hhist
      simp [c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4,
        c3, c2, c1, allocate, removeState, unloadState, leaveState, divertLandState,
        raiseState, retireState, iterState, finishState, beginState, editCell,
        updateFiber, iterPayload, beginPayload, rulesSem] at hhist
      rcases hhist with h3 | h0 | h1 | h2
      all_goals
        subst name; decide

theorem cycleEndpoint_wellFormed : WellFormed cycleProfile c19 :=
  ⟨c19_parentClosed, c19_parentAcyclic, c19_tableConfined, c19_provisionDisjoint,
    c19_committedViewClosed, c19_committedProvidersClosed, c19_dataCoherent,
    trivial, trivial, trivial⟩


/-! ### Nonconstant factorization evidence -/

abbrev cell1begun : Cell := { cell1 with phase := .reloading, committedView := ∅, payload := { cell1.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }
abbrev cell2begun : Cell := { cell2 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell2.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }

theorem factorization_nonconstant :
    ∃ label1 label2 before1 before2 m1 m2, SelectedBody rulesSem label1 before1 m1 ∧
      SelectedBody rulesSem label2 before2 m2 ∧ m1 ≠ m2 := by
  refine ⟨.inr (.iter 2 0 1 { s6 with ambient := 7 }), .inr (.iter 1 0 1 { s2 with ambient := 9 }),
    s6, s2, { s6 with ambient := 7 }, { s2 with ambient := 9 }, ?_, ?_, ?_⟩
  · refine ⟨cell2begun, by congr, rfl, targetViewAt_s6_2, rfl, by decide, rfl⟩
  · refine ⟨cell1begun, by congr, rfl, ?_, rfl, by decide, rfl⟩
    refine ⟨cell1begun, by congr, rfl, by
      intro key provider hkv
      change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩
  · intro h
    have hh := congrArg (fun state : State => state.ambient) h
    simp at hh


end

end STC.Examples.GlobalRules
