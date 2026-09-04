module

public import STC.Examples.GlobalRules.Semantics
public import STC.Examples.GlobalRules.Trace

/-!
# Global rule evidence

Full-step frame discharges, the nested-registration witness, the §3.1
negatives, the R.base macro witnesses, the nonconstant fixed-operation
factorization, the A.async admissibility evidence, and the ADR-09 cycle
trace candidate with its endpoint facts.
-/

namespace STC.Examples.GlobalRules

open STC STC.State STC.Control

@[expose] public section

/-! ### Full-step D48 discharges -/

theorem iter1_writeFrame : WriteFrame s3 1 s4 :=
  iter_full_writeFrame rulesSem bodyFrameAdequacy lookup_s3_1
    (by change fixtureStage 1 s3 = some (.yield s3 [2] 0); rfl)
    (by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)
    rfl

theorem iter1_readNoninterference : ReadNoninterference s3 1 s4 :=
  iter_full_readNoninterference rulesSem bodyFrameAdequacy lookup_s3_1
    (by change fixtureStage 1 s3 = some (.yield s3 [2] 0); rfl)
    rfl

theorem finish1_writeFrame : WriteFrame s4 1 s5 :=
  finish_full_writeFrame rulesSem bodyFrameAdequacy lookup_s4_1
    (by change fixtureStage 0 s4 = some (.halt s4 []); rfl)
    (by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)
    rfl

theorem finish1_readNoninterference : ReadNoninterference s4 1 s5 :=
  finish_full_readNoninterference rulesSem bodyFrameAdequacy lookup_s4_1
    (by change fixtureStage 0 s4 = some (.halt s4 []); rfl)
    rfl

theorem lookup_s4_2 : Finmap.lookup 2 s4.registry = some cell2 := by
  congr

theorem finish1_tableConfined : TableConfined s5 :=
  finish_tableConfined rulesSem s4 1 [] (by
    intro name cell hl
    have hmem : name ∈ s4.registry.keys := by
      rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
      rfl
    simp [s4, s3, s2, s1, iterState, beginState, editCell, allocate, beginPayload,
      iterPayload, rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
    rcases hmem with h1 | h2 | htail
    · subst name
      rw [lookup_s4_1] at hl
      cases hl with | refl
      intro key hkey
      change key ∈ cell1itered.committed.entries.keys at hkey
      rw [cell1itered, cell1begun, cell1] at hkey
      simp at hkey
    · subst name
      rw [lookup_s4_2] at hl
      cases hl with | refl
      intro key hkey
      change key ∈ cell2.committed.entries.keys at hkey
      rw [cell2] at hkey
      simp at hkey
    · rcases htail with h1' | hempty
      · subst name
        rw [lookup_s4_1] at hl
        cases hl with | refl
        intro key hkey
        change key ∈ cell1itered.committed.entries.keys at hkey
        rw [cell1itered, cell1begun, cell1] at hkey
        simp at hkey
      · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
        simp at hempty)

theorem divertLand2_writeFrame : WriteFrame s22 2 s23 :=
  divertLand_full_writeFrame (landing := ()) rulesSem bodyFrameAdequacy lookup_s22_2
    (by change fixtureLanding () s22 = some (.landed { s22 with ambient := s22.ambient + 1 } [7]); rfl)
    (by change (∅ : Finset Nat) ⊆ ({20} : Finset Nat); simp)
    rfl

theorem divertLand2_readNoninterference : ReadNoninterference s22 2 s23 :=
  divertLand_full_readNoninterference (landing := ()) rulesSem bodyFrameAdequacy lookup_s22_2
    (by change fixtureLanding () s22 = some (.landed { s22 with ambient := s22.ambient + 1 } [7]); rfl)
    rfl

/-- Every foreign edit of the unload1 body is a recorded-child retirement of
owner 1 (the only changed cell is 2, retired from inactive). -/
theorem unload1_hchildren : ∀ n cellN, Finmap.lookup n s26.registry = some cellN → n ≠ 1 →
    Finmap.lookup n s26.registry ≠ Finmap.lookup n s27.registry →
      cellN.parent = some 1 := by
  intro n cellN hl hn hne
  have hbody : Finmap.lookup n s26.registry ≠ Finmap.lookup n (foldRetire [2] s26).registry := by
    intro h'
    exact hne (by
      rw [h']
      change Finmap.lookup n (foldRetire [2] s26).registry = Finmap.lookup n (unloadState (foldRetire [2] s26) 1).registry
      exact (editCell_lookup_ne (foldRetire [2] s26) 1 _ hn).symm)
  rcases foldRetire_lookup [2] s26 n with h | h
  · exfalso
    exact hbody h.symm
  · rcases h with ⟨hmem, cell, hl', hret, ha⟩
    rw [List.mem_singleton] at hmem
    subst n
    rw [hl'] at hl
    have hcellN : cellN = cell := (Option.some.inj hl).symm
    rw [hcellN]
    rw [lookup_s26_2] at hl'
    have hcell2 : cell = cell2inactive := (Option.some.inj hl').symm
    rw [hcell2]

theorem unload1_cleanupFrame : CleanupFrame s26 1 s27 :=
  unload_full_cleanupFrame rulesSem bodyFrameAdequacy lookup_s26_1 unload1_hchildren
    (by change fixtureAccumulator [2] s26 = some (foldRetire [2] s26); rfl)
    rfl

theorem unload1_readNoninterference : ReadNoninterference s26 1 s27 :=
  unload_full_readNoninterference rulesSem bodyFrameAdequacy lookup_s26_1
    (by change fixtureAccumulator [2] s26 = some (foldRetire [2] s26); rfl)
    rfl

theorem unload1_noAllocation :
    s27.registry.keys = s26.registry.keys ∧ s27.ledger = s26.ledger ∧
      s27.allocationHistory = s26.allocationHistory :=
  unload_noAllocation rulesSem bodyFrameAdequacy lookup_s26_1 rfl
    (by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hl, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s26_2] at hl
          cases hl with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s26.registry = none := by
              change Finmap.lookup 3 (editCell s25 2 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s25 2 _ (by decide)]
              change Finmap.lookup 3 (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s24 4 _ (by decide)]
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [7], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hl
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s26_4] at hl
              cases hl with | refl
              rw [Finmap.lookup_empty] at hkv
              cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s26_5] at hl
                cases hl with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s26.registry = none :=
                  lookup_s26_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hl)
    (by change fixtureAccumulator [2] s26 = some (foldRetire [2] s26); rfl)
    (by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)

/-! ### The nested-registration witness -/

def registrationWitness : NestedRegistrationWitness rulesSem :=
  { actionCode := ()
    parent := 1
    fresh := 2
    child := cell2
    parentBefore := s2
    parentAfter := s3
    result := { state := s3, inverse? := some [2] }
    inverse := [2]
    parentCell := cell1begun
    parent_lookup := lookup_s2_1
    action_run := by
      change fixtureAction () s2 = some { state := s3, inverse? := some [2] }
      unfold fixtureAction
      rw [show Finmap.lookup 2 s2.registry = none from by
        change Finmap.lookup 2 (editCell s1 1 (fun cell => { cell with phase := .reloading, committedView := ∅, payload := beginPayload rulesSem cell () })).registry = none
        rw [editCell_lookup_ne s1 1 _ (by decide)]
        change Finmap.lookup 2 (Finmap.insert 1 cell1 s0.registry) = none
        rw [Finmap.lookup_insert_of_ne (a := 1) (a' := 2) (s := s0.registry) (by decide)]
        change Finmap.lookup 2 (∅ : Finmap (fun _ : Nat => Cell)) = none
        rw [Finmap.lookup_empty]]
      simp [s2, s1, beginState, editCell, allocate, beginPayload, rulesSem,
        ]
    insert_step := step_insert2
    endpoint_link := rfl
    returns_inverse := rfl
    retire_adequate := by
      intro state cell hl
      change some (List.foldl (fun s n => (retire? s n).getD s) state [2]) = some (editCell state 2 (fun cell => { cell with retired := true }))
      rw [show List.foldl (fun s n => (retire? s n).getD s) state [2] = (retire? state 2).getD state from rfl]
      unfold retire?
      rw [hl]
      change some (updateFiber state 2 { cell with retired := true }) = some (editCell state 2 (fun cell => { cell with retired := true }))
      congr 1
      unfold editCell
      rw [hl]
      rfl }

theorem registrationWitness_folds :
    ∃ cell, Finmap.lookup 1 (foldInverseState rulesSem s3 1 [2]).registry = some cell ∧
      cell.payload.accumulatorCode = rulesSem.composeInverse cell1begun.payload.accumulatorCode [2] :=
  nestedRegistration_foldInverse rulesSem registrationWitness

/-! ### The §3.1 negatives -/

theorem retiredOwner_noTarget : ¬ TargetViewAt s17 1 ∅ := by
  intro h
  rcases h with ⟨cell, hl, hret, _hkeys, _hall⟩
  rw [lookup_s17_1] at hl
  cases hl with | refl
  cases hret

theorem retiredActive_provides : ProvidesNow s17 1 10 :=
  ⟨_, lookup_s17_1, by
    change 10 ∈ (commitProjection s17 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem inactiveNonretired_notQuiescent : ¬ Quiescent s8 := by
  intro h
  have hq := h 3 cell3 (by congr)
  rcases hq with ⟨_h1, _h2, _h3, _h4, h5⟩
  have hbad := h5 rfl
  rcases hbad with hret | habsent
  · cases hret
  · exact habsent view101 targetViewAt_s8_3

theorem reloading_not_stagingStable : ¬ StagingStable s2 := by
  intro h
  have hf := h 1 cell1begun lookup_s2_1
  rcases hf with ha | ha
  · cases ha
  · rcases ha with hi | hf'
    · cases hi
    · cases hf'

/-! ### The R.base macro witnesses -/

abbrev cell4t : Cell := { cell4 with birth := 2 }
abbrev cell4u : Cell := { cell4 with component := { cell4.component with requires := ∅ }, birth := 2 }

abbrev t0 : State := allocate s5 4 cell4t
abbrev t1 : State := beginState rulesSem t0 4 view101 ()
abbrev t2 : State := finishState rulesSem t1 4 []

abbrev u0 : State := allocate s5 4 cell4u
abbrev u1 : State := beginState rulesSem u0 4 ∅ ()
abbrev u2 : State := finishState rulesSem u1 4 []
abbrev u3 : State := retireState u2 4
abbrev u4 : State := leaveState u3 4
abbrev u5 : State := unloadState u4 4

theorem stagingStable_t0 : StagingStable t0 := by
  intro name fiber hl
  have hmem : name ∈ t0.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
    rfl
  simp [t0, s5, s4, s3, s2, s1, finishState, iterState, beginState, editCell,
    allocate, beginPayload, iterPayload, rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
  rcases hmem with h4 | h1 | h2 | htail
  · subst name
    rw [show Finmap.lookup 4 t0.registry = some cell4t from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · subst name
    rw [show Finmap.lookup 1 t0.registry = some cell1active from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 2 t0.registry = some cell2 from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · rcases htail with h | hempty
    · subst name
      rw [show Finmap.lookup 1 t0.registry = some cell1active from by congr] at hl
      cases hl with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

theorem stagingStable_t2 : StagingStable t2 := by
  intro name fiber hl
  have hmem : name ∈ t2.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
    rfl
  simp [t2, t1, t0, s5, s4, s3, s2, s1, finishState, beginState, iterState, editCell,
    allocate, beginPayload, iterPayload, rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
  rcases hmem with h4 | h1 | h2 | htail
  · subst name
    rw [show Finmap.lookup 4 t2.registry = some { cell4t with phase := .active, committed := { entries := commitProjection t1 (∅ : Finset Nat) }, committedView := view101, payload := { cell4t.payload with iteratorCode := 0, accumulatorCode := [], flightCode := none, failureData := none } } from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 1 t2.registry = some cell1active from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 2 t2.registry = some cell2 from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · rcases htail with h | hempty
    · subst name
      rw [show Finmap.lookup 1 t2.registry = some cell1active from by congr] at hl
      cases hl with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

/-! ### The R.base macro steps and instances -/

theorem step_insert4t : OrchestrationRule (.insert none 4 cell4t) s5 t0 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 4) (child := cell4t)
    (by simp [s5, s4, s3, s2, s1, finishState, iterState, beginState, editCell,
      allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne])
    (by simp [s5, s4, s3, s2, s1, finishState, iterState, beginState, editCell,
      allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s5, s4, s3, s2, s1, nextBirth, finishState, iterState,
        beginState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem providesNow_t0 : ProvidesNow t0 1 10 :=
  ⟨_, by
    change Finmap.lookup 1 t0.registry = some cell1active
    congr, by
    change 10 ∈ (commitProjection t0 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem targetViewAt_t0_4 : TargetViewAt t0 4 view101 := by
  refine ⟨_, by
    change Finmap.lookup 4 t0.registry = some cell4t
    congr, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
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
      exact providesNow_t0
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

abbrev cell4tbegun : Cell := { cell4t with phase := .reloading, committedView := view101, payload := { cell4t.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }

theorem step_begin4t : LifecycleRule rulesSem (.begin 4 view101) t0 t1 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell4t)
    (hlook := by change Finmap.lookup 4 t0.registry = some cell4t; congr)
    (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_t0_4)
    (hlaunch := rfl)

theorem targetViewAt_t1_4 : TargetViewAt t1 4 view101 := by
  refine ⟨_, by
    change Finmap.lookup 4 t1.registry = some cell4tbegun
    congr, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
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
      exact providesNow_t0
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem step_finish4t : LifecycleRule rulesSem (.finish 4) t1 t2 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell4tbegun)
    (hlook := by change Finmap.lookup 4 t1.registry = some cell4tbegun; congr)
    (hphase := rfl)
    (htarget := targetViewAt_t1_4)
    (hstage := by change fixtureStage 0 t1 = some (.halt t1 []); rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

theorem step_insert4u : OrchestrationRule (.insert none 4 cell4u) s5 u0 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 4) (child := cell4u)
    (by simp [s5, s4, s3, s2, s1, finishState, iterState, beginState, editCell,
      allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne])
    (by simp [s5, s4, s3, s2, s1, finishState, iterState, beginState, editCell,
      allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s5, s4, s3, s2, s1, nextBirth, finishState, iterState,
        beginState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

abbrev cell4ubegun : Cell := { cell4u with phase := .reloading, committedView := ∅, payload := { cell4u.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }
abbrev cell4uactive : Cell := { cell4ubegun with phase := .active, committed := { entries := commitProjection u1 (∅ : Finset Nat) }, payload := { cell4ubegun.payload with accumulatorCode := [], flightCode := none, failureData := none } }

theorem step_begin4u : LifecycleRule rulesSem (.begin 4 ∅) u0 u1 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell4u)
    (hlook := by change Finmap.lookup 4 u0.registry = some cell4u; congr)
    (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cell4u, by change Finmap.lookup 4 u0.registry = some cell4u; congr, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_finish4u : LifecycleRule rulesSem (.finish 4) u1 u2 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell4ubegun)
    (hlook := by change Finmap.lookup 4 u1.registry = some cell4ubegun; congr)
    (hphase := rfl)
    (htarget := ⟨cell4ubegun, by change Finmap.lookup 4 u1.registry = some cell4ubegun; congr, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by change fixtureStage 0 u1 = some (.halt u1 []); rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

theorem step_retire4u : OrchestrationRule (.retire 4) u2 u3 := by
  exact OrchestrationRule.retire (by change Finmap.lookup 4 u2.registry = some cell4uactive; congr)

theorem step_leave4u : LifecycleRule rulesSem (.leave 4) u3 u4 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := { cell4uactive with retired := true })
    (hlook := by change Finmap.lookup 4 u3.registry = some { cell4uactive with retired := true }; congr)
    (hphase := rfl)
    (hchanged := by
      intro h
      rcases h with ⟨cell, hl, hret, _hkeys, _hall⟩
      rw [show Finmap.lookup 4 u3.registry = some { cell4uactive with retired := true } from by congr] at hl
      cases hl with | refl
      cases hret)

theorem step_unload4u : LifecycleRule rulesSem (.unload 4) u4 u5 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := { { cell4uactive with retired := true } with phase := .unloading })
    (hlook := by congr) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hl, _hkey, hkv⟩
      have hmem : dependent ∈ u4.registry.keys := by
        rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
        rfl
      simp [u4, u3, u2, u1, u0, s5, s4, s3, s2, s1, leaveState, retireState, finishState,
        beginState, iterState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.mem_keys, Finmap.mem_insert] at hmem
      rcases hmem with h4 | h1 | h2 | htail
      · subst dependent
        rw [show Finmap.lookup 4 u4.registry = some { { cell4uactive with retired := true } with phase := .unloading } from by congr] at hl
        cases hl with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · subst dependent
        rw [show Finmap.lookup 1 u4.registry = some cell1active from by congr] at hl
        cases hl with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · subst dependent
        rw [show Finmap.lookup 2 u4.registry = some cell2 from by congr] at hl
        cases hl with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rcases htail with h | hempty
        · subst dependent
          rw [show Finmap.lookup 1 u4.registry = some cell1active from by congr] at hl
          cases hl with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
          simp at hempty)
    (haccumulator := by change fixtureAccumulator [] u4 = some u4; rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

theorem stagingStable_u3 : StagingStable u3 := by
  intro name fiber hl
  have hmem : name ∈ u3.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
    rfl
  simp [u3, u2, u1, u0, s5, s4, s3, s2, s1, retireState, finishState, beginState, iterState,
    editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.mem_keys,
    Finmap.mem_insert] at hmem
  rcases hmem with h4 | h1 | h2 | htail
  · subst name
    rw [show Finmap.lookup 4 u3.registry = some { cell4uactive with retired := true } from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 1 u3.registry = some cell1active from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 2 u3.registry = some cell2 from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · rcases htail with h | hempty
    · subst name
      rw [show Finmap.lookup 1 u3.registry = some cell1active from by congr] at hl
      cases hl with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

theorem stagingStable_u5 : StagingStable u5 := by
  intro name fiber hl
  have hmem : name ∈ u5.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
    rfl
  simp [u5, u4, u3, u2, u1, u0, s5, s4, s3, s2, s1, unloadState, leaveState, retireState,
    finishState, beginState, iterState, editCell, allocate, beginPayload, iterPayload,
    rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
  rcases hmem with h4 | h1 | h2 | htail
  · subst name
    rw [show Finmap.lookup 4 u5.registry = some { { cell4uactive with retired := true } with phase := .inactive, committedView := ∅, payload := { cell4uactive.payload with flightCode := none } } from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · subst name
    rw [show Finmap.lookup 1 u5.registry = some cell1active from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 2 u5.registry = some cell2 from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · rcases htail with h | hempty
    · subst name
      rw [show Finmap.lookup 1 u5.registry = some cell1active from by congr] at hl
      cases hl with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

theorem baseReload_cell4 : baseLifecycleRule rulesSem (.reload 4 view101) ⟨t0, stagingStable_t0⟩ ⟨t2, stagingStable_t2⟩ := by
  rw [baseLife_reload_iff]
  refine ⟨t1, step_begin4t, step_finish4t⟩

theorem baseUnload_cell4 : baseLifecycleRule rulesSem (.unload 4) ⟨u3, stagingStable_u3⟩ ⟨u5, stagingStable_u5⟩ := by
  rw [baseLife_unload_iff]
  refine ⟨u4, step_leave4u, step_unload4u⟩

theorem reloadMiddle_not_stable : ¬ StagingStable t1 := by
  intro h
  have hf := h 4 cell4tbegun (by change Finmap.lookup 4 t1.registry = some cell4tbegun; congr)
  rcases hf with ha | ha
  · cases ha
  · rcases ha with hi | hf'
    · cases hi
    · cases hf'

theorem unloadMiddle_not_stable : ¬ StagingStable u4 := by
  intro h
  have hf := h 4 { { cell4uactive with retired := true } with phase := .unloading }
    (by congr)
  rcases hf with ha | ha
  · cases ha
  · rcases ha with hi | hf'
    · cases hi
    · cases hf'

/-! ### The nonconstant fixed-operation factorization -/

theorem factor_replay_nonconstant :
    ∃ label b1 b2 m1 m2, (∃ i1, SelectedBody rulesSem label b1 m1 i1) ∧
      (∃ i2, SelectedBody rulesSem label b2 m2 i2) ∧ m1 ≠ m2 := by
  refine ⟨.inr (.iter 1 0), s3, { s3 with ambient := 42 }, s3, { s3 with ambient := 42 }, ?_, ?_, ?_⟩
  · exact ⟨[2], ⟨cell1begun, lookup_s3_1, rfl,
      ⟨cell1begun, lookup_s3_1, rfl, by
        change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
        simp, by
        intro key provider hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv⟩,
      by change fixtureStage 1 s3 = some (.yield s3 [2] 0); rfl,
      by decide,
      by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp⟩⟩
  · exact ⟨[2], ⟨cell1begun, by
      change Finmap.lookup 1 { s3 with ambient := 42 }.registry = some cell1begun
      change Finmap.lookup 1 s3.registry = some cell1begun
      exact lookup_s3_1, rfl,
      ⟨cell1begun, by
        change Finmap.lookup 1 { s3 with ambient := 42 }.registry = some cell1begun
        change Finmap.lookup 1 s3.registry = some cell1begun
        exact lookup_s3_1, rfl, by
        change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
        simp, by
        intro key provider hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv⟩,
      by change fixtureStage 1 { s3 with ambient := 42 } = some (.yield { s3 with ambient := 42 } [2] 0); rfl,
      by decide,
      by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp⟩⟩
  · intro h
    have hh := congrArg (fun state : State => state.ambient) h
    change s3.ambient = { s3 with ambient := 42 }.ambient at hh
    change 10 = 42 at hh
    omega

/-! ### The A.async admissibility evidence -/

/-- The computable providers of a key: the installed active cells that declare
the key. Retired/left/unloading cells no longer provide. -/
def providersOf (state : State) (key : Nat) : Finset Nat :=
  (state.registry.entries.filterMap (fun e =>
    if key ∈ e.2.component.provides ∧ e.2.phase = .active then some e.1 else none)).toFinset

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
    (.inr (.divertAbort 3 .absent)) s18 := by
  change ∃ cell flight, Finmap.lookup 3 s18.registry = some cell ∧
    cell.payload.flightCode = some flight ∧ cell.phase = .reloading ∧
      boundaryRealizes s18 3 cell .absent ∧ rulesPolicy.allowed flight s18 .abort
  refine ⟨cell3begun, (), lookup_s18_3, rfl, rfl, targetAbsent_s18_3, ?_⟩
  change providersOf s18 10 = ∅
  decide

theorem divertLand_admissible : divertAdmissible rulesSem rulesPolicy
    (.inr (.divertLand 2 ())) s22 := by
  change ∃ cell flight, Finmap.lookup 2 s22.registry = some cell ∧
    cell.payload.flightCode = some flight ∧ flight = () ∧ cell.phase = .reloading ∧
      rulesPolicy.allowed flight s22 .land
  refine ⟨cell2itered, (), lookup_s22_2, rfl, rfl, rfl, ?_⟩
  trivial

/-! ### The ADR-09 cycle-trace candidate (r = 0, c = 1, n = 2; former provider p = 3) -/

abbrev view20p : Finmap (fun _ : Nat => Nat) := Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))

abbrev cellP : Cell :=
  { incarnation := 3, parent := none, birth := 0,
    component := { key := 3, requires := ∅, provides := {20}, actionCode := (), iteratorCode := 0, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 0, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cellR : Cell :=
  { incarnation := 0, parent := none, birth := 1,
    component := { key := 0, requires := {20}, provides := {10}, actionCode := (), iteratorCode := 0, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 0, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cellC : Cell :=
  { incarnation := 1, parent := some 0, birth := 2,
    component := { key := 1, requires := {20}, provides := ∅, actionCode := (), iteratorCode := 1, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cellN : Cell :=
  { incarnation := 2, parent := some 1, birth := 3,
    component := { key := 2, requires := {10}, provides := {20}, actionCode := (), iteratorCode := 1, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev c1 : State := allocate s0 3 cellP
abbrev c2 : State := beginState rulesSem c1 3 ∅ ()
abbrev c3 : State := finishState rulesSem c2 3 []
abbrev c4 : State := allocate c3 0 cellR
abbrev c5 : State := beginState rulesSem c4 0 view20p ()
abbrev c6 : State := finishState rulesSem c5 0 []
abbrev c7 : State := allocate c6 1 cellC
abbrev c8 : State := beginState rulesSem c7 1 view20p ()
abbrev c9 : State := iterState rulesSem c8 1 [2] 0
abbrev c10 : State := retireState c9 1
abbrev c11 : State := retireState c10 3
abbrev c12 : State := leaveState c11 3
abbrev c13 : State := divertLandState rulesSem { c12 with ambient := c12.ambient + 1 } 1 [7]
abbrev c14 : State := unloadState c13 1
abbrev c15 : State := leaveState c14 0
abbrev c16 : State := unloadState c15 0
abbrev c17 : State := unloadState c16 3
abbrev c18 : State := removeState c17 3
abbrev c19 : State := allocate c18 2 cellN

abbrev cellPbegun : Cell := { cellP with phase := .reloading, committedView := ∅, payload := { cellP.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }
abbrev cellPactive : Cell := { cellPbegun with phase := .active, committed := { entries := commitProjection c2 ({20} : Finset Nat) }, payload := { cellPbegun.payload with accumulatorCode := [], flightCode := none, failureData := none } }
abbrev cellPretired : Cell := { cellPactive with retired := true }
abbrev cellPunloading : Cell := { cellPretired with phase := .unloading }
abbrev cellPinactive : Cell := { cellPunloading with phase := .inactive, committedView := ∅, payload := { cellPunloading.payload with flightCode := none } }

abbrev cellRbegun : Cell := { cellR with phase := .reloading, committedView := view20p, payload := { cellR.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }
abbrev cellRactive : Cell := { cellRbegun with phase := .active, committed := { entries := commitProjection c5 ({10} : Finset Nat) }, payload := { cellRbegun.payload with accumulatorCode := [], flightCode := none, failureData := none } }
abbrev cellRleft : Cell := { cellRactive with phase := .unloading }
abbrev cellRinactive : Cell := { cellRleft with phase := .inactive, committedView := ∅, payload := { cellRleft.payload with flightCode := none } }

abbrev cellCbegun : Cell := { cellC with phase := .reloading, committedView := view20p, payload := { cellC.payload with iteratorCode := 1, accumulatorCode := [], flightCode := some () } }
abbrev cellCitered : Cell := { cellCbegun with payload := { cellCbegun.payload with iteratorCode := 0, accumulatorCode := [2] } }
abbrev cellCretired : Cell := { cellCitered with retired := true }
abbrev cellCunloading : Cell := { cellCretired with phase := .unloading, payload := { cellCretired.payload with accumulatorCode := [7,2], flightCode := none } }
abbrev cellCinactive : Cell := { cellCunloading with phase := .inactive, committedView := ∅, payload := { cellCunloading.payload with flightCode := none } }

theorem lookup_c2_3 : Finmap.lookup 3 c2.registry = some cellPbegun := by
  congr

theorem lookup_c3_3 : Finmap.lookup 3 c3.registry = some cellPactive := by
  congr

theorem lookup_c4_0 : Finmap.lookup 0 c4.registry = some cellR := by
  congr

theorem lookup_c5_0 : Finmap.lookup 0 c5.registry = some cellRbegun := by
  congr

theorem lookup_c6_0 : Finmap.lookup 0 c6.registry = some cellRactive := by
  congr

theorem lookup_c7_1 : Finmap.lookup 1 c7.registry = some cellC := by
  congr

theorem lookup_c8_1 : Finmap.lookup 1 c8.registry = some cellCbegun := by
  congr

theorem lookup_c9_1 : Finmap.lookup 1 c9.registry = some cellCitered := by
  congr

theorem lookup_c10_1 : Finmap.lookup 1 c10.registry = some cellCretired := by
  congr

theorem lookup_c12_3 : Finmap.lookup 3 c12.registry = some cellPunloading := by
  congr

theorem lookup_c13_3 : Finmap.lookup 3 c13.registry = some cellPunloading := by
  congr

theorem lookup_c13_1 : Finmap.lookup 1 c13.registry = some cellCunloading := by
  congr

theorem lookup_c14_3 : Finmap.lookup 3 c14.registry = some cellPunloading := by
  congr

theorem lookup_c15_0 : Finmap.lookup 0 c15.registry = some cellRleft := by
  congr

theorem lookup_c16_0 : Finmap.lookup 0 c16.registry = some cellRinactive := by
  congr

theorem lookup_c15_3 : Finmap.lookup 3 c15.registry = some cellPunloading := by
  congr

theorem lookup_c17_0 : Finmap.lookup 0 c17.registry = some cellRinactive := by
  congr

theorem lookup_c16_3 : Finmap.lookup 3 c16.registry = some cellPunloading := by
  congr

theorem lookup_c17_3 : Finmap.lookup 3 c17.registry = some cellPinactive := by
  congr

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
  · simp [allocate, removeState, unloadState, leaveState, divertLandState, retireState, iterState, finishState, beginState, editCell, hd0, hd1, hd2, hd3]

theorem cycleStep_insertP : OrchestrationRule (.insert none 3 cellP) s0 c1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 3) (child := cellP)
    (by simp []) (by decide)
    (by simp [CanonicalInitialCell, nextBirth])
    (by intro name cell' h; simp [] at h)

theorem cycleStep_beginP : LifecycleRule rulesSem (.begin 3 ∅) c1 c2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellP)
    (hlook := by change Finmap.lookup 3 c1.registry = some cellP; congr)
    (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cellP, by change Finmap.lookup 3 c1.registry = some cellP; congr, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem cycleStep_finishP : LifecycleRule rulesSem (.finish 3) c2 c3 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellPbegun)
    (hlook := lookup_c2_3) (hphase := rfl)
    (htarget := ⟨cellPbegun, lookup_c2_3, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by change fixtureStage 0 c2 = some (.halt c2 []); rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ ({20} : Finset Nat); simp)

theorem provides20_c3 : ProvidesNow c3 3 20 :=
  ⟨_, lookup_c3_3, by
    change 20 ∈ (commitProjection c2 ({20} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 20 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem cycleStep_insertR : OrchestrationRule (.insert none 0 cellR) c3 c4 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 0) (child := cellR)
    (by simp [c3, c2, c1, finishState, beginState, editCell, allocate, beginPayload, rulesSem, Finmap.lookup_insert])
    (by simp [c3, c2, c1, finishState, beginState, editCell, allocate, beginPayload, rulesSem])
    (by
      simp [CanonicalInitialCell, c3, c2, c1, nextBirth, finishState, beginState, editCell, allocate, beginPayload, rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        by_cases hname : name = 3
        · subst name
          rw [lookup_c3_3] at h
          cases h with | refl
          apply Finset.disjoint_left.mpr
          intro key hkey
          change key ∈ cellR.component.provides at hkey
          rw [cellR] at hkey
          simp at hkey
          subst key
          intro hk
          rw [cellPactive] at hk
          simp at hk
        · simp [c3, c2, c1, finishState, beginState, editCell, allocate, beginPayload, rulesSem, Finmap.lookup_insert, hname] at h)

theorem cycleTargetViewAt_c4_0 : TargetViewAt c4 0 view20p := by
  refine ⟨_, lookup_c4_0, ?_, ?_, ?_⟩
  · rfl
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

theorem cycleStep_beginR : LifecycleRule rulesSem (.begin 0 view20p) c4 c5 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellR)
    (hlook := lookup_c4_0) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := cycleTargetViewAt_c4_0)
    (hlaunch := rfl)

theorem cycleStep_finishR : LifecycleRule rulesSem (.finish 0) c5 c6 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellRbegun)
    (hlook := lookup_c5_0) (hphase := rfl)
    (htarget := ⟨cellRbegun, lookup_c5_0, rfl, by
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
      · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
        cases hkv⟩)
    (hstage := by change fixtureStage 0 c5 = some (.halt c5 []); rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)

theorem cycleStep_insertC : OrchestrationRule (.insert (some 0) 1 cellC) c6 c7 := by
  exact OrchestrationRule.insert (registrar := some 0) (fresh := 1) (child := cellC)
    (by simp [c6, c5, c4, c3, c2, c1, finishState, beginState, editCell, allocate, beginPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty])
    (by simp [c6, c5, c4, c3, c2, c1, finishState, beginState, editCell, allocate, beginPayload, rulesSem])
    (by
      simp [CanonicalInitialCell, Registered, c6, c5, c4, c3, c2, c1, nextBirth, finishState, beginState, editCell, allocate, beginPayload, rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem cycleTargetViewAt_c7_1 : TargetViewAt c7 1 view20p := by
  refine ⟨_, lookup_c7_1, ?_, ?_, ?_⟩
  · rfl
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

theorem cycleStep_beginC : LifecycleRule rulesSem (.begin 1 view20p) c7 c8 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellC)
    (hlook := lookup_c7_1) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := cycleTargetViewAt_c7_1)
    (hlaunch := rfl)

theorem cycleStep_iterC : LifecycleRule rulesSem (.iter 1 0) c8 c9 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellCbegun)
    (hlook := lookup_c8_1) (hphase := rfl)
    (htarget := ⟨cellCbegun, lookup_c8_1, rfl, by
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
      · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
        cases hkv⟩)
    (hstage := by change fixtureStage 1 c8 = some (.yield c8 [2] 0); rfl)
    (hrank := by decide)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

theorem cycleStep_retireC : OrchestrationRule (.retire 1) c9 c10 := by
  exact OrchestrationRule.retire lookup_c9_1

theorem cycleStep_retireP : OrchestrationRule (.retire 3) c10 c11 := by
  exact OrchestrationRule.retire (by congr)

theorem cycleStep_leaveP : LifecycleRule rulesSem (.leave 3) c11 c12 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cellPretired)
    (hlook := by change Finmap.lookup 3 c11.registry = some cellPretired; congr)
    (hphase := rfl)
    (hchanged := by
      intro h
      rcases h with ⟨cell, hl, hret, _hkeys, _hall⟩
      rw [show Finmap.lookup 3 c11.registry = some cellPretired from by congr] at hl
      cases hl with | refl
      cases hret)

theorem cycleTargetNot_c12_1 : ¬ TargetViewAt c12 1 view20p := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow c12 3 20 := hall 20 3 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_c12_3] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem cycleStep_divertLandC : LifecycleRule rulesSem (.divertLand 1 ()) c12 c13 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cellCretired)
    (hlook := by change Finmap.lookup 1 c12.registry = some cellCretired; congr)
    (hphase := rfl) (htoken := rfl)
    (hchanged := cycleTargetNot_c12_1)
    (hland := by
      change fixtureLanding () c12 = some (.landed { c12 with ambient := c12.ambient + 1 } [7])
      rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

theorem cycleStep_unloadC : LifecycleRule rulesSem (.unload 1) c13 c14 := by
  have hnone7 : Finmap.lookup 7 c13.registry = none := by
    simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, divertLandState, leaveState,
      retireState, iterState, finishState, beginState, editCell, allocate, beginPayload, iterPayload,
      rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty]
  have hnone2 : Finmap.lookup 2 c13.registry = none := by
    simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, divertLandState, leaveState,
      retireState, iterState, finishState, beginState, editCell, allocate, beginPayload, iterPayload,
      rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty]
  have hfold : foldRetire [7,2] c13 = c13 := by
    rw [foldRetire_cons_none hnone7, foldRetire_cons_none hnone2, foldRetire_absent]
    intro n hn
    cases hn
  rw [show c14 = unloadState (foldRetire [7,2] c13) 1 from by rw [hfold]]
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellCunloading)
    (hlook := lookup_c13_1) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hl, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd3 : dependent = 3
        · subst dependent
          rw [lookup_c13_3] at hl
          cases hl with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · by_cases hd0 : dependent = 0
          · subst dependent
            rw [show Finmap.lookup 0 c13.registry = some cellRactive from by congr] at hl
            cases hl with | refl
            by_cases hk : key = 20
            · subst key
              rw [Finmap.lookup_insert] at hkv
              have h31 : (3 : Nat) = 1 := Option.some.inj hkv
              omega
            · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
              cases hkv
          · have hnone : Finmap.lookup dependent c13.registry = none := by
              simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, divertLandState, leaveState, retireState, iterState, finishState, beginState, editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty, hd1, hd3, hd0]
            rw [hnone] at hl
            cases hl)
    (haccumulator := by
      change fixtureAccumulator [7,2] c13 = some (foldRetire [7,2] c13)
      rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

theorem cycleTargetNot_c14_0 : ¬ TargetViewAt c14 0 view20p := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow c14 3 20 := hall 20 3 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_c14_3] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem cycleStep_leaveR : LifecycleRule rulesSem (.leave 0) c14 c15 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cellRactive)
    (hlook := by change Finmap.lookup 0 c14.registry = some cellRactive; congr)
    (hphase := rfl)
    (hchanged := cycleTargetNot_c14_0)

theorem cycleStep_unloadR : LifecycleRule rulesSem (.unload 0) c15 c16 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellRleft)
    (hlook := lookup_c15_0) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hl, _hkey, hkv⟩
      by_cases hd0 : dependent = 0
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd1 : dependent = 1
        · subst dependent
          rw [show Finmap.lookup 1 c15.registry = some cellCinactive from by congr] at hl
          cases hl with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            rw [lookup_c15_3] at hl
            cases hl with | refl
            rw [Finmap.lookup_empty] at hkv
            cases hkv
          · have hnone : Finmap.lookup dependent c15.registry = none := by
              simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, leaveState, unloadState, divertLandState, retireState, iterState, finishState, beginState, editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty, hd0, hd1, hd3]
            rw [hnone] at hl
            cases hl)
    (haccumulator := by change fixtureAccumulator [] c15 = some c15; rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)

theorem cycleStep_unloadP : LifecycleRule rulesSem (.unload 3) c16 c17 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellPunloading)
    (hlook := lookup_c16_3) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hl, _hkey, hkv⟩
      by_cases hd3 : dependent = 3
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd0 : dependent = 0
        · subst dependent
          rw [lookup_c16_0] at hl
          cases hl with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · by_cases hd1 : dependent = 1
          · subst dependent
            rw [show Finmap.lookup 1 c16.registry = some cellCinactive from by congr] at hl
            cases hl with | refl
            rw [Finmap.lookup_empty] at hkv
            cases hkv
          · have hnone : Finmap.lookup dependent c16.registry = none := by
              simp [c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, unloadState, leaveState, divertLandState, retireState, iterState, finishState, beginState, editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty, hd3, hd0, hd1]
            rw [hnone] at hl
            cases hl)
    (haccumulator := by change fixtureAccumulator [] c16 = some c16; rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ ({20} : Finset Nat); simp)

theorem cycleStep_removeP : OrchestrationRule (.remove 3) c17 c18 := by
  exact OrchestrationRule.remove (cell := cellPinactive) (hlook := lookup_c17_3)
    (hretired := rfl) (hphase := by left; rfl) (hnoChild := by
      intro name cell' h hparent
      by_cases hd0 : name = 0
      · subst name
        rw [lookup_c17_0] at h
        cases h with | refl
        cases hparent
      · by_cases hd1 : name = 1
        · subst name
          rw [show Finmap.lookup 1 c17.registry = some cellCinactive from by congr] at h
          cases h with | refl
          cases hparent
        · by_cases hd3 : name = 3
          · subst name
            rw [lookup_c17_3] at h
            cases h with | refl
            cases hparent
          · have hnone : Finmap.lookup name c17.registry = none := by
              simp [c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, unloadState, leaveState, divertLandState, retireState, iterState, finishState, beginState, editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty, hd0, hd1, hd3]
            rw [hnone] at h
            cases h)

theorem cycleStep_insertN : OrchestrationRule (.insert (some 1) 2 cellN) c18 c19 := by
  exact OrchestrationRule.insert (registrar := some 1) (fresh := 2) (child := cellN)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, Registered, removeState, unloadState, leaveState, divertLandState,
        retireState, iterState, finishState, beginState, editCell, allocate,
        beginPayload, iterPayload, rulesSem]
      rfl)
    (by intro name cell' h
        by_cases hd1 : name = 1
        · subst name
          simp [removeState, unloadState, leaveState, divertLandState, retireState, iterState,
            finishState, beginState, editCell, allocate, beginPayload, iterPayload,
            rulesSem] at h
          have hcell' : cell' = cellCinactive := h.symm
          subst cell'
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
          subst key
          intro hk
          change 20 ∈ (∅ : Finset Nat) at hk
          simp at hk
        · by_cases hd0 : name = 0
          · subst name
            simp [removeState, unloadState, leaveState, divertLandState, retireState, iterState,
              finishState, beginState, editCell, allocate, beginPayload, iterPayload,
              rulesSem] at h
            have hcell' : cell' = cellRinactive := h.symm
            subst cell'
            apply Finset.disjoint_left.mpr
            intro key hkey
            change key ∈ cellN.component.provides at hkey
            rw [cellN] at hkey
            simp at hkey
            subst key
            intro hk
            change 20 ∈ ({10} : Finset Nat) at hk
            simp at hk
          · have hnone : Finmap.lookup name c18.registry = none := by
              by_cases hd3 : name = 3
              · subst name
                rfl
              · by_cases hd2 : name = 2
                · subst name
                  decide
                · simp [removeState, unloadState, leaveState, divertLandState, retireState,
                    iterState, finishState, beginState, editCell, allocate, hd1, hd0, hd3]
            rw [hnone] at h
            cases h)

/-! ### The cycle-endpoint facts -/

theorem cycleEndpoint_parentEdges :
    (Finmap.lookup 1 c19.registry).isSome ∧
      (∀ cell, Finmap.lookup 1 c19.registry = some cell → cell.parent = some 0) ∧
      (∀ cell, Finmap.lookup 2 c19.registry = some cell → cell.parent = some 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lookup_c19_1]
    rfl
  · intro _ h
    rw [lookup_c19_1] at h
    cases h with | refl
    rfl
  · intro _ h
    rw [lookup_c19_2] at h
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
    rw [lookup_c19_2] at h
    cases h with | refl
    rw [cellN]
    simp
  · intro cell h
    rw [lookup_c19_0] at h
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
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      decide
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        decide
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          decide
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · decide

def cycleProfile : WellFormedProfile Nat Nat Nat Unit Nat (List Nat) Unit Nat Nat :=
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
      rw [Finmap.mem_keys, ← Finmap.lookup_isSome, lookup_c19_0]
      rfl
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        change 1 ∈ c19.registry.keys
        rw [Finmap.mem_keys, ← Finmap.lookup_isSome, lookup_c19_1]
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
    change key ∈ cellRactive.committed.entries.keys at hkey
    change key ∈ (commitProjection c5 ({10} : Finset Nat)).keys at hkey
    rw [commitProjection_mem_keys_iff] at hkey
    exact hkey.1
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key hkey
      change key ∈ cellCinactive.committed.entries.keys at hkey
      rw [cellCinactive, cellCunloading, cellCretired, cellCitered, cellCbegun, cellC] at hkey
      simp at hkey
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key hkey
        change key ∈ cellN.committed.entries.keys at hkey
        rw [cellN] at hkey
        simp at hkey
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
      change key ∈ cellR.component.provides at hkey
      rw [cellR] at hkey
      simp at hkey
      subst key
      intro h
      rw [cellCinactive] at h
      simp at h
    · by_cases hd2b : b = 2
      · subst b
        rw [lookup_c19_2] at hb
        cases hb with | refl
        apply Finset.disjoint_left.mpr
        intro key hkey
        change key ∈ cellR.component.provides at hkey
        rw [cellR] at hkey
        simp at hkey
        subst key
        intro h
        rw [cellN] at h
        simp at h
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
        change key ∈ cellC.component.provides at hkey
        rw [cellC] at hkey
        simp at hkey
      · by_cases hd2b : b = 2
        · subst b
          rw [lookup_c19_2] at hb
          cases hb with | refl
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
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
          change key ∈ cellN.component.provides at hkey
          rw [cellN] at hkey
          simp at hkey
          subst key
          intro h
          rw [cellRinactive] at h
          simp at h
        · by_cases hd1b : b = 1
          · subst b
            rw [lookup_c19_1] at hb
            cases hb with | refl
            apply Finset.disjoint_left.mpr
            intro key hkey
            simp at hkey
            subst key
            intro h
            rw [cellCinactive] at h
            simp at h
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
      simp [allocate, removeState, unloadState, leaveState, divertLandState, retireState,
        iterState, finishState, beginState, editCell, iterPayload] at hhist
      rcases hhist with h3 | h0 | h1 | h2
      all_goals
        subst name; decide

theorem cycleEndpoint_wellFormed : WellFormed cycleProfile c19 :=
  ⟨c19_parentClosed, c19_parentAcyclic, c19_tableConfined, c19_provisionDisjoint,
    c19_committedViewClosed, c19_committedProvidersClosed, c19_dataCoherent,
    trivial, trivial, trivial⟩

end

end STC.Examples.GlobalRules
