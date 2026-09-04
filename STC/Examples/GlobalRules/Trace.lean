module

public import STC.Examples.GlobalRules.Semantics

/-!
# Global rule trace witnesses

The finite state chain s0..s27, per-state cell facts, provider and target
views, and the twenty-seven authoritative step witnesses over two acting
fibers.
-/

namespace STC.Examples.GlobalRules

open STC STC.State STC.Control

@[expose] public section

/-! ### Main fixture: state chain -/

abbrev view101 : Finmap (fun _ : Nat => Nat) := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))

abbrev s1 : State := allocate s0 1 cell1
abbrev s2 : State := beginState rulesSem s1 1 ∅ ()
abbrev s3 : State := allocate s2 2 cell2
abbrev s4 : State := iterState rulesSem s3 1 [2] 0
abbrev s5 : State := finishState rulesSem s4 1 []
abbrev s6 : State := beginState rulesSem s5 2 view101 ()
abbrev s7 : State := iterState rulesSem s6 2 [] 2
abbrev s8 : State := allocate s7 3 cell3
abbrev s9 : State := beginState rulesSem s8 3 view101 ()
abbrev s10 : State := allocate s9 4 cell4
abbrev s11 : State := beginState rulesSem s10 4 view101 ()
abbrev s12 : State := finishState rulesSem s11 4 []
abbrev s13 : State := allocate s12 5 cell5
abbrev s14 : State := beginState rulesSem s13 5 view101 ()
abbrev s15 : State := raiseState s14 5 7
abbrev s16 : State := unloadState s15 5
abbrev s17 : State := retireState s16 1
abbrev s18 : State := leaveState s17 1
abbrev s19 : State := divertAbortState s18 3
abbrev s20 : State := unloadState s19 3
abbrev s21 : State := retireState s20 3
abbrev s22 : State := removeState s21 3
abbrev s23 : State := divertLandState rulesSem { s22 with ambient := s22.ambient + 1 } 2 [7]
abbrev s24 : State := leaveState s23 4
abbrev s25 : State := unloadState s24 4
abbrev s26 : State := unloadState s25 2
abbrev s27 : State := unloadState (foldRetire [2] s26) 1

/-! ### Per-state cell facts -/

abbrev cell1begun : Cell := { cell1 with phase := .reloading, committedView := ∅, payload := { cell1.payload with iteratorCode := 1, accumulatorCode := [], flightCode := some () } }
abbrev cell1itered : Cell := { cell1begun with payload := { cell1begun.payload with iteratorCode := 0, accumulatorCode := [2] } }
abbrev cell1active : Cell := { cell1itered with phase := .active, committed := { entries := commitProjection s4 ({10} : Finset Nat) }, payload := { cell1itered.payload with accumulatorCode := [2], flightCode := none, failureData := none } }
abbrev cell1retired : Cell := { cell1active with retired := true }
abbrev cell1unloading : Cell := { cell1retired with phase := .unloading }
abbrev cell1inactive : Cell := { cell1unloading with phase := .inactive, committedView := ∅, payload := { cell1unloading.payload with flightCode := none } }

abbrev cell2begun : Cell := { cell2 with phase := .reloading, committedView := view101, payload := { cell2.payload with iteratorCode := 3, accumulatorCode := [], flightCode := some () } }
abbrev cell2itered : Cell := { cell2begun with payload := { cell2begun.payload with iteratorCode := 2, accumulatorCode := [] } }
abbrev cell2unloading : Cell := { cell2itered with phase := .unloading, payload := { cell2itered.payload with accumulatorCode := [7], flightCode := none } }
abbrev cell2inactive : Cell := { cell2unloading with phase := .inactive, committedView := ∅, payload := { cell2unloading.payload with flightCode := none } }
abbrev cell2retiredInactive : Cell := { cell2inactive with retired := true }

abbrev cell3begun : Cell := { cell3 with phase := .reloading, committedView := view101, payload := { cell3.payload with iteratorCode := 1, accumulatorCode := [], flightCode := some () } }
abbrev cell3unloading : Cell := { cell3begun with phase := .unloading }
abbrev cell3inactive : Cell := { cell3 with phase := .inactive, committedView := ∅, payload := { cell3.payload with flightCode := none } }
abbrev cell3retired : Cell := { cell3inactive with retired := true }

abbrev cell4begun : Cell := { cell4 with phase := .reloading, committedView := view101, payload := { cell4.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }
abbrev cell4active : Cell := { cell4begun with phase := .active, committed := { entries := commitProjection s11 (∅ : Finset Nat) }, payload := { cell4begun.payload with accumulatorCode := [], flightCode := none, failureData := none } }
abbrev cell4unloading : Cell := { cell4active with phase := .unloading }
abbrev cell4inactive : Cell := { cell4unloading with phase := .inactive, committedView := ∅, payload := { cell4unloading.payload with flightCode := none } }

abbrev cell5begun : Cell := { cell5 with phase := .reloading, committedView := view101, payload := { cell5.payload with iteratorCode := 99, accumulatorCode := [], flightCode := some () } }
abbrev cell5unloading : Cell := { cell5begun with phase := .unloading, payload := { cell5begun.payload with failureData := some 7 } }
abbrev cell5failed : Cell := { cell5unloading with phase := .failed, committedView := ∅, payload := { cell5unloading.payload with flightCode := none } }

theorem lookup_s1_1 : Finmap.lookup 1 s1.registry = some cell1 := by
  congr

theorem lookup_s2_1 : Finmap.lookup 1 s2.registry = some cell1begun := by
  congr

theorem lookup_s3_1 : Finmap.lookup 1 s3.registry = some cell1begun := by
  congr

theorem lookup_s4_1 : Finmap.lookup 1 s4.registry = some cell1itered := by
  congr

theorem lookup_s5_1 : Finmap.lookup 1 s5.registry = some cell1active := by
  congr

theorem lookup_s5_2 : Finmap.lookup 2 s5.registry = some cell2 := by
  congr

theorem lookup_s6_1 : Finmap.lookup 1 s6.registry = some cell1active := by
  congr

theorem lookup_s6_2 : Finmap.lookup 2 s6.registry = some cell2begun := by
  congr

theorem lookup_s7_2 : Finmap.lookup 2 s7.registry = some cell2itered := by
  congr

theorem lookup_s8_3 : Finmap.lookup 3 s8.registry = some cell3 := by
  congr

theorem lookup_s9_3 : Finmap.lookup 3 s9.registry = some cell3begun := by
  congr

theorem lookup_s10_4 : Finmap.lookup 4 s10.registry = some cell4 := by
  congr

theorem lookup_s11_4 : Finmap.lookup 4 s11.registry = some cell4begun := by
  congr

theorem lookup_s12_4 : Finmap.lookup 4 s12.registry = some cell4active := by
  congr

theorem lookup_s13_5 : Finmap.lookup 5 s13.registry = some cell5 := by
  congr

theorem lookup_s14_5 : Finmap.lookup 5 s14.registry = some cell5begun := by
  congr

theorem lookup_s15_5 : Finmap.lookup 5 s15.registry = some cell5unloading := by
  congr

theorem lookup_s16_5 : Finmap.lookup 5 s16.registry = some cell5failed := by
  congr

theorem lookup_s17_1 : Finmap.lookup 1 s17.registry = some cell1retired := by
  congr

theorem lookup_s18_1 : Finmap.lookup 1 s18.registry = some cell1unloading := by
  congr

theorem lookup_s18_3 : Finmap.lookup 3 s18.registry = some cell3begun := by
  congr

theorem lookup_s19_3 : Finmap.lookup 3 s19.registry = some cell3unloading := by
  congr

theorem lookup_s20_3 : Finmap.lookup 3 s20.registry = some cell3inactive := by
  congr

theorem lookup_s21_3 : Finmap.lookup 3 s21.registry = some cell3retired := by
  congr

theorem lookup_s22_2 : Finmap.lookup 2 s22.registry = some cell2itered := by
  congr

theorem lookup_s23_2 : Finmap.lookup 2 s23.registry = some cell2unloading := by
  congr

theorem lookup_s23_4 : Finmap.lookup 4 s23.registry = some cell4active := by
  congr

theorem lookup_s24_4 : Finmap.lookup 4 s24.registry = some cell4unloading := by
  congr

theorem lookup_s25_4 : Finmap.lookup 4 s25.registry = some cell4inactive := by
  congr

theorem lookup_s25_2 : Finmap.lookup 2 s25.registry = some cell2unloading := by
  congr

theorem lookup_s26_2 : Finmap.lookup 2 s26.registry = some cell2inactive := by
  congr

theorem lookup_s26_1 : Finmap.lookup 1 s26.registry = some cell1unloading := by
  congr

theorem lookup_s27_1 : Finmap.lookup 1 s27.registry = some cell1inactive := by
  congr

theorem lookup_s27_2 : Finmap.lookup 2 s27.registry = some cell2retiredInactive := by
  congr

/-! ### Provider and target views -/

theorem commitProjection_mem_keys_iff (state : State) (provides : Finset Nat) (key : Nat) :
    key ∈ (commitProjection state provides).keys ↔ key ∈ provides ∧ key ∈ state.coeffects.keys := by
  constructor
  · intro h
    exact ⟨commitProjection_keys_subset state provides h, by
      rw [Finmap.mem_keys] at h
      rw [Finmap.mem_def] at h
      change key ∈ Multiset.map Sigma.fst (Multiset.filter (fun entry => entry.1 ∈ provides) state.coeffects.entries) at h
      rw [Multiset.mem_map] at h
      rcases h with ⟨entry, hmem, hfst⟩
      rw [Multiset.mem_filter] at hmem
      rw [Finmap.mem_keys, Finmap.mem_def]
      change key ∈ Multiset.map Sigma.fst state.coeffects.entries
      rw [Multiset.mem_map]
      exact ⟨entry, hmem.1, hfst⟩⟩
  · intro h
    rw [Finmap.mem_keys, Finmap.mem_def]
    change key ∈ Multiset.map Sigma.fst (Multiset.filter (fun entry => entry.1 ∈ provides) state.coeffects.entries)
    rw [Multiset.mem_map]
    rcases h with ⟨hprov, hkeys⟩
    rw [Finmap.mem_keys, Finmap.mem_def] at hkeys
    change key ∈ Multiset.map Sigma.fst state.coeffects.entries at hkeys
    rw [Multiset.mem_map] at hkeys
    rcases hkeys with ⟨entry, hmem, hfst⟩
    exact ⟨entry, by rw [Multiset.mem_filter]; exact ⟨hmem, by rwa [hfst]⟩, hfst⟩

theorem providesNow_s5 : ProvidesNow s5 1 10 :=
  ⟨_, lookup_s5_1, by
    change 10 ∈ (commitProjection s4 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem providesNow_s6 : ProvidesNow s6 1 10 :=
  ⟨_, lookup_s6_1, by
    change 10 ∈ (commitProjection s6 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem targetViewAt_s5_2 : TargetViewAt s5 2 view101 := by
  refine ⟨_, lookup_s5_2, ?_, ?_, ?_⟩
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
      exact providesNow_s5
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s6_2 : TargetViewAt s6 2 view101 := by
  refine ⟨_, lookup_s6_2, ?_, ?_, ?_⟩
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
      exact providesNow_s5
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s8_3 : TargetViewAt s8 3 view101 := by
  refine ⟨_, lookup_s8_3, ?_, ?_, ?_⟩
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
      exact providesNow_s6
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s10_4 : TargetViewAt s10 4 view101 := by
  refine ⟨_, lookup_s10_4, ?_, ?_, ?_⟩
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
      exact providesNow_s6
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s13_5 : TargetViewAt s13 5 view101 := by
  refine ⟨_, lookup_s13_5, ?_, ?_, ?_⟩
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
      exact providesNow_s6
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv


theorem lookup_s11_1 : Finmap.lookup 1 s11.registry = some cell1active := by
  congr

theorem lookup_s18_2 : Finmap.lookup 2 s18.registry = some cell2itered := by
  congr

theorem lookup_s18_4 : Finmap.lookup 4 s18.registry = some cell4active := by
  congr

theorem lookup_s18_5 : Finmap.lookup 5 s18.registry = some cell5failed := by
  congr

theorem lookup_s21_1 : Finmap.lookup 1 s21.registry = some cell1unloading := by
  congr

theorem lookup_s21_2 : Finmap.lookup 2 s21.registry = some cell2itered := by
  congr

theorem lookup_s21_4 : Finmap.lookup 4 s21.registry = some cell4active := by
  congr

theorem lookup_s21_5 : Finmap.lookup 5 s21.registry = some cell5failed := by
  congr

theorem lookup_s23_1 : Finmap.lookup 1 s23.registry = some cell1unloading := by
  congr

theorem lookup_s15_1 : Finmap.lookup 1 s15.registry = some cell1active := by
  congr

theorem lookup_s15_2 : Finmap.lookup 2 s15.registry = some cell2itered := by
  congr

theorem lookup_s15_3 : Finmap.lookup 3 s15.registry = some cell3begun := by
  congr

theorem lookup_s15_4 : Finmap.lookup 4 s15.registry = some cell4active := by
  congr

theorem lookup_s19_5 : Finmap.lookup 5 s19.registry = some cell5failed := by
  congr

theorem lookup_s16_1 : Finmap.lookup 1 s16.registry = some cell1active := by
  congr

theorem lookup_s16_2 : Finmap.lookup 2 s16.registry = some cell2itered := by
  congr

theorem lookup_s16_3 : Finmap.lookup 3 s16.registry = some cell3begun := by
  congr

theorem lookup_s16_4 : Finmap.lookup 4 s16.registry = some cell4active := by
  congr

theorem lookup_s19_1 : Finmap.lookup 1 s19.registry = some cell1unloading := by
  congr

theorem lookup_s19_2 : Finmap.lookup 2 s19.registry = some cell2itered := by
  congr

theorem lookup_s19_4 : Finmap.lookup 4 s19.registry = some cell4active := by
  congr

theorem lookup_s22_1 : Finmap.lookup 1 s22.registry = some cell1unloading := by
  congr

theorem lookup_s22_4 : Finmap.lookup 4 s22.registry = some cell4active := by
  congr

theorem lookup_s24_1 : Finmap.lookup 1 s24.registry = some cell1unloading := by
  congr

theorem lookup_s24_2 : Finmap.lookup 2 s24.registry = some cell2unloading := by
  congr

theorem lookup_s24_5 : Finmap.lookup 5 s24.registry = some cell5failed := by
  congr

theorem lookup_s25_1 : Finmap.lookup 1 s25.registry = some cell1unloading := by
  congr

theorem lookup_s25_5 : Finmap.lookup 5 s25.registry = some cell5failed := by
  congr

theorem lookup_s26_4 : Finmap.lookup 4 s26.registry = some cell4inactive := by
  congr

theorem lookup_s26_5 : Finmap.lookup 5 s26.registry = some cell5failed := by
  congr

theorem providesNow_s11 : ProvidesNow s11 1 10 :=
  ⟨_, lookup_s11_1, by
    change 10 ∈ (commitProjection s11 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem targetViewAt_s11_4 : TargetViewAt s11 4 view101 := by
  refine ⟨_, lookup_s11_4, ?_, ?_, ?_⟩
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
      exact providesNow_s11
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem noProvides10_s18 : ∀ p, ¬ ProvidesNow s18 p 10 := by
  intro p h
  rcases h with ⟨cell, hlook, htable, hphase⟩
  by_cases hp1 : p = 1
  · subst p
    rw [lookup_s18_1] at hlook
    cases hlook with | refl
    simp at hphase
  · by_cases hp2 : p = 2
    · subst p
      rw [lookup_s18_2] at hlook
      cases hlook with | refl
      change 10 ∈ cell2itered.committed.entries.keys at htable
      simp at htable
    · by_cases hp3 : p = 3
      · subst p
        rw [lookup_s18_3] at hlook
        cases hlook with | refl
        change 10 ∈ cell3begun.committed.entries.keys at htable
        simp at htable
      · by_cases hp4 : p = 4
        · subst p
          rw [lookup_s18_4] at hlook
          cases hlook with | refl
          change 10 ∈ (commitProjection s11 (∅ : Finset Nat)).keys at htable
          rw [commitProjection_mem_keys_iff] at htable
          simp at htable
        · by_cases hp5 : p = 5
          · subst p
            rw [lookup_s18_5] at hlook
            cases hlook with | refl
            simp at hphase
          · have hnone : Finmap.lookup p s18.registry = none := by
              simp [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
                leaveState, retireState, unloadState, raiseState, beginState, finishState, iterState,
                editCell, allocate, beginPayload, iterPayload, rulesSem,
                Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty,
                hp1, hp2, hp3, hp4, hp5]
            simp [hnone] at hlook

theorem targetAbsent_s18_3 : TargetAbsent s18 3 := by
  intro ω h
  rcases h with ⟨cell, hlook, _hret, hkeys, hall⟩
  rw [lookup_s18_3] at hlook
  cases hlook with | refl
  have hmem : 10 ∈ ω.keys := by
    rw [hkeys]
    change 10 ∈ cell3.component.requires
    rw [cell3]
    simp
  have hisome : (Finmap.lookup 10 ω).isSome := by
    rw [Finmap.lookup_isSome, ← Finmap.mem_keys]
    exact hmem
  cases hlook10 : Finmap.lookup 10 ω with
  | none => simp [hlook10] at hisome
  | some provider =>
      have hprov : ProvidesNow s18 provider 10 := hall 10 provider hlook10
      exact noProvides10_s18 provider hprov

theorem targetNot_s22_2 : ¬ TargetViewAt s22 2 view101 := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow s22 1 10 := hall 10 1 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_s22_1] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem targetNot_s23_4 : ¬ TargetViewAt s23 4 view101 := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow s23 1 10 := hall 10 1 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_s23_1] at hlook'
  cases hlook' with | refl
  simp at hphase

/-- The pure control edit never touches a foreign cell. -/
theorem editCell_lookup_ne (state : State) (owner : Nat) (edit : Cell → Cell) {name : Nat}
    (h : name ≠ owner) :
    Finmap.lookup name (editCell state owner edit).registry = Finmap.lookup name state.registry := by
  unfold editCell
  cases hlook : Finmap.lookup owner state.registry with
  | none => rfl
  | some _ => exact Finmap.lookup_insert_of_ne (a := owner) (a' := name) (s := state.registry) h

/-- A name outside {1..5} is absent from the s22 registry (cell 3 was removed;
the whole chain reduces through the successor equations). -/
theorem lookup_s22_none_of_ne {name : Nat} (h1 : name ≠ 1) (h2 : name ≠ 2) (h3 : name ≠ 3)
    (h4 : name ≠ 4) (h5 : name ≠ 5) :
    Finmap.lookup name s22.registry = none := by
  change Finmap.lookup name (Finmap.erase 3 s21.registry) = none
  rw [Finmap.lookup_erase_ne h3]
  change Finmap.lookup name (editCell s20 3 (fun cell => { cell with retired := true })).registry = none
  rw [editCell_lookup_ne s20 3 _ h3]
  change Finmap.lookup name (editCell s19 3 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s19 3 _ h3]
  change Finmap.lookup name (editCell s18 3 (fun cell => { cell with phase := .unloading })).registry = none
  rw [editCell_lookup_ne s18 3 _ h3]
  change Finmap.lookup name (editCell s17 1 (fun cell => { cell with phase := .unloading })).registry = none
  rw [editCell_lookup_ne s17 1 _ h1]
  change Finmap.lookup name (editCell s16 1 (fun cell => { cell with retired := true })).registry = none
  rw [editCell_lookup_ne s16 1 _ h1]
  change Finmap.lookup name (editCell s15 5 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s15 5 _ h5]
  change Finmap.lookup name (editCell s14 5 (fun cell => { cell with phase := .unloading, payload := { cell.payload with failureData := some 7 } })).registry = none
  rw [editCell_lookup_ne s14 5 _ h5]
  change Finmap.lookup name (editCell s13 5 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s13 5 _ h5]
  change Finmap.lookup name (Finmap.insert 5 cell5 s12.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 5) (a' := name) (s := s12.registry) h5]
  change Finmap.lookup name (editCell s11 4 (fun cell => { cell with phase := .active, committed := { entries := commitProjection s11 cell.component.provides }, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none, failureData := none } })).registry = none
  rw [editCell_lookup_ne s11 4 _ h4]
  change Finmap.lookup name (editCell s10 4 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s10 4 _ h4]
  change Finmap.lookup name (Finmap.insert 4 cell4 s9.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 4) (a' := name) (s := s9.registry) h4]
  change Finmap.lookup name (editCell s8 3 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s8 3 _ h3]
  change Finmap.lookup name (Finmap.insert 3 cell3 s7.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 3) (a' := name) (s := s7.registry) h3]
  change Finmap.lookup name (editCell s6 2 (fun cell => { cell with payload := iterPayload rulesSem cell [] 2 })).registry = none
  rw [editCell_lookup_ne s6 2 _ h2]
  change Finmap.lookup name (editCell s5 2 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s5 2 _ h2]
  change Finmap.lookup name (editCell s4 1 (fun cell => { cell with phase := .active, committed := { entries := commitProjection s4 cell.component.provides }, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none, failureData := none } })).registry = none
  rw [editCell_lookup_ne s4 1 _ h1]
  change Finmap.lookup name (editCell s3 1 (fun cell => { cell with payload := iterPayload rulesSem cell [2] 0 })).registry = none
  rw [editCell_lookup_ne s3 1 _ h1]
  change Finmap.lookup name (Finmap.insert 2 cell2 s2.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 2) (a' := name) (s := s2.registry) h2]
  change Finmap.lookup name (editCell s1 1 (fun cell => { cell with phase := .reloading, committedView := ∅, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s1 1 _ h1]
  change Finmap.lookup name (Finmap.insert 1 cell1 s0.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 1) (a' := name) (s := s0.registry) h1]
  change Finmap.lookup name (∅ : Finmap (fun _ : Nat => Cell)) = none
  rw [Finmap.lookup_empty]

/-! ### The main trace witnesses -/

/-- A name outside {1..5} is absent from the s24 registry (same chain as the
s22 lemma plus the leave/divertLand control edits). -/
theorem lookup_s24_none_of_ne {name : Nat} (h1 : name ≠ 1) (h2 : name ≠ 2) (h3 : name ≠ 3)
    (h4 : name ≠ 4) (h5 : name ≠ 5) :
    Finmap.lookup name s24.registry = none := by
  change Finmap.lookup name (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
  rw [editCell_lookup_ne s23 4 _ h4]
  change Finmap.lookup name (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [7], flightCode := none } })).registry = none
  rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ h2]
  change Finmap.lookup name { s22 with ambient := s22.ambient + 1 }.registry = none
  change Finmap.lookup name s22.registry = none
  exact lookup_s22_none_of_ne h1 h2 h3 h4 h5

/-- A name outside {1..5} is absent from the s26 registry (unload of 2, unload
of 4, then the s24 chain). -/
theorem lookup_s26_none_of_ne {name : Nat} (h1 : name ≠ 1) (h2 : name ≠ 2) (h3 : name ≠ 3)
    (h4 : name ≠ 4) (h5 : name ≠ 5) :
    Finmap.lookup name s26.registry = none := by
  change Finmap.lookup name (editCell s25 2 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s25 2 _ h2]
  change Finmap.lookup name (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s24 4 _ h4]
  exact lookup_s24_none_of_ne h1 h2 h3 h4 h5

theorem step_insert1 : OrchestrationRule (.insert none 1 cell1) s0 s1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 1) (child := cell1)
    (by simp []) (by decide)
    (by simp [CanonicalInitialCell, nextBirth])
    (by intro name cell' h; simp at h)

theorem step_begin1 : LifecycleRule rulesSem (.begin 1 ∅) s1 s2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell1)
    (hlook := lookup_s1_1) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cell1, lookup_s1_1, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_insert2 : OrchestrationRule (.insert (some 1) 2 cell2) s2 s3 := by
  exact OrchestrationRule.insert (registrar := some 1) (fresh := 2) (child := cell2)
    (by simp [s2, s1, beginState, editCell, allocate, Finmap.lookup_insert])
    (by simp [s2, s1, beginState, editCell, allocate, ])
    (by
      simp [CanonicalInitialCell, Registered, s2, s1, nextBirth, beginState, editCell,
        allocate, beginPayload, rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        by_cases hname : name = 1
        · subst name
          rw [lookup_s2_1] at h
          cases h with | refl
          change key ∈ cell2.component.provides at hkey
          simp at hkey
          subst key
          simp []
        · simp [s2, s1, beginState, editCell, allocate, beginPayload, rulesSem,
            Finmap.lookup_insert, hname] at h)

theorem step_iter1 : LifecycleRule rulesSem (.iter 1 0) s3 s4 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cell1begun)
    (hlook := lookup_s3_1) (hphase := rfl)
    (htarget := ⟨cell1begun, lookup_s3_1, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 1 s3 = some (.yield s3 [2] 0)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

theorem step_finish1 : LifecycleRule rulesSem (.finish 1) s4 s5 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell1itered)
    (hlook := lookup_s4_1) (hphase := rfl)
    (htarget := ⟨cell1itered, lookup_s4_1, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 0 s4 = some (.halt s4 [])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

theorem step_begin2 : LifecycleRule rulesSem (.begin 2 view101) s5 s6 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell2)
    (hlook := lookup_s5_2) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s5_2)
    (hlaunch := rfl)

theorem step_iter2 : LifecycleRule rulesSem (.iter 2 2) s6 s7 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cell2begun)
    (hlook := lookup_s6_2) (hphase := rfl)
    (htarget := targetViewAt_s6_2)
    (hstage := by
      change fixtureStage 3 s6 = some (.yield s6 [] 2)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({20} : Finset Nat)
      simp)

theorem step_insert3 : OrchestrationRule (.insert none 3 cell3) s7 s8 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 3) (child := cell3)
    (by simp [s7, s6, s5, s4, s3, s2, s1, iterState, beginState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne])
    (by simp [s7, s6, s5, s4, s3, s2, s1, iterState, beginState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s7, s6, s5, s4, s3, s2, s1, nextBirth, iterState, beginState,
        finishState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin3 : LifecycleRule rulesSem (.begin 3 view101) s8 s9 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell3)
    (hlook := lookup_s8_3) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s8_3)
    (hlaunch := rfl)

theorem step_insert4 : OrchestrationRule (.insert none 4 cell4) s9 s10 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 4) (child := cell4)
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, beginState, iterState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert,
        Finmap.lookup_insert_of_ne])
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, beginState, iterState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s9, s8, s7, s6, s5, s4, s3, s2, s1, nextBirth, beginState,
        iterState, finishState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin4 : LifecycleRule rulesSem (.begin 4 view101) s10 s11 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell4)
    (hlook := lookup_s10_4) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s10_4)
    (hlaunch := rfl)

theorem step_finish4 : LifecycleRule rulesSem (.finish 4) s11 s12 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell4begun)
    (hlook := lookup_s11_4) (hphase := rfl)
    (htarget := targetViewAt_s11_4)
    (hstage := by
      change fixtureStage 0 s11 = some (.halt s11 [])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_insert5 : OrchestrationRule (.insert none 5 cell5) s12 s13 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 5) (child := cell5)
    (by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, finishState, beginState, iterState,
        editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert,
        Finmap.lookup_insert_of_ne])
    (by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, finishState, beginState, iterState,
        editCell, allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, nextBirth,
        finishState, beginState, iterState, editCell, allocate, beginPayload, iterPayload,
        rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin5 : LifecycleRule rulesSem (.begin 5 view101) s13 s14 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell5)
    (hlook := lookup_s13_5) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s13_5)
    (hlaunch := rfl)

abbrev failureEvidence5 : FailureEvidence State Nat (List Nat) :=
  { error := 7, boundary := s14, prefixUndo := [] }

theorem step_raise5 : LifecycleRule rulesSem (.raise 5 failureEvidence5) s14 s15 := by
  exact LifecycleRule.raise (sem := rulesSem) (cell := cell5begun)
    (hlook := lookup_s14_5) (hphase := rfl)
    (hstage := by
      change fixtureStage 99 s14 = some (.raise 7)
      rfl)
    (hbridge := by unfold FailureFromStage; rfl)

theorem step_unload5 : LifecycleRule rulesSem (.unload 5) s15 s16 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell5unloading)
    (hlook := lookup_s15_5) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s15_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s15_2] at hlook
          cases hlook with | refl
          by_cases hk : key = 10
          · subst key
            rw [Finmap.lookup_insert] at hkv
            have h15 : (1 : Nat) = 5 := Option.some.inj hkv
            omega
          · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
            cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            rw [lookup_s15_3] at hlook
            cases hlook with | refl
            by_cases hk : key = 10
            · subst key
              rw [Finmap.lookup_insert] at hkv
              have h15 : (1 : Nat) = 5 := Option.some.inj hkv
              omega
            · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
              cases hkv
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s15_4] at hlook
              cases hlook with | refl
              by_cases hk : key = 10
              · subst key
                rw [Finmap.lookup_insert] at hkv
                have h15 : (1 : Nat) = 5 := Option.some.inj hkv
                omega
              · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
                cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                exact (hne rfl).elim
              · have hnone : Finmap.lookup dependent s15.registry = none := by
                  simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
                    raiseState, beginState, finishState, iterState, editCell, allocate,
                    beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
                    Finmap.lookup_empty, hd1, hd2, hd3, hd4, hd5]
                rw [hnone] at hlook
                cases hlook)
    (haccumulator := by
      change fixtureAccumulator [] s15 = some s15
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_retire1 : OrchestrationRule (.retire 1) s16 s17 := by
  exact OrchestrationRule.retire lookup_s16_1

theorem step_leave1 : LifecycleRule rulesSem (.leave 1) s17 s18 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cell1retired)
    (hlook := lookup_s17_1) (hphase := rfl)
    (hchanged := by
      intro h
      rcases h with ⟨cell, hlook, hret, _hkeys, _hall⟩
      rw [lookup_s17_1] at hlook
      cases hlook with | refl
      cases hret)

theorem step_divertAbort3 : LifecycleRule rulesSem (.divertAbort 3 .absent) s18 s19 := by
  exact LifecycleRule.divertAbort (sem := rulesSem) (cell := cell3begun)
    (hlook := lookup_s18_3) (hphase := rfl) (hboundary := targetAbsent_s18_3)

theorem step_unload3 : LifecycleRule rulesSem (.unload 3) s19 s20 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell3unloading)
    (hlook := lookup_s19_3) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s19_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s19_2] at hlook
          cases hlook with | refl
          by_cases hk : key = 10
          · subst key
            rw [Finmap.lookup_insert] at hkv
            have h13 : (1 : Nat) = 3 := Option.some.inj hkv
            omega
          · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
            cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            exact (hne rfl).elim
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s19_4] at hlook
              cases hlook with | refl
              by_cases hk : key = 10
              · subst key
                rw [Finmap.lookup_insert] at hkv
                have h13 : (1 : Nat) = 3 := Option.some.inj hkv
                omega
              · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
                cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s19_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s19.registry = none := by
                  simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3,
                    s2, s1, divertAbortState, leaveState, retireState, unloadState, raiseState,
                    beginState, finishState, iterState, editCell, allocate, beginPayload,
                    iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
                    Finmap.lookup_empty, hd1, hd2, hd3, hd4, hd5]
                rw [hnone] at hlook
                cases hlook)
    (haccumulator := by
      change fixtureAccumulator [] s19 = some s19
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_retire3 : OrchestrationRule (.retire 3) s20 s21 := by
  exact OrchestrationRule.retire lookup_s20_3

theorem step_remove3 : OrchestrationRule (.remove 3) s21 s22 := by
  exact OrchestrationRule.remove (cell := cell3retired) (hlook := lookup_s21_3)
    (hretired := rfl) (hphase := by left; rfl) (hnoChild := by
      intro name cell' h hparent
      by_cases hn1 : name = 1
      · subst name
        rw [lookup_s21_1] at h
        cases h with | refl
        cases hparent
      · by_cases hn2 : name = 2
        · subst name
          rw [lookup_s21_2] at h
          cases h with | refl
          cases hparent
        · by_cases hn3 : name = 3
          · subst name
            rw [lookup_s21_3] at h
            cases h with | refl
            simp at hparent
          · by_cases hn4 : name = 4
            · subst name
              rw [lookup_s21_4] at h
              cases h with | refl
              cases hparent
            · by_cases hn5 : name = 5
              · subst name
                rw [lookup_s21_5] at h
                cases h with | refl
                cases hparent
              · have hnone : Finmap.lookup name s21.registry = none := by
                  simp [s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5,
                    s4, s3, s2, s1, retireState, unloadState, divertAbortState, leaveState, raiseState,
                    beginState, finishState, iterState, editCell, allocate, beginPayload,
                    iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
                    Finmap.lookup_empty, hn1, hn2, hn3, hn4, hn5]
                rw [hnone] at h
                cases h)

theorem step_divertLand2 : LifecycleRule rulesSem (.divertLand 2 ()) s22 s23 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cell2itered)
    (hlook := lookup_s22_2) (hphase := rfl) (htoken := rfl)
    (hchanged := targetNot_s22_2)
    (hland := by
      change fixtureLanding () s22 = some (.landed { s22 with ambient := s22.ambient + 1 } [7])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({20} : Finset Nat)
      simp)

theorem step_leave4 : LifecycleRule rulesSem (.leave 4) s23 s24 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cell4active)
    (hlook := lookup_s23_4) (hphase := rfl)
    (hchanged := targetNot_s23_4)

theorem step_unload4 : LifecycleRule rulesSem (.unload 4) s24 s25 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell4unloading)
    (hlook := lookup_s24_4) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s24_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s24_2] at hlook
          cases hlook with | refl
          by_cases hk : key = 10
          · subst key
            rw [Finmap.lookup_insert] at hkv
            have h14 : (1 : Nat) = 4 := Option.some.inj hkv
            omega
          · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
            cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s24.registry = none := by
              unfold s24 s23 s22
              unfold leaveState
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [7], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 s22.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hlook
          · by_cases hd4 : dependent = 4
            · subst dependent
              exact (hne rfl).elim
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s24_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s24.registry = none := by
                  change Finmap.lookup dependent (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
                  rw [editCell_lookup_ne s23 4 _ (by intro h; exact hd4 h)]
                  change Finmap.lookup dependent (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [7], flightCode := none } })).registry = none
                  rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by intro h; exact hd2 h)]
                  change Finmap.lookup dependent { s22 with ambient := s22.ambient + 1 }.registry = none
                  change Finmap.lookup dependent s22.registry = none
                  exact lookup_s22_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hlook)
    (haccumulator := by
      change fixtureAccumulator [] s24 = some s24
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_unload2 : LifecycleRule rulesSem (.unload 2) s25 s26 := by
  have hnone7 : Finmap.lookup 7 s25.registry = none := by
    change Finmap.lookup 7 (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
    rw [editCell_lookup_ne s24 4 _ (by decide)]
    exact lookup_s24_none_of_ne (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfold : foldRetire [7] s25 = s25 := by
    rw [foldRetire_cons_none hnone7, foldRetire_absent]
    intro n hn
    cases hn
  rw [show s26 = unloadState (foldRetire [7] s25) 2 from by rw [hfold]]
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell2unloading)
    (hlook := lookup_s25_2) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s25_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          exact (hne rfl).elim
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s25.registry = none := by
              change Finmap.lookup 3 (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s24 4 _ (by decide)]
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [7], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hlook
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s25_4] at hlook
              cases hlook with | refl
              rw [Finmap.lookup_empty] at hkv
              cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s25_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s25.registry = none := by
                  change Finmap.lookup dependent (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome = true then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
                  rw [editCell_lookup_ne s24 4 _ (by intro h; exact hd4 h)]
                  exact lookup_s24_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hlook)
    (haccumulator := by
      change fixtureAccumulator [7] s25 = some (foldRetire [7] s25)
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({20} : Finset Nat)
      simp)

theorem step_unload1 : LifecycleRule rulesSem (.unload 1) s26 s27 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell1unloading)
    (hlook := lookup_s26_1) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s26_2] at hlook
          cases hlook with | refl
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
            simp [hnone] at hlook
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s26_4] at hlook
              cases hlook with | refl
              rw [Finmap.lookup_empty] at hkv
              cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s26_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s26.registry = none :=
                  lookup_s26_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hlook)
    (haccumulator := by
      change fixtureAccumulator [2] s26 = some (foldRetire [2] s26)
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

/-! ### The anti-vacuity mini-traces -/

/-! #### Success: Begin → Iter [1] → Iter [2] → Finish [3] gives [3,2,1] -/

abbrev cellA : Cell :=
  { incarnation := 6, parent := none, birth := 0,
    component := { key := 6, requires := ∅, provides := ∅, actionCode := (), iteratorCode := 6, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 6, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev a1 : State := allocate s0 6 cellA
abbrev a2 : State := beginState rulesSem a1 6 ∅ ()
abbrev a3 : State := iterState rulesSem a2 6 [1] 5
abbrev a4 : State := iterState rulesSem a3 6 [2] 4
abbrev a5 : State := finishState rulesSem a4 6 [3]

abbrev cellAbegun : Cell := { cellA with phase := .reloading, committedView := ∅, payload := { cellA.payload with iteratorCode := 6, accumulatorCode := [], flightCode := some () } }
abbrev cellAitered1 : Cell := { cellAbegun with payload := { cellAbegun.payload with iteratorCode := 5, accumulatorCode := [1] } }
abbrev cellAitered2 : Cell := { cellAitered1 with payload := { cellAitered1.payload with iteratorCode := 4, accumulatorCode := [2,1] } }
abbrev cellAactive : Cell := { cellAitered2 with phase := .active, committed := { entries := commitProjection a4 (∅ : Finset Nat) }, payload := { cellAitered2.payload with accumulatorCode := [3,2,1], flightCode := none, failureData := none } }

theorem lookup_a1_6 : Finmap.lookup 6 a1.registry = some cellA := by
  congr

theorem lookup_a2_6 : Finmap.lookup 6 a2.registry = some cellAbegun := by
  congr

theorem lookup_a3_6 : Finmap.lookup 6 a3.registry = some cellAitered1 := by
  congr

theorem lookup_a4_6 : Finmap.lookup 6 a4.registry = some cellAitered2 := by
  congr

theorem lookup_a5_6 : Finmap.lookup 6 a5.registry = some cellAactive := by
  congr

theorem step_beginA : LifecycleRule rulesSem (.begin 6 ∅) a1 a2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellA)
    (hlook := lookup_a1_6) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cellA, lookup_a1_6, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_iterA1 : LifecycleRule rulesSem (.iter 6 5) a2 a3 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellAbegun)
    (hlook := lookup_a2_6) (hphase := rfl)
    (htarget := ⟨cellAbegun, lookup_a2_6, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 6 a2 = some (.yield a2 [1] 5)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_iterA2 : LifecycleRule rulesSem (.iter 6 4) a3 a4 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellAitered1)
    (hlook := lookup_a3_6) (hphase := rfl)
    (htarget := ⟨cellAitered1, lookup_a3_6, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 5 a3 = some (.yield a3 [2] 4)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_finishA : LifecycleRule rulesSem (.finish 6) a4 a5 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellAitered2)
    (hlook := lookup_a4_6) (hphase := rfl)
    (htarget := ⟨cellAitered2, lookup_a4_6, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 4 a4 = some (.halt a4 [3])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

/-! #### Failure: Begin → Iter [1] → Raise with the nonempty prefixUndo -/

abbrev cellF : Cell :=
  { incarnation := 7, parent := none, birth := 0,
    component := { key := 7, requires := ∅, provides := ∅, actionCode := (), iteratorCode := 10, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 10, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev f1 : State := allocate s0 7 cellF
abbrev f2 : State := beginState rulesSem f1 7 ∅ ()
abbrev f3 : State := iterState rulesSem f2 7 [1] 9
abbrev f4 : State := raiseState f3 7 7

abbrev failureEvidenceF : FailureEvidence State Nat (List Nat) :=
  { error := 7, boundary := f3, prefixUndo := [1] }

abbrev cellFbegun : Cell := { cellF with phase := .reloading, committedView := ∅, payload := { cellF.payload with iteratorCode := 10, accumulatorCode := [], flightCode := some () } }
abbrev cellFitered : Cell := { cellFbegun with payload := { cellFbegun.payload with iteratorCode := 9, accumulatorCode := [1] } }

theorem lookup_f1_7 : Finmap.lookup 7 f1.registry = some cellF := by
  congr

theorem lookup_f2_7 : Finmap.lookup 7 f2.registry = some cellFbegun := by
  congr

theorem lookup_f3_7 : Finmap.lookup 7 f3.registry = some cellFitered := by
  congr

theorem lookup_f4_7 : Finmap.lookup 7 f4.registry = some { cellFitered with phase := .unloading, payload := { cellFitered.payload with failureData := some 7 } } := by
  congr

theorem step_beginF : LifecycleRule rulesSem (.begin 7 ∅) f1 f2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellF)
    (hlook := lookup_f1_7) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cellF, lookup_f1_7, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_iterF : LifecycleRule rulesSem (.iter 7 9) f2 f3 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellFbegun)
    (hlook := lookup_f2_7) (hphase := rfl)
    (htarget := ⟨cellFbegun, lookup_f2_7, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 10 f2 = some (.yield f2 [1] 9)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_raiseF : LifecycleRule rulesSem (.raise 7 failureEvidenceF) f3 f4 := by
  exact LifecycleRule.raise (sem := rulesSem) (cell := cellFitered)
    (hlook := lookup_f3_7) (hphase := rfl)
    (hstage := by
      change fixtureStage 9 f3 = some (.raise 7)
      rfl)
    (hbridge := by unfold FailureFromStage; rfl)

/-! #### Landing: provider active → consumer Begin/Iter → provider Retire/Leave → consumer DivertLand -/

abbrev viewL10 : Finmap (fun _ : Nat => Nat) := Finmap.insert 10 9 (∅ : Finmap (fun _ : Nat => Nat))

abbrev cellLP : Cell :=
  { incarnation := 9, parent := none, birth := 0,
    component := { key := 9, requires := ∅, provides := {10}, actionCode := (), iteratorCode := 0, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 0, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cellL : Cell :=
  { incarnation := 8, parent := none, birth := 1,
    component := { key := 8, requires := {10}, provides := ∅, actionCode := (), iteratorCode := 6, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 6, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev l1 : State := allocate s0 9 cellLP
abbrev l2 : State := beginState rulesSem l1 9 ∅ ()
abbrev l3 : State := finishState rulesSem l2 9 []
abbrev l4 : State := allocate l3 8 cellL
abbrev l5 : State := beginState rulesSem l4 8 viewL10 ()
abbrev l6 : State := iterState rulesSem l5 8 [1] 5
abbrev l7 : State := retireState l6 9
abbrev l8 : State := leaveState l7 9
abbrev l9 : State := divertLandState rulesSem { l8 with ambient := l8.ambient + 1 } 8 [7]

abbrev cellLPbegun : Cell := { cellLP with phase := .reloading, committedView := ∅, payload := { cellLP.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }
abbrev cellLPactive : Cell := { cellLPbegun with phase := .active, committed := { entries := commitProjection l2 ({10} : Finset Nat) }, payload := { cellLPbegun.payload with accumulatorCode := [], flightCode := none, failureData := none } }
abbrev cellLPretired : Cell := { cellLPactive with retired := true }
abbrev cellLPunloading : Cell := { cellLPretired with phase := .unloading }
abbrev cellLbegun : Cell := { cellL with phase := .reloading, committedView := viewL10, payload := { cellL.payload with iteratorCode := 6, accumulatorCode := [], flightCode := some () } }
abbrev cellLitered : Cell := { cellLbegun with payload := { cellLbegun.payload with iteratorCode := 5, accumulatorCode := [1] } }
abbrev cellLlanded : Cell := { cellLitered with phase := .unloading, payload := { cellLitered.payload with accumulatorCode := [7,1], flightCode := none } }

theorem lookup_l1_9 : Finmap.lookup 9 l1.registry = some cellLP := by
  congr

theorem lookup_l2_9 : Finmap.lookup 9 l2.registry = some cellLPbegun := by
  congr

theorem lookup_l3_9 : Finmap.lookup 9 l3.registry = some cellLPactive := by
  congr

theorem lookup_l4_9 : Finmap.lookup 9 l4.registry = some cellLPactive := by
  congr

theorem lookup_l4_8 : Finmap.lookup 8 l4.registry = some cellL := by
  congr

theorem lookup_l5_8 : Finmap.lookup 8 l5.registry = some cellLbegun := by
  congr

theorem lookup_l6_8 : Finmap.lookup 8 l6.registry = some cellLitered := by
  congr

theorem lookup_l7_9 : Finmap.lookup 9 l7.registry = some cellLPretired := by
  congr

theorem lookup_l8_9 : Finmap.lookup 9 l8.registry = some cellLPunloading := by
  congr

theorem lookup_l8_8 : Finmap.lookup 8 l8.registry = some cellLitered := by
  congr

theorem lookup_l9_8 : Finmap.lookup 8 l9.registry = some cellLlanded := by
  congr

theorem providesNow_l4_9_10 : ProvidesNow l4 9 10 :=
  ⟨_, lookup_l4_9, by
    change 10 ∈ (commitProjection l2 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem targetViewAt_l4_8 : TargetViewAt l4 8 viewL10 := by
  refine ⟨_, lookup_l4_8, ?_, ?_, ?_⟩
  · rfl
  · change viewL10.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 9 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 9 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_l4_9_10
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_l5_8 : TargetViewAt l5 8 viewL10 := by
  refine ⟨_, lookup_l5_8, ?_, ?_, ?_⟩
  · rfl
  · change viewL10.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 9 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 9 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_l4_9_10
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetNot_l7_9 : ¬ TargetViewAt l7 9 ∅ := by
  intro h
  rcases h with ⟨cell, hl, hret, _hkeys, _hall⟩
  rw [lookup_l7_9] at hl
  cases hl with | refl
  cases hret

theorem targetNot_l8_8 : ¬ TargetViewAt l8 8 viewL10 := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow l8 9 10 := hall 10 9 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_l8_9] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem step_beginLP : LifecycleRule rulesSem (.begin 9 ∅) l1 l2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellLP)
    (hlook := lookup_l1_9) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cellLP, lookup_l1_9, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_finishLP : LifecycleRule rulesSem (.finish 9) l2 l3 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellLPbegun)
    (hlook := lookup_l2_9) (hphase := rfl)
    (htarget := ⟨cellLPbegun, lookup_l2_9, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 0 l2 = some (.halt l2 [])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

theorem step_insertL : OrchestrationRule (.insert none 8 cellL) l3 l4 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 8) (child := cellL)
    (by decide)
    (by decide)
    (by
      simp [CanonicalInitialCell, l3, l2, l1, nextBirth, finishState, beginState, editCell,
        allocate, beginPayload, rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_beginL : LifecycleRule rulesSem (.begin 8 viewL10) l4 l5 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellL)
    (hlook := lookup_l4_8) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_l4_8)
    (hlaunch := rfl)

theorem step_iterL : LifecycleRule rulesSem (.iter 8 5) l5 l6 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellLbegun)
    (hlook := lookup_l5_8) (hphase := rfl)
    (htarget := targetViewAt_l5_8)
    (hstage := by
      change fixtureStage 6 l5 = some (.yield l5 [1] 5)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_retireLP : OrchestrationRule (.retire 9) l6 l7 := by
  exact OrchestrationRule.retire (by change Finmap.lookup 9 l6.registry = some cellLPactive; congr)

theorem step_leaveLP : LifecycleRule rulesSem (.leave 9) l7 l8 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cellLPretired)
    (hlook := lookup_l7_9)
    (hphase := rfl)
    (hchanged := targetNot_l7_9)

theorem step_divertLandL : LifecycleRule rulesSem (.divertLand 8 ()) l8 l9 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cellLitered)
    (hlook := lookup_l8_8) (hphase := rfl) (htoken := rfl)
    (hchanged := targetNot_l8_8)
    (hland := by
      change fixtureLanding () l8 = some (.landed { l8 with ambient := l8.ambient + 1 } [7])
      rfl)
    (henvelope := by change (∅ : Finset Nat) ⊆ (∅ : Finset Nat); simp)

/-! #### D48: the guarded stage write of key 12 within the acting fiber's provision -/

abbrev cellDW : Cell :=
  { incarnation := 11, parent := none, birth := 0,
    component := { key := 11, requires := ∅, provides := {12}, actionCode := (), iteratorCode := 8, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 8, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev d1 : State := allocate s0 11 cellDW
abbrev d2 : State := beginState rulesSem d1 11 ∅ ()
abbrev d3 : State := iterState rulesSem (stageWrite12 d2) 11 [1] 7

abbrev cellDWbegun : Cell := { cellDW with phase := .reloading, committedView := ∅, payload := { cellDW.payload with iteratorCode := 8, accumulatorCode := [], flightCode := some () } }
abbrev cellDWitered : Cell := { cellDWbegun with payload := { cellDWbegun.payload with iteratorCode := 7, accumulatorCode := [1] } }

theorem lookup_d1_11 : Finmap.lookup 11 d1.registry = some cellDW := by
  congr

theorem lookup_d2_11 : Finmap.lookup 11 d2.registry = some cellDWbegun := by
  congr

theorem lookup_d3_11 : Finmap.lookup 11 d3.registry = some cellDWitered := by
  congr

theorem stageGuard12_d2_false : stageGuard12 d2 = false := by
  decide

theorem step_insertDW : OrchestrationRule (.insert none 11 cellDW) s0 d1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 11) (child := cellDW)
    (by decide) (by decide)
    (by simp [CanonicalInitialCell, nextBirth])
    (by intro name cell' h; simp at h)

theorem step_beginDW : LifecycleRule rulesSem (.begin 11 ∅) d1 d2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellDW)
    (hlook := lookup_d1_11) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cellDW, lookup_d1_11, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_iterDW : LifecycleRule rulesSem (.iter 11 7) d2 d3 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellDWbegun)
    (hlook := lookup_d2_11) (hphase := rfl)
    (htarget := ⟨cellDWbegun, lookup_d2_11, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 8 d2 = some (.yield (stageWrite12 d2) [1] 7)
      exact fixtureStage_eq_8_write stageGuard12_d2_false)
    (hrank := by decide)
    (henvelope := by
      change ({12} : Finset Nat) ⊆ ({12} : Finset Nat)
      simp)
end

end STC.Examples.GlobalRules
