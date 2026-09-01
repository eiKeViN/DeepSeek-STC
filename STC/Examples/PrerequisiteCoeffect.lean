module

public import STC.Core.Coeffect

/-!
# Coeffect prerequisite evidence

Finite store transitions distinguish semantic satisfaction from the Boolean
checker and retain explicit restoration laws.
-/

namespace STC.Examples.PrerequisiteCoeffect

open STC STC.Coeffect

@[expose] public section

def requirement : Nat → Nat → Prop := fun key value => key = value

def emptyStore : Store (fun _ : Nat => Nat) := ∅
def providedStore : Store (fun _ : Nat => Nat) := insert 2 2 emptyStore

theorem provided_step : ProvideStep 2 2 emptyStore providedStore := by
  constructor
  · rfl
  · rfl

theorem provided_lookup : lookup 2 providedStore = some 2 :=
  provideStep_lookup provided_step

theorem provided_restore : erase 2 providedStore = emptyStore :=
  provide_revoke_restore provided_step

/-- The constructive per-binding decidability for the equality requirement. -/
def requirementDec : ∀ k value, Decidable (requirement k value) :=
  fun k value => by
    dsimp [requirement]
    infer_instance

/-- The checker round trip under constructive decidability. -/
theorem sat_round_trip (store : Store (fun _ : Nat => Nat)) :
    satCheck requirement requirementDec store = true ↔ Satisfies requirement store := by
  constructor
  · intro h
    exact satCheck_sound requirement requirementDec store h
  · intro h
    exact satCheck_complete requirement requirementDec store h

/-- The declared-set checker round trip for the finite declaration `{2}`. -/
theorem declared_round_trip (store : Store (fun _ : Nat => Nat)) :
    declaredCheck {2} store = true ↔ declaredSatisfied {2} store := by
  constructor
  · intro h
    exact declaredCheck_sound {2} store h
  · intro h
    exact declaredCheck_complete {2} store h

/-- Pinned: the provided store satisfies the finite declaration `{2}`. -/
example : declaredCheck {2} providedStore = true := by
  decide

/-- Pinned: the empty store does not satisfy the declaration `{2}`. -/
example : declaredCheck {2} emptyStore = false := by
  decide

/-- Lift evidence: the lifted read of a present binding. -/
theorem liftGet_evidence :
    liftGet 2 providedStore = some
      { state := providedStore, undo := id, outcome := ⟨2, 2⟩ } := by
  unfold liftGet
  change (lookup 2 (insert 2 2 emptyStore)).map
      (fun value =>
        ({ state := providedStore, undo := id, outcome := ⟨2, value⟩ } :
          OpResult (Store (fun _ : Nat => Nat)) (Sigma (fun _ : Nat => Nat)))) =
    some ({ state := providedStore, undo := id, outcome := ⟨2, 2⟩ } :
      OpResult (Store (fun _ : Nat => Nat)) (Sigma (fun _ : Nat => Nat)))
  rw [coeffect_lookup_insert 2 2 emptyStore]
  rfl

/-- Lift evidence: a provision at a fresh key and its undo restore. -/
theorem liftProvide_evidence :
    ∃ r, liftProvide 3 3 emptyStore = some r ∧ r.undo r.state = emptyStore := by
  refine ⟨{ state := insert 3 3 emptyStore, undo := erase 3, outcome := () }, ?_, ?_⟩
  · unfold liftProvide
    change (if h : lookup 3 emptyStore = none then
        some ({ state := insert 3 3 emptyStore, undo := erase 3, outcome := () } :
          OpResult (Store (fun _ : Nat => Nat)) Unit)
      else none) = some ({ state := insert 3 3 emptyStore, undo := erase 3, outcome := () } :
        OpResult (Store (fun _ : Nat => Nat)) Unit)
    rw [dif_pos (by rfl)]
  · change erase 3 (insert 3 3 emptyStore) = emptyStore
    exact provide_revoke_restore ⟨rfl, rfl⟩

/-- Lift evidence: a key-local doubling update and its captured undo. -/
def doubleKey : Nat → Option Nat := fun n => some (n + n)

theorem liftKeyLocal_evidence :
    ∃ r, liftKeyLocal 2 doubleKey providedStore = some r ∧ lookup 2 (r.undo r.state) = some 2 := by
  refine ⟨{ state := insert 2 4 providedStore, undo := fun s => insert 2 2 s, outcome := () },
    ?_, ?_⟩
  · unfold liftKeyLocal
    change (match lookup 2 (insert 2 2 emptyStore) with
      | none => none
      | some old => (doubleKey old).map fun newVal =>
          ({ state := insert 2 newVal providedStore, undo := fun s => insert 2 old s, outcome := () } :
            OpResult (Store (fun _ : Nat => Nat)) Unit)) =
      some ({ state := insert 2 4 providedStore, undo := fun s => insert 2 2 s, outcome := () } :
        OpResult (Store (fun _ : Nat => Nat)) Unit)
    rw [coeffect_lookup_insert 2 2 emptyStore]
    rfl
  · change lookup 2 (insert 2 2 (insert 2 4 providedStore)) = some 2
    rw [coeffect_lookup_insert 2 2 (insert 2 4 providedStore)]

end

end STC.Examples.PrerequisiteCoeffect
