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

noncomputable def decideSat : ∀ store : Store (fun _ : Nat => Nat), Decidable (Satisfies requirement store) :=
  fun store => @Classical.propDecidable (Satisfies requirement store)

theorem sat_round_trip (store : Store (fun _ : Nat => Nat)) :
    satCheck requirement decideSat store = true ↔ Satisfies requirement store := by
  constructor
  · intro h
    exact satCheck_sound requirement decideSat store h
  · intro h
    exact satCheck_complete requirement decideSat store h

end

end STC.Examples.PrerequisiteCoeffect
