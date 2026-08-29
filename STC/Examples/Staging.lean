module

public import STC.Staging

/-!
# Finite staging evidence

The fixture uses the production Control trace as the authoritative full path and
derives reload/unload base macros through an explicit atomic profile.
-/

namespace STC.Examples.Staging

open STC.Control STC.Staging

@[expose] public section

section Fixture

inductive BaseState where
  | inactive
  | active
  deriving DecidableEq, Repr

inductive ExtendedState where
  | inactive
  | reloading
  | active
  | unloading
  deriving DecidableEq, Repr

inductive BaseOrch where
  | insert
  | retire
  | remove
  deriving DecidableEq, Repr

inductive BaseLife where
  | reload
  | unload
  deriving DecidableEq, Repr

abbrev FullOrch := OrchestrationLabel Nat Unit
abbrev FullLife := LifecycleLabel Nat Nat Unit ExtendedState Bool

def embed : BaseState → ExtendedState
  | .inactive => .inactive
  | .active => .active

def project : ExtendedState → Option BaseState
  | .inactive => some .inactive
  | .active => some .active
  | .reloading => none
  | .unloading => none

def stable : ExtendedState → Prop
  | .inactive => True
  | .active => True
  | .reloading => False
  | .unloading => False

def fullOrch : FullOrch → ExtendedState → ExtendedState → Prop
  | .insert _ _, before, after => before = .inactive ∧ after = .inactive
  | .retire _, before, after => before = .active ∧ after = .active
  | .remove _, before, after => before = .inactive ∧ after = .inactive

def fullLife : FullLife → ExtendedState → ExtendedState → Prop
  | .begin _ _, before, after => before = .inactive ∧ after = .reloading
  | .finish _, before, after => before = .reloading ∧ after = .active
  | .leave _, before, after => before = .active ∧ after = .unloading
  | .unload _, before, after => before = .unloading ∧ after = .inactive
  | _, _, _ => False

def expandOrch : BaseOrch → List (Sum FullOrch FullLife)
  | .insert => [.inl (OrchestrationLabel.insert 1 ())]
  | .retire => [.inl (OrchestrationLabel.retire 1)]
  | .remove => [.inl (OrchestrationLabel.remove 1)]

def expandLife : BaseLife → List (Sum FullOrch FullLife)
  | .reload => [.inr (.begin 1 ()), .inr (.finish 1)]
  | .unload => [.inr (.leave 1), .inr (.unload 1)]

def atomicOrch (labels : List (Sum FullOrch FullLife)) : Prop :=
  labels = expandOrch .insert ∨ labels = expandOrch .retire ∨ labels = expandOrch .remove

def atomicLife (labels : List (Sum FullOrch FullLife)) : Prop :=
  labels = [] ∨ labels = expandLife .reload ∨ labels = expandLife .unload

def model : StagingModel BaseState ExtendedState BaseOrch FullOrch BaseLife FullLife where
  embed := embed
  project := project
  stable := stable
  fullOrch := fullOrch
  fullLife := fullLife
  expandOrch := expandOrch
  expandLife := expandLife
  atomicOrch := atomicOrch
  atomicLife := atomicLife
  project_embed := by intro base; cases base <;> rfl
  stable_embed := by intro base; cases base <;> trivial

def reloadPath : MacroPath model (expandLife .reload) .inactive .active :=
  ⟨.cons (.lifecycle (.begin 1 ()) (show fullLife (.begin 1 ()) .inactive .reloading from ⟨rfl, rfl⟩))
      (.cons (.lifecycle (.finish 1) (show fullLife (.finish 1) .reloading .active from ⟨rfl, rfl⟩)) .nil), by rfl⟩

def unloadPath : MacroPath model (expandLife .unload) .active .inactive :=
  ⟨.cons (.lifecycle (.leave 1) (show fullLife (.leave 1) .active .unloading from ⟨rfl, rfl⟩))
      (.cons (.lifecycle (.unload 1) (show fullLife (.unload 1) .unloading .inactive from ⟨rfl, rfl⟩)) .nil), by rfl⟩

theorem reload_macro : RbLife model .reload .inactive .active :=
  ⟨by exact Or.inr (Or.inl rfl), ⟨reloadPath⟩⟩

theorem unload_macro : RbLife model .unload .active .inactive :=
  ⟨by exact Or.inr (Or.inr rfl), ⟨unloadPath⟩⟩

theorem simulation : ForwardSimulation model where
  orchestration := by intro before after label h; exact h.2
  lifecycle := by intro before after label h; exact h.2

theorem reload_forward :
    ∃ _path : MacroPath model (expandLife .reload) (.inactive) (.active), True := by
  exact ⟨reloadPath, trivial⟩

def composed_reload_unload :
    MacroPath model (expandLife .reload ++ expandLife .unload) .inactive .inactive := by
  exact append_macro_paths reloadPath unloadPath

theorem round_trip (base : BaseState) : project (embed base) = some base :=
  project_embed_round_trip model base

theorem stable_image (base : BaseState) : stable (embed base) :=
  STC.Staging.stable_embed model base

theorem reload_adequacy_case
    (_path : MacroPath model (expandLife .reload) .inactive .active) :
    ∃ label : BaseLife, expandLife label = expandLife .reload ∧ RbLife model label .inactive .active := by
  exact ⟨.reload, rfl, reload_macro⟩

theorem wrong_endpoint_rejected : project .reloading ≠ some .inactive := by
  simp [project]

theorem non_atomic_rejected : ¬ atomicLife [Sum.inr (.begin 1 ())] := by
  simp [atomicLife, expandLife]

theorem interleaved_rejected :
    ¬ atomicLife ([Sum.inr (.begin 1 ())] ++ [Sum.inl (.insert 1 ())]) := by
  simp [atomicLife, expandLife]

theorem unfinished_rejected : ¬ atomicLife [Sum.inr (.begin 1 ())] := by
  exact non_atomic_rejected

end Fixture

end

end STC.Examples.Staging
