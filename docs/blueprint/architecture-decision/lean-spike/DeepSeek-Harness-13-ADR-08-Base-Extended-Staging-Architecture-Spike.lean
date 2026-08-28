/-
  ADR-08 BD-STAGING standalone compiler spike.

  R+ is the only authoritative full labelled relation.  The base relation is
  an AtomicProfile-controlled finite macro/view over R+; it is not a second
  independently maintained calculus and is not an arbitrary subrelation.

  This file is intentionally independent of production STC modules and of
  historical ADR spikes.  It demonstrates the carrier, embedding/projection,
  finite trace, forward-simulation, and atomic-adequacy interfaces on a small
  lifecycle profile.  Concrete K, guard, WF, provider, control, and runtime
  refinement obligations remain deferred.
-/

import Std.Tactic

set_option autoImplicit false

universe u

namespace STCADR08

/-! ## 1. Finite labelled traces -/

inductive Trace {State Label : Type u}
    (step : Label -> State -> State -> Prop) :
    State -> List Label -> State -> Prop where
  | nil (state : State) : Trace step state [] state
  | cons {before middle after : State} {label : Label} {rest : List Label} :
      step label before middle ->
      Trace step middle rest after ->
      Trace step before (label :: rest) after

namespace Trace

theorem append {State Label : Type u}
    {step : Label -> State -> State -> Prop}
    {before middle after : State} {left right : List Label} :
    Trace step before left middle ->
    Trace step middle right after ->
    Trace step before (left ++ right) after
  | .nil _, h => h
  | .cons h hs, ht => .cons h (append hs ht)

theorem nil_endpoint {State Label : Type u}
    {step : Label -> State -> State -> Prop}
    {state endpoint : State}
    (h : Trace step state [] endpoint) : endpoint = state := by
  cases h
  rfl

end Trace

/-! ## 2. Staging model and derived macro contracts -/

structure StagingModel
    (BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u) where
  embed : BaseState -> ExtendedState
  project : ExtendedState -> Option BaseState
  stable : ExtendedState -> Prop
  fullOrch : FullOrchLabel -> ExtendedState -> ExtendedState -> Prop
  fullLife : FullLifeLabel -> ExtendedState -> ExtendedState -> Prop
  baseOrch : BaseOrchLabel -> BaseState -> BaseState -> Prop
  baseLife : BaseLifeLabel -> BaseState -> BaseState -> Prop
  expandOrch : BaseOrchLabel -> List FullOrchLabel
  expandLife : BaseLifeLabel -> List FullLifeLabel
  atomicOrch : List FullOrchLabel -> Prop
  atomicLife : List FullLifeLabel -> Prop
  project_embed : forall base, project (embed base) = some base
  stable_embed : forall base, stable (embed base)

def AtomicOrchMacro
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel)
    (label : BaseOrchLabel) (before after : BaseState) : Prop :=
  model.atomicOrch (model.expandOrch label) /\
    Trace model.fullOrch (model.embed before) (model.expandOrch label)
      (model.embed after)

def AtomicLifeMacro
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel)
    (label : BaseLifeLabel) (before after : BaseState) : Prop :=
  model.atomicLife (model.expandLife label) /\
    Trace model.fullLife (model.embed before) (model.expandLife label)
      (model.embed after)

structure ForwardSimulation
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) : Prop where
  orchestration :
    forall {before after : BaseState} {label : BaseOrchLabel},
      model.baseOrch label before after ->
      AtomicOrchMacro model label before after
  lifecycle :
    forall {before after : BaseState} {label : BaseLifeLabel},
      model.baseLife label before after ->
      AtomicLifeMacro model label before after

structure AtomicAdequacy
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) : Prop where
  orchestration :
    forall {before after : BaseState} {labels : List FullOrchLabel},
      model.atomicOrch labels ->
      Trace model.fullOrch (model.embed before) labels (model.embed after) ->
      before = after \/
        exists label, labels = model.expandOrch label /\
          model.baseOrch label before after
  lifecycle :
    forall {before after : BaseState} {labels : List FullLifeLabel},
      model.atomicLife labels ->
      Trace model.fullLife (model.embed before) labels (model.embed after) ->
      before = after \/
        exists label, labels = model.expandLife label /\
          model.baseLife label before after

theorem project_embed_round_trip
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) (base : BaseState) :
    model.project (model.embed base) = some base :=
  model.project_embed base

theorem forward_orchestration_trace
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    (simulation : ForwardSimulation model)
    {before after : BaseState} {label : BaseOrchLabel}
    (h : model.baseOrch label before after) :
    Trace model.fullOrch (model.embed before) (model.expandOrch label)
      (model.embed after) :=
  (simulation.orchestration h).2

theorem forward_lifecycle_trace
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    (simulation : ForwardSimulation model)
    {before after : BaseState} {label : BaseLifeLabel}
    (h : model.baseLife label before after) :
    Trace model.fullLife (model.embed before) (model.expandLife label)
      (model.embed after) :=
  (simulation.lifecycle h).2

/-! ## 3. A finite lifecycle profile -/

inductive ToyBase : Type
  | inactive
  | active
  deriving DecidableEq, Repr

inductive ToyExtended : Type
  | inactive
  | reloading
  | active
  | unloading
  deriving DecidableEq, Repr

inductive ToyOrch : Type
  | insert
  | retire
  | remove
  deriving DecidableEq, Repr

inductive ToyFullOrch : Type
  | insert
  | retire
  | remove
  deriving DecidableEq, Repr

inductive ToyLife : Type
  | reload
  | unload
  deriving DecidableEq, Repr

inductive ToyFullLife : Type
  | begin
  | finish
  | leave
  | unload
  | raise
  deriving DecidableEq, Repr

def toyEmbed : ToyBase -> ToyExtended
  | .inactive => .inactive
  | .active => .active

def toyProject : ToyExtended -> Option ToyBase
  | .inactive => some .inactive
  | .active => some .active
  | .reloading => none
  | .unloading => none

def toyStable : ToyExtended -> Prop
  | .inactive => True
  | .active => True
  | .reloading => False
  | .unloading => False

def toyFullOrch : ToyFullOrch -> ToyExtended -> ToyExtended -> Prop
  | .insert, before, after =>
      before = .inactive /\ after = .inactive
  | .retire, before, after =>
      before = .active /\ after = .active
  | .remove, before, after =>
      before = .inactive /\ after = .inactive

def toyFullLife : ToyFullLife -> ToyExtended -> ToyExtended -> Prop
  | .begin, before, after =>
      before = .inactive /\ after = .reloading
  | .finish, before, after =>
      before = .reloading /\ after = .active
  | .leave, before, after =>
      before = .active /\ after = .unloading
  | .unload, before, after =>
      before = .unloading /\ after = .inactive
  | _, _, _ => False

def toyBaseOrch : ToyOrch -> ToyBase -> ToyBase -> Prop
  | .insert, before, after =>
      before = .inactive /\ after = .inactive
  | .retire, before, after =>
      before = .active /\ after = .active
  | .remove, before, after =>
      before = .inactive /\ after = .inactive

def toyBaseLife : ToyLife -> ToyBase -> ToyBase -> Prop
  | .reload, before, after =>
      before = .inactive /\ after = .active
  | .unload, before, after =>
      before = .active /\ after = .inactive

def toyExpandOrch : ToyOrch -> List ToyFullOrch
  | .insert => [.insert]
  | .retire => [.retire]
  | .remove => [.remove]

def toyExpandLife : ToyLife -> List ToyFullLife
  | .reload => [.begin, .finish]
  | .unload => [.leave, .unload]

def toyAtomicOrch (labels : List ToyFullOrch) : Prop :=
  labels = [.insert] \/ labels = [.retire] \/ labels = [.remove]

def toyAtomicLife (labels : List ToyFullLife) : Prop :=
  labels = [] \/
    labels = [.begin, .finish] \/
    labels = [.leave, .unload]

def toyModel : StagingModel ToyBase ToyExtended ToyOrch ToyFullOrch ToyLife ToyFullLife where
  embed := toyEmbed
  project := toyProject
  stable := toyStable
  fullOrch := toyFullOrch
  fullLife := toyFullLife
  baseOrch := toyBaseOrch
  baseLife := toyBaseLife
  expandOrch := toyExpandOrch
  expandLife := toyExpandLife
  atomicOrch := toyAtomicOrch
  atomicLife := toyAtomicLife
  project_embed := by
    intro base
    cases base <;> rfl
  stable_embed := by
    intro base
    cases base <;> trivial

theorem toy_reload_macro :
    AtomicLifeMacro toyModel .reload .inactive .active := by
  constructor
  · exact Or.inr (Or.inl rfl)
  · apply Trace.cons
    · exact ⟨rfl, rfl⟩
    · apply Trace.cons
      · exact ⟨rfl, rfl⟩
      · exact Trace.nil _

theorem toy_unload_macro :
    AtomicLifeMacro toyModel .unload .active .inactive := by
  constructor
  · exact Or.inr (Or.inr rfl)
  · apply Trace.cons
    · exact ⟨rfl, rfl⟩
    · apply Trace.cons
      · exact ⟨rfl, rfl⟩
      · exact Trace.nil _

theorem toy_insert_macro :
    AtomicOrchMacro toyModel .insert .inactive .inactive := by
  constructor
  · exact Or.inl rfl
  · apply Trace.cons
    · exact ⟨rfl, rfl⟩
    · exact Trace.nil _

theorem toy_retire_macro :
    AtomicOrchMacro toyModel .retire .active .active := by
  constructor
  · exact Or.inr (Or.inl rfl)
  · apply Trace.cons
    · exact ⟨rfl, rfl⟩
    · exact Trace.nil _

theorem toy_remove_macro :
    AtomicOrchMacro toyModel .remove .inactive .inactive := by
  constructor
  · exact Or.inr (Or.inr rfl)
  · apply Trace.cons
    · exact ⟨rfl, rfl⟩
    · exact Trace.nil _

theorem toy_orchestration_rejects_wrong_endpoint :
    not (AtomicOrchMacro toyModel .insert .inactive .active) := by
  intro h
  cases h.2 with
  | cons hstep hrest =>
      cases hrest
      cases hstep.2

theorem toy_nonatomic_rejected :
    not (toyAtomicLife [.begin, .finish, .leave]) := by
  intro h
  rcases h with h | h | h
  · simp at h
  · simp at h
  · simp at h

theorem toy_failure_or_interleaving_rejected :
    not (toyAtomicLife [.begin, .finish, .raise]) := by
  intro h
  rcases h with h | h | h
  · simp at h
  · simp at h
  · simp at h

theorem toy_base_life_cases
    {before after : ToyBase} {label : ToyLife}
    (h : toyBaseLife label before after) :
      (before = .inactive /\ label = .reload /\ after = .active) \/
      (before = .active /\ label = .unload /\ after = .inactive) := by
  cases before <;> cases label <;> cases after <;>
    simp [toyBaseLife] at h ⊢

def toyForwardSimulation : ForwardSimulation toyModel where
  orchestration := by
    intro before after label h
    cases before with
    | inactive =>
      cases after with
      | inactive =>
        cases label with
        | insert => exact toy_insert_macro
        | retire => cases h
        | remove => exact toy_remove_macro
      | active =>
        cases label <;> cases h
    | active =>
      cases after with
      | inactive =>
        cases label <;> cases h
      | active =>
        cases label with
        | insert => cases h
        | retire => exact toy_retire_macro
        | remove => cases h
  lifecycle := by
    intro before after label h
    rcases toy_base_life_cases h with h | h
    · rcases h with ⟨hbefore, hlabel, hafter⟩
      cases hbefore
      cases hlabel
      cases hafter
      exact toy_reload_macro
    · rcases h with ⟨hbefore, hlabel, hafter⟩
      cases hbefore
      cases hlabel
      cases hafter
      exact toy_unload_macro

theorem toy_reload_adequacy :
    toyAtomicLife [.begin, .finish] ->
      Trace toyFullLife (toyEmbed .inactive) [.begin, .finish]
        (toyEmbed .active) ->
      (.inactive = .active \/
        exists label, [.begin, .finish] = toyExpandLife label /\
          toyBaseLife label .inactive .active) := by
  intro _ htrace
  right
  refine ⟨.reload, rfl, ?_⟩
  exact ⟨rfl, rfl⟩

theorem toy_reload_atomic_adequacy :
    toyAtomicLife [.begin, .finish] ->
      Trace toyFullLife (toyEmbed .inactive) [.begin, .finish]
        (toyEmbed .active) ->
      exists label, [.begin, .finish] = toyExpandLife label /\
        toyBaseLife label .inactive .active := by
  intro hatomic htrace
  rcases toy_reload_adequacy hatomic htrace with h | h
  · cases h
  · exact h

theorem toy_project_round_trip :
    toyProject (toyEmbed .inactive) = some .inactive := by
  exact project_embed_round_trip toyModel .inactive

end STCADR08
