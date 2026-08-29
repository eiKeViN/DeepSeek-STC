module

public import STC.Control

/-!
# Atomic staging view

The extended Control relation is authoritative.  A base step is a finite,
profile-approved macro path over the shared `STC.Control.Trace` carrier, with
stable embedded endpoints and explicit projection witnesses.

## Main declarations

* `StagingModel`, `MacroPath`, `AtomicOrchMacro`, and `AtomicLifeMacro`;
* `RbOrch`, `RbLife`, `ForwardSimulation`, and `AtomicAdequacy`;
* project/embed and trace-composition theorems.
-/

universe u v w x y z

namespace STC.Staging

open STC.Control

@[expose] public section

section Model

structure StagingModel
    (BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel : Type u) where
  embed : BaseState → ExtendedState
  project : ExtendedState → Option BaseState
  stable : ExtendedState → Prop
  fullOrch : FullOrchLabel → ExtendedState → ExtendedState → Prop
  fullLife : FullLifeLabel → ExtendedState → ExtendedState → Prop
  expandOrch : BaseOrchLabel → List (Sum FullOrchLabel FullLifeLabel)
  expandLife : BaseLifeLabel → List (Sum FullOrchLabel FullLifeLabel)
  atomicOrch : List (Sum FullOrchLabel FullLifeLabel) → Prop
  atomicLife : List (Sum FullOrchLabel FullLifeLabel) → Prop
  project_embed : ∀ base, project (embed base) = some base
  stable_embed : ∀ base, stable (embed base)

structure MacroPath
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel)
    (labels : List (Sum FullOrchLabel FullLifeLabel))
    (before after : ExtendedState) where
  trace : Trace model.fullOrch model.fullLife before after
  labels_eq : trace.labels = labels

def AtomicOrchMacro
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel)
    (label : BaseOrchLabel) (before after : BaseState) : Prop :=
  model.atomicOrch (model.expandOrch label) ∧
    Nonempty (MacroPath model (model.expandOrch label)
      (model.embed before) (model.embed after))

def AtomicLifeMacro
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel)
    (label : BaseLifeLabel) (before after : BaseState) : Prop :=
  model.atomicLife (model.expandLife label) ∧
    Nonempty (MacroPath model (model.expandLife label)
      (model.embed before) (model.embed after))

def RbOrch
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) := AtomicOrchMacro model

def RbLife
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) := AtomicLifeMacro model

structure ForwardSimulation
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) : Prop where
  orchestration : ∀ {before after : BaseState} {label : BaseOrchLabel},
    RbOrch model label before after →
      Nonempty (MacroPath model (model.expandOrch label)
        (model.embed before) (model.embed after))
  lifecycle : ∀ {before after : BaseState} {label : BaseLifeLabel},
    RbLife model label before after →
      Nonempty (MacroPath model (model.expandLife label)
        (model.embed before) (model.embed after))

structure AtomicAdequacy
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) : Prop where
  orchestration : ∀ {before after : BaseState}
    {labels : List (Sum FullOrchLabel FullLifeLabel)},
    model.atomicOrch labels →
    (path : MacroPath model labels (model.embed before) (model.embed after)) →
    before = after ∨ ∃ label, labels = model.expandOrch label ∧ RbOrch model label before after
  lifecycle : ∀ {before after : BaseState}
    {labels : List (Sum FullOrchLabel FullLifeLabel)},
    model.atomicLife labels →
    (path : MacroPath model labels (model.embed before) (model.embed after)) →
    before = after ∨ ∃ label, labels = model.expandLife label ∧ RbLife model label before after

theorem project_embed_round_trip
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) (base : BaseState) :
    model.project (model.embed base) = some base :=
  model.project_embed base

theorem stable_embed
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel) (base : BaseState) :
    model.stable (model.embed base) :=
  model.stable_embed base

theorem forward_orchestration
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    {before after : BaseState} {label : BaseOrchLabel}
    (simulation : ForwardSimulation model) (h : RbOrch model label before after) :
    Nonempty (MacroPath model (model.expandOrch label)
      (model.embed before) (model.embed after)) :=
  simulation.orchestration h

theorem forward_lifecycle
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    {before after : BaseState} {label : BaseLifeLabel}
    (simulation : ForwardSimulation model) (h : RbLife model label before after) :
    Nonempty (MacroPath model (model.expandLife label)
      (model.embed before) (model.embed after)) :=
  simulation.lifecycle h

def append_macro_paths
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type u}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    {before middle after : ExtendedState}
    {leftLabels rightLabels : List (Sum FullOrchLabel FullLifeLabel)}
    (left : MacroPath model leftLabels before middle)
    (right : MacroPath model rightLabels middle after) :
    MacroPath model (leftLabels ++ rightLabels) before after := by
  refine ⟨Trace.append left.trace right.trace, ?_⟩
  rw [Trace.append_labels, left.labels_eq, right.labels_eq]

end Model

end

end STC.Staging
