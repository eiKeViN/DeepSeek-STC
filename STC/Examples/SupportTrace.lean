module

public import Mathlib.Tactic
public import STC.Control.Support
public import STC.Examples.Control
public import STC.Examples.Staging
public import STC.Staging.Support
public import STC.State.Support.Alpha

/-!
# Integrated support trace evidence

Finite examples reuse the labelled Control trace and derived Staging macros.
They demonstrate certificate transport, fixed-point equality, and a genuine
non-identity name permutation while retaining a negative cyclic profile.
-/

namespace STC.Examples.SupportTrace

open STC STC.Control STC.Staging
open STC.Examples.Control
open STC.Examples.Staging

@[expose] public section

section Snapshot

def snapshot : SupportSnapshot (Fin 2) (Fin 1) where
  dom := {0, 1}
  retired := fun _ => false
  parent := fun _ => none
  requires := fun _ => ∅
  provides := fun _ => ∅
  birth := fun n => n.val

def order : SupportOrder snapshot where
  rank := fun n => n.val
  edge_lt := by
    intro a b ha hb h
    simp [SupportRel, Precedes, ParentEdge, snapshot] at h

def certificate : CommittedSnapshot snapshot where
  committed := snapshot.dom
  committed_subset := by intro n h; exact h
  domain_committed := by intro n h; exact h
  order := order

def stateSnapshot : State → SupportSnapshot (Fin 2) (Fin 1) := fun _ => snapshot

theorem contract : SupportTraceContract stateSnapshot
    STC.Examples.Control.orchestration STC.Examples.Control.lifecycle where
  orchestration_preserves := by
    intro label before after premise h
    exact ⟨certificate⟩
  lifecycle_preserves := by
    intro label before after premise h
    exact ⟨certificate⟩

theorem initial_certificate : HasCommittedSupport stateSnapshot inserted := by
  exact ⟨certificate⟩

theorem lifecycle_trace_certificate :
    HasCommittedSupport stateSnapshot active :=
  trace_support_preserves contract reloadTrace initial_certificate

theorem lifecycle_trace_wellFounded :
    SupportWF (stateSnapshot active) :=
  trace_endpoint_supportWF contract reloadTrace initial_certificate

theorem lifecycle_trace_dependency_wf :
    ∃ _o : SupportOrder (stateSnapshot active),
      WellFounded (fun (x y : {n // n ∈ (stateSnapshot active).dom}) =>
        SupportDep (stateSnapshot active) y.1 x.1) :=
  trace_endpoint_supportDep_wellFounded contract reloadTrace initial_certificate

theorem support_fixed_point_example :
    SupportSet snapshot = (snapshot.dom : Set (Fin 2)) := by
  apply supportSet_eq_of_fixed snapshot order
  ext n
  fin_cases n <;>
    simp [SupportOperator, SupportClause, ParentSupported, ProvidersSupported, snapshot]

end Snapshot

section Alpha

def swapNames : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem swap_is_nonidentity : swapNames 0 ≠ 0 := by decide

theorem swap_support_transport (n : Fin 2) :
    swapNames n ∈ SupportSet (renameSnapshot swapNames snapshot) ↔
      n ∈ SupportSet snapshot :=
  supportSet_rename swapNames snapshot

theorem swap_order_transport :
    SupportWF (renameSnapshot swapNames snapshot) := by
  exact (supportWF_rename swapNames snapshot).mpr ⟨order⟩

end Alpha

section Staging

def stagingSnapshot : STC.Examples.Staging.ExtendedState → SupportSnapshot (Fin 2) (Fin 1) := fun _ => snapshot

theorem stagingContract : MacroSupportContract STC.Examples.Staging.model stagingSnapshot where
  path_preserves := by
    intro labels before after path h
    exact ⟨certificate⟩

theorem staging_reload_support :
    HasCommittedSupport stagingSnapshot (STC.Examples.Staging.embed .active) := by
  exact lifecycle_macro_support stagingContract STC.Examples.Staging.reload_macro ⟨certificate⟩

theorem staging_singleton_orchestration_support :
    HasCommittedSupport stagingSnapshot (STC.Examples.Staging.embed .inactive) := by
  exact orchestration_macro_support stagingContract
    (show RbOrch STC.Examples.Staging.model .insert .inactive .inactive from by
      refine ⟨?_, ?_⟩
      · exact Or.inl rfl
      · refine ⟨?_⟩
        refine ⟨.cons (.orchestration (.insert 1 ()) (by exact ⟨rfl, rfl⟩)) .nil, ?_⟩
        rfl)
    ⟨certificate⟩

end Staging

end

end STC.Examples.SupportTrace
