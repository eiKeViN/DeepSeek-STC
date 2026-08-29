module

public import STC.Control.Recovery
public import STC.Control.Support.Quiescence

/-!
# Closed-episode deletion

The shortened-trace result is a contract whose envelope names every semantic
condition required by the repaired L72 statement.
-/

universe u v w

namespace STC.Control

@[expose] public section

structure DeletionEnvelope (State : Type u) (Label : Type v) where
  reachable : State → Prop
  wellFormed : State → Prop
  closedEpisode : State → Prop
  recovery : State → State → Prop
  continuationIndependent : State → State → Prop
  noRegisteredChildren : State → Prop
  totalProvision : State → Prop
  quiescent : State → Prop
  structural : State → Prop
  endpointObs : State → State → Prop

structure DeletionResult (State : Type u) (Label : Type v)
    (trace : State → State → Prop) (envelope : DeletionEnvelope State Label)
    (source : State) (target : State) where
  shortened : State
  original : trace source target
  shortenedTrace : trace source shortened
  endpoint_related : envelope.endpointObs shortened target
  envelope_holds : envelope.reachable source ∧ envelope.wellFormed source ∧
    envelope.closedEpisode target ∧ envelope.recovery source target ∧
      envelope.continuationIndependent source target ∧ envelope.noRegisteredChildren target ∧
        envelope.totalProvision target ∧ envelope.quiescent target ∧ envelope.structural target

/-- L72 is represented as an explicit construction obligation. -/
def CanDelete (State : Type u) (Label : Type v)
    (trace : State → State → Prop) (envelope : DeletionEnvelope State Label) : Prop :=
  ∀ source target, envelope.reachable source → envelope.wellFormed source →
    envelope.closedEpisode target → trace source target →
      Nonempty (DeletionResult State Label trace envelope source target)

end

end STC.Control
