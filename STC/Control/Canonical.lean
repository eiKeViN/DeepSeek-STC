module

public import STC.Control.Deletion
public import STC.Control.Commutation

/-!
# Canonicalization and confluence contracts

Canonicalization, endpoint confluence, and unique normal forms are three
separate results. The confluence relation retains explicit state and episode
observations plus a permutation witness.
-/

universe u v w

namespace STC.Control

@[expose] public section

structure CanonicalEnvelope (State : Type u) (Trace : Type v) where
  reachable : State → Prop
  wellFormed : State → Prop
  finiteSupport : State → Prop
  supportOrdered : State → Prop
  totalProvision : State → Prop
  quiescentNonfailed : State → Prop
  semanticCoherent : State → Prop
  pairwiseIndependent : State → Prop
  deletionAvailable : State → Prop

structure CanonicalResult (State : Type u) (Trace : Type v) where
  input : Trace
  output : Trace
  normalized : Trace
  preservesObservation : Prop
  supportCompatible : Prop

def Canonicalizes (State : Type u) (Trace : Type v)
    (envelope : CanonicalEnvelope State Trace) : Prop :=
  ∀ state, envelope.reachable state → envelope.wellFormed state →
    envelope.finiteSupport state → Nonempty (CanonicalResult State Trace)

structure ConfluenceResult (State : Type u) (Episode : Type v) (Name : Type w) where
  permutation : Equiv.Perm Name
  stateRelated : State → State → Prop
  episodeRelated : Episode → Episode → Prop
  conclusion : Prop

structure ConfluenceEnvelope (State : Type u) (Trace : Type v) where
  canonical : State → Prop
  admissible : Trace → Prop
  nonfailed : Trace → Prop
  sameInputs : Trace → Trace → Prop
  sameWitnesses : Trace → Trace → Prop
  alphaComplete : Prop

def EndpointConfluent (State : Type u) (Trace : Type v) (Name : Type w)
    (Episode : Type u) (envelope : ConfluenceEnvelope State Trace) : Prop :=
  ∀ left right, envelope.admissible left → envelope.admissible right →
    envelope.nonfailed left → envelope.nonfailed right → envelope.sameInputs left right →
      Nonempty (ConfluenceResult State Episode Name)

def UniqueNormalForm (State : Type u) (Trace : Type v)
    (envelope : ConfluenceEnvelope State Trace) : Prop :=
  ∀ left right, envelope.admissible left → envelope.admissible right → left = right

end

end STC.Control
