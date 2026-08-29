module

public import STC.Control.Commutation
public import STC.Control.Deletion

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
  startsAt : Trace → State → Prop
  normalizes : Trace → Trace → Prop
  traceObservation : Trace → Trace → Prop
  supportCompatible : Trace → Trace → Prop

structure CanonicalResult (State : Type u) (Trace : Type v)
    (envelope : CanonicalEnvelope State Trace) (input : Trace) where
  output : Trace
  normalized : envelope.normalizes input output
  preservesObservation : envelope.traceObservation input output
  supportCompatible : envelope.supportCompatible input output

def Canonicalizes (State : Type u) (Trace : Type v)
    (envelope : CanonicalEnvelope State Trace) : Prop :=
  ∀ state input, envelope.startsAt input state → envelope.reachable state →
    envelope.wellFormed state → envelope.finiteSupport state →
      envelope.supportOrdered state → envelope.totalProvision state →
        envelope.quiescentNonfailed state → envelope.semanticCoherent state →
          envelope.pairwiseIndependent state → envelope.deletionAvailable state →
            Nonempty (CanonicalResult State Trace envelope input)

structure ConfluenceEnvelope (State : Type u) (Trace : Type v) (Name : Type w)
    (Episode : Type u) where
  canonical : State → Prop
  admissible : Trace → Prop
  nonfailed : Trace → Prop
  sameInputs : Trace → Trace → Prop
  sameWitnesses : Trace → Trace → Prop
  endpoint : Trace → State
  episode : Trace → Episode
  stateRelated : Equiv.Perm Name → State → State → Prop
  episodeRelated : Equiv.Perm Name → Episode → Episode → Prop
  alphaComplete : ∀ χ left right, stateRelated χ left right →
    stateRelated χ⁻¹ right left

structure ConfluenceResult (State : Type u) (Trace : Type v) (Episode : Type u)
    (Name : Type w) (envelope : ConfluenceEnvelope State Trace Name Episode)
    (left right : Trace) where
  permutation : Equiv.Perm Name
  state_related :
    envelope.stateRelated permutation (envelope.endpoint left) (envelope.endpoint right)
  episode_related :
    envelope.episodeRelated permutation (envelope.episode left) (envelope.episode right)

def EndpointConfluent (State : Type u) (Trace : Type v) (Name : Type w)
    (Episode : Type u) (envelope : ConfluenceEnvelope State Trace Name Episode) : Prop :=
  ∀ left right, envelope.admissible left → envelope.admissible right →
    envelope.nonfailed left → envelope.nonfailed right → envelope.sameInputs left right →
      envelope.sameWitnesses left right → envelope.canonical (envelope.endpoint left) →
        envelope.canonical (envelope.endpoint right) →
          Nonempty (ConfluenceResult State Trace Episode Name envelope left right)

def UniqueNormalForm (State : Type u) (Trace : Type v) (Name : Type w)
    (Episode : Type u) (envelope : ConfluenceEnvelope State Trace Name Episode) : Prop :=
  ∀ left right, envelope.admissible left → envelope.admissible right →
    envelope.canonical (envelope.endpoint left) → envelope.canonical (envelope.endpoint right) →
      envelope.sameInputs left right → left = right

end

end STC.Control
