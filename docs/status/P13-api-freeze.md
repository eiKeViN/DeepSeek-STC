# P13 API Freeze

| Field | Value |
|---|---|
| Plan | `DH-P13-GLOBAL-METATHEORY-EXEC-01` |
| Base | `96b8752` (`P13 plan added`) |
| Freeze state | review checkpoint; final T02/T03/T04 freeze remains open |
| Toolchain | Lean 4.33.0 / Mathlib v4.33.0 |

## Current production surface

The P13 production graph is additive and data-positive:

```text
Core/Effect/Closure + Core/Partial/Recovery + Core/Coeffect
  -> State/Positive + State/Observation/Lift + Relation/Transport
  -> State/Component + State/Fiber + State/Global + Global/Observation
  -> Control/Rules -> Control/Reachability + Control/Episode
  -> Control/Structural, Preservation, Recovery, Support, Spatial, Progress,
     Alpha, Commutation -> Control/Deletion -> Control/Canonical
  -> Conformance/Global
```

The carrier retains `NameLedger.everIssued` and an ordered `allocationHistory`.
`GlobalState` stores only finite maps, records, codes, phases, and data. The
semantic interpreter/profile fields are external to the carrier. `fullRule` is
the sole union of `orchestrationRule` and `lifecycleRule`; `withdrawRule`,
`iterationRule`, and `failureRule` are derived constructor views.

## Signature inventory

* `STC.State.GlobalState`, `WellFormedProfile`, `WellFormed`, `ProvidesNow`,
  `ProviderModel`, `TargetView`, `Quiescent`.
* `STC.Control.GlobalOrchestrationLabel`, `GlobalLifecycleLabel`,
  `orchestrationRule`, `lifecycleRule`, `fullRule`, `globalControlModel`.
* `STC.Control.InitialProfile`, `ReachedFrom`, `Reachable`, `Episode`,
  `ActivationProvenance`, `GrowingBijection`, `RelatedCell`,
  `SameOrderedOrchestrationInputs`,
  `SameResolvedSemanticWitnesses`.
* `STC.Control.StructuralLaws`, `PreservationProfile`, `RecoveryProfile`,
  `SpatialProfile`, `ProgressMeasure`, `RuleAlphaProfile`, `DiamondProfile`,
  `DeletionEnvelope`, `CanonicalEnvelope`, `ConfluenceEnvelope`.
* `STC.Conformance.p13Entries`, `p13Deferred`, and `globalManifestShape`.

No frozen upstream file was edited. This inventory is not the final semantic
freeze: per-rule factorization, write/read frame laws, and activation-provenance
preservation must close before T05 theorem lanes can rely on these signatures.
