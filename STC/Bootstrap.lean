module

public import STC.Alpha.Transport
public import STC.Conformance.Global
public import STC.Control
public import STC.Control.Alpha
public import STC.Control.Canonical
public import STC.Control.Commutation
public import STC.Control.Deletion
public import STC.Control.Episode
public import STC.Control.Preservation
public import STC.Control.Progress
public import STC.Control.Reachability
public import STC.Control.Recovery
public import STC.Control.Rules
public import STC.Control.Spatial
public import STC.Control.Structural
public import STC.Control.Support
public import STC.Control.Support.Quiescence
public import STC.Control.Support.Reachable
public import STC.Core.Coeffect
public import STC.Core.Effect
public import STC.Core.Effect.Closure
public import STC.Core.EffectCode
public import STC.Core.Iterator
public import STC.Core.Partial
public import STC.Core.Partial.Recovery
public import STC.Examples.Alpha
public import STC.Examples.Control
public import STC.Examples.Effect
public import STC.Examples.Global
public import STC.Examples.GlobalAlpha
public import STC.Examples.GlobalConfluence
public import STC.Examples.GlobalDeletion
public import STC.Examples.GlobalModel
public import STC.Examples.GlobalProgress
public import STC.Examples.GlobalRecovery
public import STC.Examples.GlobalRules.Semantics
public import STC.Examples.GlobalRules.Trace
public import STC.Examples.GlobalRules.Evidence
public import STC.Examples.GlobalStructural
public import STC.Examples.PrerequisiteCoeffect
public import STC.Examples.PrerequisiteRecovery
public import STC.Examples.PrerequisiteState
public import STC.Examples.RelationResult
public import STC.Examples.Scoped
public import STC.Examples.Staging
public import STC.Examples.State
public import STC.Examples.Support
public import STC.Examples.SupportCycle
public import STC.Examples.SupportTrace
public import STC.Examples.TwoCounter
public import STC.Examples.VerticalSlice
public import STC.Foundation.Relation
public import STC.Foundation.Relation.Transport
public import STC.Foundation.Result
public import STC.Scoped
public import STC.Staging
public import STC.Staging.Support
public import STC.State.CoeffectStore
public import STC.State.Component
public import STC.State.Fiber
public import STC.State.FinmapAdapter
public import STC.State.Global
public import STC.State.Global.Observation
public import STC.State.Like
public import STC.State.Observation
public import STC.State.Observation.Lift
public import STC.State.Positive
public import STC.State.RegistryLike
public import STC.State.Support
public import STC.State.Support.Alpha
public import STC.State.Support.Closure
public import STC.State.Toy

/-!
# STC production bootstrap

This cumulative checkpoint imports the relation/result foundations, reversible Effect
kernel, state/observation/registry interfaces, Control and derived Staging surfaces,
the positive support closure and alpha/trace bridges, and finite elaboration-time
checks. It is the package entrypoint checked by `lake build` through root `STC.lean`.

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never historical ADR spikes;
* keep executable checks finite and preserve all result fields;
* keep the selected relation explicit in semantic declarations.

## Main declarations

* `STC.RelSpec`, `STC.RespectsOn`, `STC.PointwiseRel`: the relation foundation;
* `STC.EffectResult`, `STC.ExecResult`, `STC.Effect`, `STC.seqRun`: the effect kernel;
* `STC.IsLawfulEffect`: the effect-law record;
* `STC.OpResult`, `STC.PartialOp`, `STC.OperationIndependenceContract`: the partial
  operations, independence, and failure bridges;
* `STC.RankedIterator`, `STC.execFrom`: the ranked continuation machine;
* `STC.StateLike`, `STC.ObservationProfile`: abstract state observations;
* `STC.RegistryLike`, `STC.ToyRegistry`: finite registry interfaces;
* `STC.Coeffect.Store`: the dependent coeffect façade;
* `STC.Scoped.RealmModel`, `STC.Scoped.Resolver`, `STC.Scoped.scopedLookup`,
  `STC.Scoped.ScopedContext`, `STC.Scoped.FlatEmbedding`: the ADR-10 typed scoped
  coeffect layer over the P5 store;
* `STC.Examples.Scoped.scopedReport`: the finite scoped-coeffect report.
* `STC.State.FinmapAdapter.RawState`: the state-side ADR-03 R0 seam;
* `STC.SupportSnapshot`, `STC.SupportSet`, `STC.SupportOrder`: committed positive
  support closure and rank certificate;
* `STC.renameSnapshot`, `STC.supportSet_rename`: name transport with fixed keys;
* `STC.Control`, `STC.Staging`: labelled Control traces and derived macro view;
* `STC.Control.Support`, `STC.Staging.Support`: conditional certificate bridges;
* `STC.AlphaAction`, `STC.renameIterator`, `STC.execFrom_rename_transport`: the name-neutral
  alpha transport layer (Core/Trace/Transport);
* `STC.NameLedger`, `STC.NameTrace`, `STC.AlphaBoundary`: the trace/freshness boundary;
* `STC.Examples.TwoCounter`, `STC.Examples.VerticalSlice`: the P3/P4 failure and iterator
  fixtures;
* `STC.Examples.Alpha.alphaReport`: the finite swap fixture report.
* `STC.Examples.SupportTrace`: integrated finite support/trace evidence.
-/
