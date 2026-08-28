module

public import STC.Core.Effect
public import STC.Core.EffectCode
public import STC.Examples.Effect
public import STC.Examples.RelationResult
public import STC.Examples.State
public import STC.Foundation.Relation
public import STC.Foundation.Result
public import STC.State.CoeffectStore
public import STC.State.FinmapAdapter
public import STC.State.Like
public import STC.State.Observation
public import STC.State.RegistryLike
public import STC.State.Toy

/-!
# STC production bootstrap

This cumulative checkpoint imports the relation/result foundations, shallow reversible
Effect kernel, P5 state/observation/registry interfaces, and finite elaboration-time
checks. It is the package entrypoint checked by `lake build` through root `STC.lean`.

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never historical ADR spikes;
* keep executable checks finite and preserve all result fields;
* keep the selected relation explicit in semantic declarations.

## Main declarations

* `STC.RelSpec`, `STC.RespectsOn`, `STC.PointwiseRel`: the relation foundation;
* `STC.EffectResult`, `STC.ExecResult`, `STC.Effect`, `STC.seqRun`: the effect kernel;
* `STC.IsLawfulEffect`: the effect-law record;
* `STC.StateLike`, `STC.ObservationProfile`: abstract state observations;
* `STC.RegistryLike`, `STC.ToyRegistry`: finite registry interfaces;
* `STC.Coeffect.Store`: the dependent coeffect façade;
* `STC.State.FinmapAdapter.RawState`: the state-side ADR-03 R0 seam.
-/
