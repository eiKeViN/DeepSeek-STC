import STC.Core.Effect
import STC.Core.EffectCode
import STC.Examples.Effect
import STC.Examples.RelationResult
import STC.Examples.State
import STC.Foundation.Relation
import STC.Foundation.Result
import STC.State.CoeffectStore
import STC.State.FinmapAdapter
import STC.State.Like
import STC.State.Observation
import STC.State.RegistryLike
import STC.State.Toy

/-!
# STC production bootstrap

This cumulative checkpoint imports the relation/result foundations, shallow
reversible Effect kernel, P5 state/observation/registry interfaces, and their
finite executable checks. It is the package entrypoint checked by `lake build`
through the root `STC.lean`.

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never historical ADR spikes;
* keep executable checks finite and preserve all result fields;
* keep the selected relation explicit in semantic declarations.
-/
