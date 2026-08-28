module

public import STC.Core.Effect
public import STC.Core.EffectCode
public import STC.Examples.Effect
public import STC.Examples.RelationResult
public import STC.Foundation.Relation
public import STC.Foundation.Result

/-!
# STC production bootstrap

Bootstrap checkpoint: this file imports the canonical relation/result foundations, plus the
shallow reversible Effect kernel and their finite executable checks.  It is the package
entrypoint actually checked by `lake build` (via the root `STC.lean`).

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never historical ADR spikes;
* keep executable checks finite and preserve all result fields;
* keep the selected relation explicit in semantic declarations.

P2 integration checkpoint: this cumulative bootstrap also imports the shallow reversible
Effect kernel, its type-parametric R0 seam, and the finite Effect fixtures used for
executable and negative evidence.

## Main declarations

* `STC.RelSpec`, `STC.RespectsOn`, `STC.PointwiseRel`: the relation foundation;
* `STC.EffectResult`, `STC.ExecResult`, `STC.Effect`, `STC.seqRun`: the effect kernel;
* `STC.IsLawfulEffect`: the lawfulness record;
* `STC.EffectInterpreter`, `STC.ShallowDeepRefinementSeam`: the R0 seam;
* `STC.Examples.report`, `STC.Examples.EffectFixture.effectReport`: executable fixtures.
-/
