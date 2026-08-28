import STC.Foundation.Relation
import STC.Foundation.Result
import STC.Examples.RelationResult
import STC.Core.Effect
import STC.Core.EffectCode
import STC.Examples.Effect

/-!
# STC production bootstrap

Bootstrap checkpoint: this file imports the canonical relation/result foundations,
plus the shallow reversible Effect kernel and their finite executable checks.  It is the package entrypoint actually
checked by `lake build` (via the root `STC.lean`).

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never historical ADR spikes;
* keep executable checks finite and preserve all result fields;
* keep the selected relation explicit in semantic declarations.
-/

/-!
P2 integration checkpoint: this cumulative bootstrap also imports the shallow
reversible Effect kernel, its type-parametric R0 seam, and the finite Effect
fixtures used for executable and negative evidence.
-/
