import STC.Foundation.Relation
import STC.Foundation.Result
import STC.Examples.RelationResult
import STC.Core.Effect
import STC.Core.EffectCode
import STC.Examples.Effect

/-!
# STC production bootstrap

P1 checkpoint: this file imports the canonical relation and result foundations
and their finite executable checks.  It is the package entrypoint actually
checked by `lake build` (via the root `STC.lean`).

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never historical ADR spikes;
* keep executable checks finite and preserve all result fields;
* keep the selected relation explicit in semantic declarations.
-/
