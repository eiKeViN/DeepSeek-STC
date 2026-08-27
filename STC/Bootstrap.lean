import Mathlib.Data.Multiset.Defs

/-!
# STC production bootstrap

P0 checkpoint: no P1 production modules exist yet, so this file imports only
Mathlib and runs the root smoke check.  It is the package entrypoint actually
checked by `lake build` (via the root `STC.lean`).

Rules that must hold as production modules appear:

* import production `STC/...` modules only — never the historical ADR spikes
  under `docs/blueprint/architecture-decision/lean-spike/`;
* no placeholder proofs, custom axioms, or unchecked code in active
  declarations (checked by `scripts/scan_lean.py`, which scans for the four
  forbidden markers).
-/

namespace STC

#eval 1

end STC
