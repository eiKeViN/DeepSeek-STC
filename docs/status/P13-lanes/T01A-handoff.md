# P13-T01A Lane Handoff

* Scope: `STC/Core/Effect/Closure.lean`, `STC/Core/Partial/Recovery.lean`,
  `STC/Examples/PrerequisiteRecovery.lean`.
* Result: T01A derivation closed.  D17 generated-submonoid unit/assoc laws and
  the no-new-generators closure principle; L18 `CommutationClosure` derived
  from generator-wise commutation plus explicit respects (no longer a field);
  T20 selective removal proved at total-effect level; C21 arbitrary-order
  (`List.Perm`) inverse recovery proved under an explicit pairwise
  inverse-commutation premise; finite fixture with two independent operations
  (increment/flip over `Nat × Bool`) exercises lawfulness, the audited
  independence contract, removal, and both inverse orders.
* Evidence: `I K E`; lifecycle continuation stability remains open (T05B/T05E,
  per plan §7 the map-commutes-but-continuation-changes counterexample belongs
  there).
* Focused gate: `lake build STC.Core.Effect.Closure STC.Core.Partial.Recovery
  STC.Examples.PrerequisiteRecovery` + strict per-file
  `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true` (all exit 0,
  zero warnings); no sorry/admit/axiom/unsafe.
* Proposed ledger deltas (central integration, not applied here): D17 →
  `completed/proved`; L18, T20, C21 → `completed/proved` with
  `deferred_reason` noting the T05B/T05E selection-stable corollaries.
