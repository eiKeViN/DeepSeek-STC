# P13-T01B Lane Handoff

* Scope: `STC/Core/Coeffect.lean`, `STC/Examples/PrerequisiteCoeffect.lean`.
* Result: T01B closed.  Store algebra completed with distinct-key frame laws
  (`insert_frame`/`erase_frame`) and domain laws (`domain_insert`/
  `domain_erase`); witnessed get/provide/revoke transitions gain distinct-key
  frame laws (`provideStep_frame`/`revokeStep_frame`); the typed key-local
  interface is lifted to store-level partial operations (`liftGet`,
  `liftProvide`, `liftRevoke`, `liftKeyLocal`) with definedness, frame, and
  restoration laws; semantic satisfaction stays distinct from its finite
  checkers — the paper-form `declaredSatisfied`/`declaredCheck` (finite
  declaration set) and the binding-quality `Satisfies`/`satCheck` now carry a
  **constructive** `decidableSatisfies` (per-binding decidability over the
  finite store domain; no `Classical` oracle), with checked
  soundness/completeness adequacy theorems.
* Evidence: `I K E`; the checker-equivalence gap under finite-support premises
  is closed.  The `SATProfile` consumer carrier is unchanged.
* Focused gate: `lake build STC.Core.Coeffect STC.Examples.PrerequisiteCoeffect`
  + strict per-file `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true`
  (exit 0, zero warnings); no sorry/admit/axiom/unsafe; full `lake build` green.
* Proposed ledger deltas (central integration, not applied here): D22–D25 →
  `completed/proved`; SAT → `completed/proved` with `deferred_reason` noting
  the checker is adequate under its stated per-binding-decidable premises and
  no deterministic checker is identified with the relational specification.
