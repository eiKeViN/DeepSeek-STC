# P13-T01C Lane Handoff

* Scope: `STC/Foundation/Relation/Transport.lean`,
  `STC/State/Positive.lean`, `STC/State/Observation/Lift.lean`, and the
  prerequisite state example.
* Result: in-progress relation-map/optional transport, positive cell/context
  carriers, and independent registry/committed/lifecycle/control/name
  observations.
* Evidence: `I K E`; the full L38 join remains open and no runtime refinement is claimed.
* Focused gate: `lake build STC.Foundation.Relation.Transport STC.State.Positive
  STC.State.Observation.Lift STC.Examples.PrerequisiteState`.

## T01C prerequisite check (2026-08-30, post T01A/T01B)

The T01-join gate requires the twelve transitive prerequisites
`D17 L18 T20 C21 D22 D23 D24 D25 SAT D32 D33 L38` to have complete
downstream-usable declarations.  Status:

| Row | Declaration(s) | Module | Ledger row | Check |
|---|---|---|---|---|
| D17 | `Generated` submonoid + unit/assoc/no-new-generators laws | `STC/Core/Effect/Closure.lean` | `in_progress/aligned` | PASS; propose `completed/proved` |
| L18 | `commutationClosure_of_generators` (derived from generator commutes + respects) | `STC/Core/Effect/Closure.lean` | `in_progress/seam_only` (stale note: "derivation not yet proved") | PASS; propose `completed/proved` |
| T20 | `selective_removal` (total-effect, explicit inverse-commutation premises) | `STC/Core/Effect/Closure.lean` | `in_progress/seam_only` (stale) | PASS; propose `completed/proved`; selection-stable lift from `OperationIndependenceContract` remains T05B/T05E |
| C21 | `arbitrary_order_recovery` (`List.Perm`) | `STC/Core/Partial/Recovery.lean` | `in_progress/pending` (stale) | PASS; propose `completed/proved` |
| D22 | P5 store + algebra/frame/domain laws | `STC/State/CoeffectStore.lean`, `STC/Core/Coeffect.lean` | `in_progress/proved` | PASS |
| D23 | `GetStep`/`ProvideStep`/`RevokeStep` + lookup/frame/restore laws | `STC/Core/Coeffect.lean` | `in_progress/aligned` | PASS; propose `completed/proved` |
| D24 | `CoeffectOps` + `liftGet`/`liftProvide`/`liftRevoke`/`liftKeyLocal` laws | `STC/Core/Coeffect.lean` | `in_progress/seam_only` (stale note: "context lift not complete") | PASS at the audited shape; propose `completed/proved` (definedness-level respect laws; value relations need further premises) |
| D25 | `Satisfies`/`satCheck` distinct from relational spec | `STC/Core/Coeffect.lean` | `in_progress/aligned` | PASS; propose `completed/proved` |
| SAT | paper-form `declaredSatisfied`/`declaredCheck` + constructive `decidableSatisfies` + adequacy | `STC/Core/Coeffect.lean` | `in_progress/seam_only` (stale note: "constructive checker open") | PASS; propose `completed/proved` |
| D32 | `PositiveCell`/`PositiveRegistry`/`PositiveContext` generic carrier; concrete `GlobalState` | `STC/State/Positive.lean`, `STC/State/Global.lean` | `in_progress/seam_only` | PASS at interface level; D32 completion evidence stays with T02 |
| D33 | `ObservationKit`/`liftedStateObs` + `Global.Observation` | `STC/State/Observation/Lift.lean`, `STC/State/Global/Observation.lean` | `in_progress/proved` | PASS |
| L38 | `RelMap`/`relMap_id`/`relMap_comp`/`optionRel_map`/`PointwiseMap` transport family | `STC/Foundation/Relation/Transport.lean` | `in_progress/proved` | PASS at the plan's audited strength (transport family); a blanket "every Section-3.1 equality transports" is not a Lean proposition (H04 L38 = generalization/SUBSUMED) |

No sorry/admit/axiom/unsafe in any of the twelve modules.  All rows with
"propose" deltas have the exact patch recorded in the T01A/T01B lane handoffs;
the ledger itself is central-integration owned and is not edited by this lane.

**Gate conclusion**: the T01 join prerequisites are declaration-complete;
T01C may proceed.  The remaining T01C obligations are the abstract
context/observation join packaging and freezing the D32/D33 generic
interfaces for T02.
