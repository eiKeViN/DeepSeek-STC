# P13 Semantic API Reopen Report

| Field | Value |
|---|---|
| Plan | `DH-P13-GLOBAL-METATHEORY-EXEC-01` |
| Continuation base | `7100e07` (`origin/main`) |
| Continuation branch | `codex/p13-completion-20260829` |
| Status | blocked at the T03/T05A/T05D semantic-freeze boundary |
| Classification | accepted-architecture integration gap |

## Trigger

The fresh integrated build and ancestry/ADR gates pass, but two concrete
authoritative-rule witnesses contradict later mandatory P13 proof interfaces.
The counterexamples are kernel checked in
`STC/Examples/GlobalStructural.lean`.

### T59 parent-closure preservation

`orchestrationRule (.insert fresh cell)` currently requires only that `fresh`
is absent from the live registry and lifetime ledger. It imposes no parent
closure guard. The checked witness `orphan_insert_rule` inserts a fresh cell
whose parent is absent into the empty, parent-closed state. The successor is
not parent closed, and `no_parentClosed_orchestration_preservation` proves
that parent-closure preservation cannot be derived from the current rule.

This blocks the required T05A proof of global WellFormed preservation. Adding
`WellFormed after` as a rule premise or as a `StructuralLaws` field would hit
the plan's explicit stop condition and would turn T59 into an assumption.

### T66 strict lifecycle progress

The current `.iter` rule maps a reloading cell to the same reloading state.
`iterator_self_loop` inhabits that rule, and `no_strict_lifecycle_measure`
proves that no natural-number measure can strictly decrease on every current
lifecycle step. The rule does not consume ranked-iterator state or advance an
iterator code, so ADR-05's rank theorem cannot discharge this contradiction.

This blocks the mandatory T05D well-founded lifecycle relation, trace bounds,
termination, and endpoint-quiescence theorem.

## Smallest required reopen

1. Strengthen the insert/remove/unload rule vocabulary with local structural
   guards sufficient for parent closure, parent acyclicity, declaration/frame
   discipline, and child-safe removal. These must be local premises, not the
   desired successor `WellFormed` conclusion.
2. Replace the `.iter` stutter with an explicit ranked iterator transition
   carrying a successor code/state and a checked strict-rank premise. A
   separately tagged Staging stutter may remain outside lifecycle progress.
3. Re-freeze `STC/Control/Rules.lean`, update all constructor witnesses, and
   then re-run T04 through T08. Existing profile fields are interface evidence
   only and cannot be promoted to L54/T59/T66 proofs.

The accepted ADR direction, positive support LFP, state positivity, and
lifetime freshness do not need to change. The missing information is in the
concrete rule guards and iterator transition payload.

## Other residual obligations

The prior P13 handoff remains accurate for L18/T20/C21, constructive SAT,
per-rule factorization, reachable L68, derived L70, adjacent swaps, L72, T73,
and the full two-fiber vertical slice. Those tasks cannot complete against a
rule API that already prevents T59 and T66.

No frozen baseline, accepted ADR artifact, or P11/P12 API is changed. The
Definition Ledger updates only T59 and T66 to record these checked blockers.
