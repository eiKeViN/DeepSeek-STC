# P13-T02R2/T03R Lane Handoff (complete, 2026-09-04)

* Branch: `codex/t02r2-t03r` (pushed to origin). Base: T02R repair + T03
  surface; this lane repairs the T03R signature breakage and rebuilds the
  anti-vacuity fixture, then re-freezes T03 and releases T04.
* Versions: base `1327ceb0`; implementation tip `6155898`; re-freeze
  documentation commit `b5964c1`.
* Commits (in order): interface tasks 1-5 `ba61a15..d238c8e`; review blockers
  `c4eec65`, cleanup-adequacy premise `0e56510`; fixture rebuild
  `82ebb39`, `eedca57`, `d0a19bc`, `08c1272`; block 4c splice `f4f1769`;
  three-file split `96d28c4`; anti-vacuity stage codes `7742455`; nonempty
  landing inverse + computable write guard `7a6c2ed`; mini-trace witnesses
  `dbd30d9`; derived evidence `6155898`.

## Signature changes vs the superseded T03 (72592ab era)

* `ComponentSemantics` takes `Key` first (explicit); `FailureEvidence` added
  (`error`/`boundary`/`prefixUndo`); the stage failure carrier is `Error`;
  `FailureFromStage` replaces the old failure bridge; `stage_inverse` and the
  old `failureBridge_law` are DELETED (see recovery boundary below).
* Envelope fields: `stageEnvelope`/`landingEnvelope`/`accumulatorEnvelope`/
  `actionEnvelope`; `writesWithinProvision : Finset Key → State → State → Prop`;
  `domainFrame`; `BodyFrameAdequacy` carries `provision_coeffectFrame`,
  `observes_readRespect`, `accumulator_domain_total`, and
  `accumulator_cleanupFrame` with the state-level recorded-children premise.
* `NestedRegistrationWitness`, `StagingStable`/`StableBase`, endpoint-free
  labels, `GlobalLifecycleLabel Nat Nat Nat Unit (FailureEvidence State Nat
  (List Nat))`; `divertAdmissible` (A.async) with the landing-token shape.

## Recovery boundary (precise)

* T03 proves inverse SOURCE BINDING, THREADING, and LIFO COMPOSITION only
  (yield/halt/landing inverses recorded on labels, threaded through
  `composeInverse`, observed by the mini-trace endpoints `[3,2,1]`/`[7,1]`).
* The nested-registration inverse IS interpreted by `RetireInverseAdequate`
  (the action's `inverse?` records the child-retirement inverse; the fold
  executes it). This does NOT extend to arbitrary stage/finish/landing
  inverses.
* ARBITRARY stage/finish/landing inverse observational recovery is MIGRATED
  to T05B as the relation-indexed recovery profile obligation (see
  `T05B-handoff.md`); no `StageInverseAdequacy` was added to T03.

## Unload ownership (precise)

* The recorded-child ownership of foreign unload edits is a CALLER premise:
  `unload_full_cleanupFrame` takes the `hchildren` proof and
  `unload1_cleanupFrame` supplies it. `LifecycleRule.unload` alone does NOT
  guarantee the D48 cleanup shape; this is declared a component/profile
  obligation in the freeze, never an automatic unload property.

## Fixture inventory (anti-vacuity acceptance gate)

* (a) Nonempty inverse/failure evidence: finish final inverse `[3]`
  (halt code 4), landing inverse `[7]` composed onto real prefixes, raise
  `prefixUndo := [1]` preserved through `raiseState`.
* (b) LIFO composition: the success mini-trace `[] →Iter[1]→ [1]
  →Iter[2]→ [2,1] →Finish[3]→ [3,2,1]` plus the explicit noncommutativity
  theorems (`composeInverse [1] [2] ≠ composeInverse [2] [1]`, endpoint ≠
  reverse-composed `[1,2,3]`); landing `[7,1] = [7] ++ [1]`.
* (c) D48 coeffect-write confinement: code 8 writes key 12 inside
  `cellDW.component.provides` under the computable guard (`stageGuard12`,
  `Multiset.foldr` over the registry entries — NO classical/choice
  anywhere; `noncomputable` count in the fixture files: 0), with
  `d48_wrote12` (12: none → some 0), `d48_write_nontrivial`,
  `d48_outOfEnvelope` (key 10 unchanged), and the
  `iter_full_writeFrame`/`iter_full_readNoninterference` discharges.
* The four mini-traces are independent authoritative traces
  (Begin→Iter→Iter→Finish; Begin→Iter→Raise; provider-active →
  consumer Begin/Iter → provider Retire/Leave → consumer DivertLand;
  insert/begin/iter-write) over fresh cells 6/7/8/9/11 and codes 4/5/6/8/9/10;
  the s0..s27 main chain and the ADR-09 cycle are untouched except the
  landing-inverse `[7]` ripple.

## Superseded T03 claims

* The old `rulesSem` description in `T03-handoff.md` (ambient-counter stage,
  inverse := 1, composeInverse := +) is superseded; the fixture is now
  code-ranked with list accumulators (`b ++ a`, identity `[]`,
  `foldRetire` LIFO folds).
* The old same-label `factorization_nonconstant` shape is replaced by
  `factor_replay_nonconstant` (cross-label non-constancy).
* The fixture is now three modules: `STC/Examples/GlobalRules/{Semantics,
  Trace,Evidence}.lean`; the monolithic `GlobalRules.lean` is removed and
  `Bootstrap.lean`/`Examples/Global.lean` import the three.

## Gates (all green, 2026-09-04)

* `lake build` — 3092 jobs, zero warnings; each fixture module
  `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true` zero errors,
  zero warnings.
* `scripts/scan_lean.py STC` exit 1 (clean); ledger 82/82 PASS (examples are
  not ledger-scoped); `git diff --check` clean.
* T03 re-frozen / T04 released in `P13-api-freeze.md` with fresh module
  SHA-256 prefixes.

## Remaining T04 work / blockers

* T04 still needs: per-rule factorization closure, write/read frame-law
  completion, activation-provenance preservation (recorded, not completed).
* T05B now owns the relation-indexed recovery profile; its stub notes the
  citable fixture evidence (landing inverse `[7]`, LIFO composition, the D48
  write) but `GlobalRecovery.lean` does not import the fixture.
* No blockers.
