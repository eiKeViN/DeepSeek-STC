# P13-T05B Lane Handoff

* Scope: `STC/Control/Recovery.lean`, `Examples/GlobalRecovery.lean`.
* Result: inverse, continuation, landing, cleanup, and no-child recovery
  envelopes are explicit, but no unrestricted lifecycle recovery is proved.
* Evidence: `I`; concrete interpreter and continuation laws remain open.

## T02R2/T03R migration note (2026-09-04)

* The old `stage_inverse` equality was judged too strong and DELETED in the
  T02R2/T03R repair (`Component.lean` documents the rationale: a yielded
  inverse is data recorded by the control edit, not a stage-undo; the
  nested-registration inverse alone is interpreted by
  `RetireInverseAdequate`).
* The relation-indexed observational recovery obligation for ARBITRARY
  stage/finish/landing inverses is MIGRATED here as T05B's required recovery
  profile. T03 proves only inverse source binding, threading, and LIFO
  composition.
* Citable fixture evidence (see `T02R2-T03R-handoff.md`): the nonempty
  landing inverse `[7]` composed LIFO onto a real prefix (`[7,1]`), the
  success-trace endpoint `[3,2,1]` with the noncommutativity theorems, and
  the guarded D48 coeffect write at key 12. `GlobalRecovery.lean` does not
  import the fixture; the profile stays abstract here.
