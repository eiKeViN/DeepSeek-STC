# T02R2-T03R Signature Candidate (pause-report draft)

Responds to `docs/plans/P13/T02R2-T03R-Semantic-Repair-Brief.md` §3–§4.
Candidate only — nothing implemented.  Pause per brief §8 before implementation.

## A. §4.8 — operation labels (endpoint-free) + replayable factorization

Principle: a label names an OPERATION (codes/tokens/target only).  Every
state-valued payload (after/result/landed/middle) moves OUT of the label into
rule-level existential witnesses bound by the semantic result.  The same
operation re-applied at another source executes the body THERE.

New `GlobalLifecycleLabel`:

```lean
| begin (owner) (ω)                                  -- launch token bound by witness
| iter (owner) (next)
| finish (owner)                                     -- halt result bound by witness
| divertAbort (owner) (boundary)
| divertLand (owner) (landingToken)                  -- landed state + inverse bound by witness
| raise (owner)                                      -- failing stage result bound by witness
| leave (owner)
| unload (owner)                                     -- accumulator middle bound by witness
```

Rule signatures (iter as the template):

```lean
| iter {before after : GState} {owner} {next} {cell} {inverse} :
    (hlook : lookup owner before.registry = some cell) →
    (hphase : cell.phase = .reloading) →
    (htarget : TargetViewAt before owner cell.committedView) →
    (hstage : sem.stage cell.payload.iteratorCode before = some (.yield after inverse next)) →
    (hrank : sem.rank next < sem.rank cell.payload.iteratorCode) →
    LifecycleRule sem (.iter owner next) before (iterState sem after owner inverse next)
```

`after`/`inverse` are constructor-local existentials, witnessed by `hstage`.
Same pattern: finish (`.halt result finalInverse`; successor composes the
final inverse per §4.4 and clears flight), divertLand (`sem.landing landingToken
before = some ⟨landed, inverse⟩` per §3.3; successor composes that inverse),
unload (`sem.accumulator code before = some middle`), begin (launch witness
binds the flight token), raise (`sem.stage … = some (.raise fresult)` with the
complete error/boundary/prefix data per §3.4).

Factorization (explicitly relational, per the brief's allowance):

```lean
def SelectedBody (sem) : Sum OLabel LLabel → GState → GState → Prop
  | .inr (.iter owner next), before, middle =>
      ∃ cell inverse, lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ TargetViewAt before owner cell.committedView ∧
        sem.stage cell.payload.iteratorCode before = some (.yield middle inverse next) ∧
        sem.rank next < sem.rank cell.payload.iteratorCode
  | .inr (.unload owner), before, middle =>
      ∃ cell, lookup … ∧ cell.phase = .unloading ∧ ¬ ReliedUpon … ∧
        sem.accumulator cell.payload.accumulatorCode before = some middle
  | -- identity bodies keep middle = before; finish/divertLand carry the
    -- stage/landing witness with middle = the result state
  …

def ControlEdit (sem) : Sum OLabel LLabel → GState → GState → Prop
  | .inr (.iter owner next), middle, after =>
      ∃ inverse, after = iterState sem middle owner inverse next
  | .inr (.unload owner), middle, after => after = unloadState middle owner
  …
```

Nonconstant evidence, ONE fixed operation (replaces the rejected cross-label
patch `factorization_nonconstant`):

```lean
theorem factor_replay_nonconstant :
    ∃ label b1 b2 m1 m2, SelectedBody sem label b1 m1 ∧
      SelectedBody sem label b2 m2 ∧ m1 ≠ m2
-- label := .inr (.iter 2 0); b1 := s6 (ambient 8 → yield 7);
-- b2 := { s6 with ambient := 9 } (→ yield 8); guards hold at both.
```

Replay: `factor_iter` proves `LifecycleRule sem (.iter owner next) before after
↔ ∃ m, SelectedBody (.iter owner next) before m ∧ ControlEdit (.iter owner next) m after`.

## B. §4.9 — R.base as a genuine ADR-08 macro specialization

```lean
def baseOrchestration : OLabel → GState → GState → Prop
  | .insert registrar fresh child, b, a => OrchestrationRule (.insert registrar fresh child) b a
  | .retire owner cell, b, a          => OrchestrationRule (.retire owner cell) b a
  | .remove owner, b, a              => OrchestrationRule (.remove owner) b a

def baseLifecycle (sem) : LLabel → GState → GState → Prop
  | .begin owner ω, b, a => ∃ m f, LifecycleRule sem (.begin owner ω) b m ∧   -- launch binds f
      LifecycleRule sem (.finish owner) m a                                    -- Reload = Begin·Finish
  | .unload owner, b, a => ∃ m, LifecycleRule sem (.leave owner) b m ∧
      LifecycleRule sem (.unload owner) m a                                    -- Unload = Leave·Unload
  | _, _, _ => False
```

No singleton equivalence; intermediate Reloading/Unloading states are not base
states; stutter only through the explicit `StutterProfile` when the projected
base observation is unchanged; adequacy via `Staging.MacroPath` over the
`[begin, finish]` / `[leave, unload]` macros.

## C. §3 — T02R2 interface deltas (one line each; brief's own spec)

* `rank : Iterator → Nat`; `rank_law` on the YIELD result: `rank next < rank current`.
  Fixture rank := iterator code, not ambient.
* `landing : Flight → State → Option (LandingResult …)` where the result binds
  source, landed state, inverse, optional failure.
* failure through `sem.stage … = some (.raise fresult)`; `fresult` carries
  error, boundary, prefix-undo.  Remove `sem.failure … = some before`.
  Fixture `Failure := Nat` (error code), not Unit.
* `action : Action → State → Option (ActionResult …)`; the action result carries
  the retirement inverse used by O-Retire (§4.7).
* Body-frame laws with concrete premises: stage/landing/accumulator do not
  change registry domain, ledger, or history; foreign fibers framed; writes
  within the acting provision envelope; reads respect the observed coeffect
  window; cleanup meets the owner/recorded-child cleanup frame.  Instantiated
  non-vacuously in the fixture (no `True` fields).

## D. Open questions for the lead (need answers before implementation)

1. O-Retire inverse: §4.7 wants the ACTION result connected to the retire
   inverse.  Proposed: O-Insert witnesses `sem.action code before = some
   ⟨inverse⟩` (during allocate), and O-Retire's label carries that inverse
   token — retire label becomes `.retire owner inverse` instead of
   `.retire owner beforeCell`.  Confirm or amend.
2. L-Begin: proposed label drops the flight token (launch witness binds it).
   Alternative: keep the token in the label (it is an input, not an endpoint).
   Which does the lead prefer?
3. StageResult raise branch: reuse the existing `.raise` constructor with the
   enriched failure payload, or a separate `StageOutcome` relation?

## E. Worktree note

Per brief §8: fresh worktree from `origin/main` (`1327ceb0`).  The branch
commits `72592ab`/`163cda8` stay in history as reference (patterns: lookup
lemmas, `s*_views` helpers, anchor tool); nothing is deleted.


## Lead rulings (2026-09-02) — candidate accepted with amendments

### D1 — O-Retire label endpoint-free

`OrchestrationLabel` becomes:

```lean
| insert (registrar) (fresh) (child)
| retire (owner)
| remove (owner)
```

`beforeCell` moves out of the label into a local lookup witness of
`OrchestrationRule.retire`.  Registration primitive returns a canonical result:

```lean
inductive RegistrationUndo (Name) | retire (owner : Name)
structure RegistrationResult (Name) where fresh : Name; inverse : RegistrationUndo Name
```

with the fixed linkage `inverse = .retire fresh`, and the interpretation
theorem: the inverse realizes exactly `retireState state fresh` — the
authoritative `O-Retire fresh` state transform.  Distinctions: O-Insert label =
orchestration input only; the registration RESULT returns the canonical
retirement inverse; the nested action/iterator witness proves it called this
O-Insert and folded the returned inverse into the parent accumulator; the
external orchestrator may ignore the return.  No arbitrary `Action` token may
claim to be the inverse — a generic `Action` needs an explicit
`RegistrationInverseAdequate action fresh` bridge.  No per-O-Insert
`sem.action …` premise; domain growth is always O-Insert's own job.

### D2 — L-Begin label without flight token

`begin (owner) (ω)`; the flight token is an internal `sem.launch` witness at
that state, not an orchestration input nor a stable operation name.  The same
resolved witness connects `sem.launch before = some flight` to the successor
storing that token.  T04's `SameResolvedSemanticWitnesses` compares launch
tokens separately; they never enter `SameOrderedOrchestrationInputs`.

### D3 — keep core `StageResult.raise`; bridge at lifecycle

`sem.stage current before = some (.raise error)` stays core.  A bridge

```lean
FailureFromStage sem cell before error failure
```

constructs `failure.error = error`, `failure.boundary = before`,
`failure.prefixUndo = <accumulated prefix in cell>` — the stage reports only
the current error; boundary and prefix are iterator-execution context.  And
the L-Raise label KEEPS the complete failure:

```lean
.raise owner failure
```

Amended endpoint-free principle: success endpoints (`after/result/landed/
middle`) never appear in labels; rule-mandated inputs, choices, and COMPLETE
FAILURE EVIDENCE remain in labels.

### Factorization — one resolved witness threads both sides

The two-sided `∃ inverse` split is rejected.  Required shape:

```lean
∃ witness, SelectedBody sem label before witness ∧ ControlEdit sem label witness after
```

(at minimum `∃ middle inverse, SelectedBody … before middle inverse ∧
ControlEdit … middle inverse after`), uniformly for Iter, Finish, DivertLand,
Unload.  The body-returned inverse must be provably the inverse the control
edit uses.
