# P13 T02R2 + T03R Semantic Repair Brief

## 0. Task status and decision

Do **not** start or freeze `P13-T04` against the current rule surface.

Audit baseline:

- repository: `eiKeViN/DeepSeek-STC`
- audited branch: `origin/main`
- audited commit: `1327ceb0de2af4a132a6b0f5f10160d03547dc0e`
- merge: PR #19, “T03 completed”

The T03 implementation has a sound overall module shape, but several current
definitions make later recovery, preservation, progress, factorization, and
staging claims false or unprovable. This task performs a coordinated, narrow
reopen of T02R and T03, repairs the authoritative semantics, rebuilds the
fixtures, and re-freezes the API. T04 begins only after the exit gate in
Section 9 passes.

This is an implementation/API conformance repair under the existing accepted
ADRs and P13 plan. Do not introduce a new ADR unless a repaired target remains
false after all existing accepted premises are implemented.

## 1. Authority and required reading

Use the repository's current `AGENTS.md`. Read these files before editing:

1. `docs/plans/P13-Execution-Plan.md`, especially Sections 10–12;
2. `docs/blueprint/architecture-decision/md/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture.md`;
3. `docs/blueprint/architecture-decision/md/DeepSeek-Harness-09-ADR-05-Iterator-and-Failure-Architecture.md`;
4. `docs/blueprint/architecture-decision/md/DeepSeek-Harness-12-ADR-07-Control-Architecture.md`;
5. `docs/blueprint/architecture-decision/md/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.md`;
6. `docs/status/P13-api-freeze.md`;
7. `docs/status/P13-lanes/T02R-handoff.md`;
8. `docs/status/P13-lanes/T03-handoff.md`;
9. `STC/Core/Iterator.lean`, `STC/Control.lean`;
10. `STC/State/Component.lean`, `STC/State/Global.lean`;
11. `STC/Control/Rules.lean`, `STC/Examples/GlobalRules.lean`;
12. the open T04 drafts `STC/Control/Reachability.lean` and
    `STC/Control/Episode.lean`, only to assess compatibility—not to complete
    T04 in this task.

The accepted ADRs and P13 plan take precedence over claims in the existing
T02R/T03 handoff reports. Compilation is interface evidence, not proof that
the chosen semantics is adequate.

## 2. Preserve what is already sound

Retain, unless a type repair mechanically requires renaming:

- the three orchestration constructors;
- the eight concrete lifecycle constructors, with printed Divert represented
  by separate land and abort branches;
- `fullRule` as the sole authoritative orchestration/lifecycle union;
- `withdrawRule`, `iterationRule`, and `failureRule` as derived constructor
  views, not competing relations;
- the separation between `ProvidesNow` and teardown visibility:
  retirement alone must **not** immediately remove an active provider's table
  from dependents;
- the name ledger, allocation history, incarnation identity, and explicit
  O-Insert allocation update;
- the existing real per-constructor fixture coverage and the raw ADR-09
  candidate's adjacent guarded steps, repairing their semantics rather than
  replacing them with arbitrary propositions.

## 3. T02R2: required semantic-interface repair

### 3.1 Target eligibility and quiescence

Repair `TargetViewAt` so that the **owner whose target is being computed** is a
currently eligible, non-retired fiber. Keep this distinct from provider
visibility:

- a retired but still Active provider may continue to satisfy an existing
  dependent's committed binding until guarded withdrawal;
- the retired fiber itself has no new/current target and must be able to enter
  withdrawal;
- `O-Retire` must therefore make `L-Leave` or the appropriate diversion path
  available without prematurely breaking dependent committed views.

Repair `Quiescent` so it reflects lifecycle/target agreement rather than only
excluding intermediate phases. In particular:

- an Active fiber must have its committed target and no pending flight;
- a normal, non-retired Inactive fiber with an available target is not
  quiescent, because `L-Begin` is enabled;
- a retired Inactive fiber may be terminal;
- a Failed fiber is terminal under the failure policy and must not be silently
  treated as a normal restartable Inactive fiber;
- Reloading and Unloading remain non-quiescent.

Add small negative fixtures proving that:

1. retiring an Active owner invalidates its own target eligibility;
2. the same retired Active cell may still provide its committed table while
   dependents drain;
3. an ordinary Inactive, unretired fiber with a satisfiable target is not
   quiescent.

### 3.2 Ranked iterator integration

The authoritative rank is over iterator/continuation codes, not global states.
Replace the current `ComponentSemantics.rank : State -> Nat` arrangement with
an interface faithful to `STC.RankedIterator`:

```lean
rank : Iterator -> Nat
yield ... next  ==>  rank next < rank current
```

Prefer reusing or adapting `STC/Core/Iterator.lean` rather than maintaining a
second incompatible iterator machine. Do not obtain progress by decrementing
an unrelated ambient/state field. The rule-level `L-Iter` guard must consume
the continuation-rank fact.

### 3.3 Witnessed landing result

Replace the current under-specified

```lean
flight : Flight -> State -> Option State
```

with a witnessed landing interface that binds, in one semantic result or
relation:

- the stored flight token;
- the source state/boundary;
- the landed state;
- the inverse produced by the landing;
- any failure branch, if supported, without reclassifying it as success.

A structure/result carrier or an explicitly functional relation is acceptable.
An API in which `L-DivertLand` may choose an arbitrary accumulator token is
not acceptable.

### 3.4 Complete failure bridge

Do not keep a separate `sem.failure failure before = some before` escape hatch.
Integrate lifecycle failure with the existing ranked iterator and
`STC.Failure`/`ExecResult` infrastructure:

- `L-Raise` is produced only by the currently executing Reloading iterator;
- the semantic witness is the actual failing stage/result;
- the retained failure contains error, boundary, and successful-prefix undo;
- the already accumulated prefix is not erased or replaced by identity;
- Active fibers cannot spontaneously raise without a distinct, separately
  justified rule (none is authorized by the current P13 target).

### 3.5 Real body-frame interfaces

Strengthen the external semantics/profile so actual `stage`, landing, and
accumulator execution can discharge the global D48 obligations. The needed
facts must cover the full body transformation, not only the later `editCell`
control edit:

- registry domain/name allocation is unchanged by lifecycle bodies;
- ledger and allocation history are unchanged;
- foreign fibers and static declarations are framed;
- reads respect the owner's required/coeffect observation;
- stage/landing writes stay within the acting component's provision envelope;
- cleanup satisfies the explicit owner/recorded-child cleanup frame;
- the acting owner still exists when the following control edit is applied.

Do not define `observes`, `writesWithinProvision`, `ReadRespect`, or a profile
field as the desired theorem itself. Provide reusable laws with concrete
premises and instantiate them non-vacuously in `GlobalRules.lean`.

## 4. T03R: authoritative rule repair

### 4.1 Canonical insertion

Strengthen `CanonicalInitialCell` and O-Insert guards so a fresh insertion
preserves the state invariants. At minimum require:

- incarnation, registrar/parent, and immutable birth are correct;
- `retired = false`, phase is normal Inactive, no flight, no failure;
- committed local table is empty;
- committed provider view is empty;
- iterator/accumulator payload is the component's authorized initial/root and
  identity payload, or is related to it by an explicit component profile;
- declarations/payload satisfy the component admissibility needed for
  `TableConfined`, lifecycle coherence, and later T59.

Prove that O-Insert preserves the relevant static/data-coherence conjuncts.
Do not postpone a plainly false T59 case to T05A.

### 4.2 Begin

`L-Begin` must require a normal startable cell:

- Inactive;
- non-retired;
- no failure outcome;
- no stale pending flight;
- a valid current target;
- a witnessed launch result.

The successor installs the committed target, root/current iterator,
identity accumulator, and exactly the new pending flight required by the
extended lifecycle semantics.

### 4.3 Iterator and inverse order

The inverse accumulator is LIFO. Under the existing
`composeInverse_law`, `composeInverse a b` executes `b` and then `a`.
Therefore, if `old` recovers the earlier prefix and `new` recovers the current
stage, update using:

```lean
composeInverse old new
```

not `composeInverse new old`.

Add a noncommutative accumulator fixture so this order cannot again be hidden
by `Nat` addition or another commutative operation.

### 4.4 Finish

`L-Finish` must:

- consume the actual `.halt result finalInverse` witness;
- compose `finalInverse` into the accumulated prefix in the correct LIFO
  order;
- commit the successful result/table/view as prescribed by the lifecycle;
- enter Active;
- clear the pending flight;
- retain no stale failure payload.

Add an end-to-end Begin/Iter*/Finish fixture proving both recovery-accumulator
content and absence of pending flight at the successful endpoint.

### 4.5 Divert

For `L-DivertLand`:

- the label/witness must identify the exact token stored in the acting cell;
- landing must be justified by the witnessed landing result from Section 3.3;
- the landed inverse must come from that result, not from a free label field;
- compose it in the correct LIFO order;
- enter Unloading and preserve the committed teardown view.

For `L-DivertAbort`:

- require the actual target-change/absence boundary;
- require the async policy's abort guard;
- do not turn a pending or failed operation into successful completion.

The raw rule relation may remain separate from a T04 trace-policy wrapper, but
every rule-local token/result connection must already be sound in T03R.

### 4.6 Raise and unload

`L-Raise` must use the complete iterator failure witness described above and
enter Unloading with the correct failure/prefix recovery data.

`L-Unload` must run the recorded accumulator under the cleanup-frame laws,
respect `ReliedUpon`, clear committed view and flight data, and end in:

- Failed when a complete failure payload exists;
- otherwise normal Inactive/retired terminal state as appropriate.

### 4.7 Nested registration and returned inverse

Nested registration must do more than prove `parent = some registrar`.
Connect the component action/registration result to:

- the fresh O-Insert incarnation;
- the corresponding explicit O-Retire inverse/action witness;
- cleanup/accumulator recording of that inverse;
- freshness, ledger/history, and registration-frame preservation.

The later existence of an unrelated `.retire owner beforeCell` label is not a
proof that registration returned the correct inverse.

### 4.8 Replayable factorization and labels

Redesign effectful labels/witnesses so they retain semantic choices without
pinning a concrete successor state as an input label. The current forms

```text
iter ... after
finish ... result
divertLand ... landed
unload ... middle
```

make a fixed-label selected body non-replayable.

Required outcome:

- a fixed label/code plus resolved semantic witness determines or relates a
  body execution at the supplied source state;
- applying the same semantic operation to another related source does not
  simply return the old captured endpoint;
- each constructor has a genuine selected-body/control-edit factorization or
  an explicitly relational factorization;
- the nonconstant evidence is for one fixed operation/body, not a comparison
  of two different labels already carrying different endpoints;
- T04 can separately define external orchestration inputs and stronger
  resolved semantic witnesses.

Do not complete T04's episode or trace equivalence in this task, but ensure the
repaired label surface can support it without another semantic reopen.

### 4.9 R.base

Replace the current degenerate identity/singleton view in which
`baseLifecycleRule <-> LifecycleRule` with the concrete ADR-08 specialization:

- base Reload is represented by an admissible full path containing
  Begin followed by Finish, with only explicitly permitted internal staging;
- base Unload is represented by Leave followed by Unload;
- intermediate Reloading/Unloading states are not stable base states;
- stuttering is admitted only through an explicit profile and only when the
  projected base observation is unchanged;
- adequacy is proved through `Staging.MacroPath`, not by declaring every
  singleton full step atomic and every state stable.

## 5. Fixture requirements

Repair `STC/Examples/GlobalRules.lean`; do not replace semantic obligations by
`True` fields or endpoint equalities.

The final fixture suite must include:

1. an inhabited witness for all 11 concrete constructors / 10 printed cases;
2. two distinct acting fibers;
3. nonempty requirements and provisions;
4. nested registration with an explicit returned retirement inverse;
5. successful Begin/Iter/Finish with final inverse retained and flight cleared;
6. a noncommutative inverse-order witness;
7. actual iterator-generated Raise with complete failure boundary/prefix undo;
8. both Divert branches, with stored token and landing inverse tied to the
   semantic witness;
9. actual full-step D48/no-allocation evidence for effectful lifecycle cases;
10. the raw ADR-09 candidate realized by adjacent authoritative rule steps;
11. non-vacuous fixed-operation factorization/replay evidence;
12. genuine ADR-08 Reload and Unload macro-path witnesses.

T04 will assemble adjacent steps into `globalTrace` and define
`Initial`/`ReachedFrom`. T05C will project to `SupportSnapshot` and prove the
actual support-cycle result. Do not falsely claim these as T03 theorems.

## 6. Explicit anti-vacuity checks

Reject the repair if any of the following occurs:

- a profile field directly assumes the preservation/recovery theorem to be
  proved;
- factorization uses `fun _ => knownAfter` or embeds the known endpoint in a
  supposedly replayable input label;
- rank decreases only because an unrelated global-state counter was changed;
- landing inverse remains a free argument;
- failure is represented by `Unit` without a checked bridge to complete
  error/boundary/prefix data;
- D48 is proved only from the intermediate body result to the final control
  edit, ignoring the source-to-body transformation;
- lifecycle no-allocation is inferred merely because the control-edit helper
  does not call `allocate`;
- `R.base` is made equivalent to every singleton `R.full` step;
- a commutative accumulator is the only evidence for inverse order;
- the fixture constructs an arbitrary endpoint graph rather than applying the
  authoritative rule guards.

## 7. Expected file scope

Primary files:

- `STC/State/Component.lean`
- `STC/State/Global.lean`
- `STC/Control/Rules.lean`
- `STC/Examples/GlobalModel.lean`
- `STC/Examples/GlobalRules.lean`

Compatibility edits are allowed in:

- `STC/Control/Reachability.lean`
- `STC/Control/Episode.lean`
- `STC/Bootstrap.lean`

The compatibility edits must only restore compilation after the label/API
repair. Do not mark T04 complete and do not preserve known-vacuous T04 draft
definitions merely to avoid signature changes.

Documentation:

- create `docs/status/P13-lanes/T02R2-T03R-handoff.md`;
- amend `docs/status/P13-api-freeze.md` with an explicit reopen and new freeze
  checkpoint;
- correct stale statements in `docs/status/P13-lanes/T03-handoff.md` or mark it
  superseded;
- update Ledger notes/evidence classification only where the repaired checked
  declarations justify it.

Avoid unrelated refactors.

## 8. Work sequence and pause rule

Use this order:

1. fresh checkout/worktree from current `origin/main`;
2. record baseline commit and run available preflight gates;
3. design and implement T02R2 interfaces;
4. focused build of state/core modules;
5. implement T03R rules and successor equations;
6. implement full-body frame/factorization theorems;
7. rebuild all fixtures, including noncommutative and negative fixtures;
8. make only required T04-draft compatibility edits;
9. run focused checks, full build, scanners, ledger validator, and diff checks;
10. write handoff/freeze documents and commit.

Pause and report before implementation only if one of these material decisions
cannot be satisfied conservatively:

- integrating `STC.RankedIterator` would require changing the data-only
  `FiberCell` carrier rather than only its external interpretation;
- a witnessed landing result cannot represent both the accepted async and
  recovery semantics;
- replayable labels require changing the externally ordered orchestration
  input notion rather than only lifecycle/resolved witnesses;
- the repaired rules still cannot realize the existing ADR-09 adjacent-step
  candidate;
- an accepted ADR and the P13 plan impose contradictory requirements.

When pausing, provide the smallest competing signatures, a counterexample or
typing obstruction, and a recommended choice. Do not silently select a weaker
semantic target.

## 9. Acceptance gate before T04

T04 may start only when all of the following are true:

- the full project builds from a fresh integrated worktree;
- no `sorry`, `admit`, project `axiom`, or `unsafe` escape is introduced;
- Ledger validator and frozen hash checks pass;
- all concrete constructors and printed cases remain inhabited;
- `O-Retire` enables correct owner withdrawal without breaking dependent
  teardown visibility;
- iterator rank is continuation-based;
- inverse order is checked with noncommutative evidence;
- Finish retains the final inverse and clears pending flight;
- Raise comes from the actual failing iterator and retains complete failure
  data;
- DivertLand binds stored token, landed state, and inverse;
- actual stage/landing/cleanup bodies discharge D48 and no-allocation facts;
- canonical O-Insert preserves the relevant WellFormed conjuncts;
- fixed-operation factorization is replayable and nonconstant;
- nested registration has an explicit returned inverse linkage;
- `R.base` is a genuine ADR-08 macro specialization;
- the raw ADR-09 candidate remains realizable by the repaired authoritative
  rules;
- `P13-api-freeze.md` records new signatures and hashes and no longer contains
  contradictory “open/complete” status text.

## 10. Handoff report requirements

The final handoff must state:

- base commit, final commit, branch, and exact changed files;
- every public signature changed by T02R2/T03R;
- semantic reason for each change;
- which earlier handoff claims were superseded;
- focused and full build commands with outcomes;
- validator/scanner/diff outcomes;
- fixture inventory mapped to the acceptance gate;
- remaining T04-owned work, explicitly including episodes, admissible traces,
  activation provenance, same ordered orchestration inputs, and resolved
  semantic witnesses;
- any residual blocker. If one remains, do not mark T03 re-frozen and do not
  start T04.

Commit the repair, but do not push or open a PR unless explicitly authorized.
