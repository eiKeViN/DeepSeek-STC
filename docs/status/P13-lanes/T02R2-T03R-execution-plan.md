# T02R2/T03R interface repair — plan for the 5 lead-mandated fixes, then fixture

## Context

The lead reviewed `codex/t02r2-t03r` (`32a7998`) and ruled it a directional
checkpoint, not T03R-complete: the fixture rewrite must wait until 5 interface
problems are fixed, or the fixture would mask them and force a T05 reopen.

**My judgment of the feedback: all 5 points are fair — I verified each against
the code written this session:**

1. **Finish commits the whole coeffect store** — `finishState` sets
   `committed := { entries := state.coeffects }`. With a multi-key global store,
   a fiber providing only `{10}` immediately violates `TableConfined`
   (`committed.entries.keys ⊆ provides`). Real bug.
2. **D48 frames cannot express real effects** — `writesWithinProvision :
   State → State → Prop` is unparameterized, so `provision_coeffectFrame`
   quantifies over arbitrary `provides`; `provides = ∅` forces ALL coeffects
   unchanged. The accumulator's `registryFrame` is interpreted as registry
   TOTAL equality, which forbids the child-retirement inverse. `CleanupFrame`
   allows retiring any foreign fiber, not just recorded children. Full
   read-noninterference theorems are missing for the effectful constructors.
3. **Nested registration is unconnected and vacuous** —
   `RegistrationInverseAdequate` is vacuous when the action never succeeds;
   `RegistrationResult`/`ActionResult`/the adequacy relation/O-Insert are not
   joined into one witness.
4. **The failure bridge does not guarantee completeness** —
   `failureBridge_law` proves output uniqueness only; nothing forces the
   output to contain error/boundary/prefixUndo.
5. **R.base's stable image is degenerate** — `embed := id`, `project := some`,
   `stable := fun _ => True`, so Reloading/Unloading are stable base states.
   Exploration of `STC/Staging.lean` confirms `stable` is otherwise INERT and
   `BaseState` is a free parameter — a subtype fix is compatible with the
   frozen single-universe `StagingModel`.

**Execution model:** I orchestrate; one subagent per task below. Subagents
must follow AGENTS.md, the debug lessons
(`docs/notes/lean-proof-debug-lessons.md`), the anchor-comment tool for files
>500 lines, and `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true` for
single-file checks. Commit per task (safety-commit discipline); no push.

## Task 1 — Finish commit projection

File: `STC/Control/Rules.lean`.

- Define `commitProjection (state : GState) (provides : Finset Key) :
  Finmap (fun _ : Key => Value)` := the coeffect store restricted to
  `provides` (via `Finmap.filter` over a decidable membership).
- `finishState` commits `{ entries := commitProjection state
  cell.component.provides }` (the lambda has the cell).
- Prove `commitProjection_keys_subset : (commitProjection state provides).keys
  ⊆ provides`.
- Add `finish_tableConfined_preserved`-style check (finish of a TableConfined
  before stays TableConfined, given the target table is confined) — or at
  minimum the keys-subset theorem feeding T05A later.
- Update the `finish` docstring.

## Task 2 — D48 ownership and cleanup frames

Files: `STC/State/Component.lean`, `STC/State/Global.lean`,
`STC/Control/Rules.lean`.

- **Write envelope binding:** parameterize
  `writesWithinProvision : Finset Key → State → State → Prop`; add per-code
  envelope fields `stageEnvelope : Iterator → Finset Key`,
  `landingEnvelope : Flight → Finset Key`, `accumulatorEnvelope : Accumulator →
  Finset Key` with laws `stage_writesWithinProvision : stage code before =
  some result → result.state? = some after → writesWithinProvision
  (stageEnvelope code) before after` (same for landing/accumulator/action).
  The effectful rule constructors (iter/finish/divertLand/unload) gain an
  envelope guard: `sem.<kind>Envelope <code> ⊆ cell.component.provides`.
  `BodyFrameAdequacy.provision_coeffectFrame` is restated over the
  parameterized relation (given `provides` = the rule's envelope, non-vacuous).
- **Registry frame split:** keep `registryFrame` (ordinary stage/landing:
  registry value equality) with `registry_total`; for the ACCUMULATOR replace
  `accumulator_registryFrame` with `accumulator_domainFrame` (registry KEYS
  equality only — retirement edits a cell but never its key) and a cleanup
  law: `accumulator code before = some after → accumulatorFrame code before
  after`, with `BodyFrameAdequacy.accumulator_cleanupFrame` interpreting
  `accumulatorFrame` as the strengthened `CleanupFrame` for the acting owner.
  `lifecycle_noAllocation` uses the domain-frame for the unload branch
  (keys-equality, ledger, history) — no registry-value equality.
- **Strengthen `CleanupFrame`** (`Global.lean`): the foreign-edit branch must
  require the edited foreign fiber satisfies `parent = some owner` (a recorded
  child) — child retirement is the only admitted foreign edit.
- **Full read-noninterference for the effectful constructors:** add
  `iter_full_readNoninterference`, `finish_full_readNoninterference`,
  `divertLand_full_readNoninterference`, `unload_full_readNoninterference`
  (hstage/hland/haccumulator-premise style, mirroring the
  `*_full_writeFrame` theorems), using `BodyFrameAdequacy.observes_readRespect`
  (new field: `observes before after → ∀ key ∈ requires, coeffects
  unchanged`) plus `editCell_readNoninterference`.
- Keep the identity-body frame theorems; zero-warning gate applies.

## Task 3 — NestedRegistrationWitness

File: `STC/Control/Rules.lean`.

- Define a non-vacuous witness bundling: an actual action execution
  `sem.action actionCode parentBefore = some result`; the corresponding
  O-Insert step `OrchestrationRule (.insert registrar fresh child)
  parentBefore parentAfter`; the endpoint linkage `result.state =
  parentAfter`; the returned inverse `∃ inverse, result.inverse? = some inverse
  ∧ RetireInverseAdequate sem inverse fresh`; and the fold evidence that the
  parent's payload accumulator becomes `composeInverse inverse old` after the
  step.
- Retire/delete `RegistrationInverseAdequate` (or restate it as a derived
  projection of the witness, keeping `RetireInverseAdequate` and the
  `registrationInverse_retires` interpretation theorem).
- No rule-constructor changes (D1 ruling: O-Insert stays action-free).

## Task 4 — Complete failure carrier

Files: `STC/State/Component.lean`, `STC/Control/Rules.lean`.

- Introduce `structure FailureEvidence (State) (Error) (Accumulator) where
  error : Error; boundary : State; prefixUndo : Accumulator`.
- ComponentSemantics: the stage error carrier becomes `Error` (rename the
  `Failure` param where it means the stage error);
  `StageResult.raise (error : Error)`. Drop `failureBridge` and
  `failureBridge_law` from the sem.
- `L-Raise` label carries the complete evidence:
  `GlobalLifecycleLabel.raise (owner) (evidence : FailureEvidence State Error
  Accumulator)`; the rule requires
  `evidence = { error := <the raise's error>, boundary := before, prefixUndo :=
  cell.payload.accumulatorCode }` (a definition `FailureFromStage`, not a
  sem-field) plus `hstage : sem.stage … = some (.raise evidence.error)`.
- The Fiber's `failureData` stores the ERROR only (`Option Error` in the
  payload — adjust `FiberPayload`'s `failureData` type if it currently stores
  the evidence) — no state recursion in the fiber.
- Update `raiseState`, `factor_raise`, `raise_not_failed`, `SelectedBody`/
  `ControlEdit` raise-cases, and the `failureRule`/`failureRule_enters_teardown`
  accordingly.

## Task 5 — R.base stable image

File: `STC/Control/Rules.lean` (uses the frozen `STC/Staging.lean`).

- Define `StagingStable (state : GState) : Prop := ∀ name fiber, lookup name
  state.registry = some fiber → fiber.phase = .active ∨ fiber.phase = .inactive
  ∨ fiber.phase = .failed` (no Reloading/Unloading).
- Set the base carrier to the subtype: `abbrev BaseState := { state : GState //
  StagingStable state }` (single universe, compatible with the frozen
  `StagingModel`); `embed base := base.1`; `project state := if h :
  StagingStable state then some ⟨state, h⟩ else none`; `stable := StagingStable`;
  `project_embed`/`stable_embed` discharged.
- `globalStaggerProfile`: keep `orchestration := fun _ _ _ => False` and make
  `lifecycle := fun _ _ _ => False` (honest empty — no iter stutter is ever
  admitted; drop the declared-but-never-admitted iter stutter).
- Adapt `baseOrchestrationRule`/`baseLifecycleRule`/`baseOrchestration_iff`/
  `baseLife_reload_iff`/`baseLife_unload_iff`/`orchestrationAdequacy`/
  `lifecycleAdequacy`/`globalAtomicAdequacy` to the subtype endpoints.
- Add a small negative fixture later proving a Reloading state is not
  `StagingStable` (in Task 6).

## Task 6 — GlobalRules.lean fixture rewrite (after Tasks 1-5)

Full rebuild per the brief §5's twelve requirements: noncommutative
accumulator (`List Nat`, `composeInverse := cons`), iterator-generated raise
with complete `FailureEvidence`, both Divert branches with stored tokens and
landing-bound inverses, nested registration via `NestedRegistrationWitness`,
finish commit with retained final inverse and cleared flight, ADR-09 cycle
trace, ADR-08 macro-path witnesses, non-vacuous fixed-operation replay
evidence (same label, two sources, two middles), full-step D48 body evidence,
and the §3.1 negative fixtures (retired owner loses target eligibility;
retired Active provider keeps providing; a normal inactive fiber with a
satisfiable target is not quiescent).

## Task 7 — Gates, handoff, freeze

Focused checks, full `lake build` (zero warnings), `scan_lean.py` exit 1,
ledger validate, forbidden-token scan, `git diff --check`; then
`docs/status/P13-lanes/T02R2-T03R-handoff.md`, the `P13-api-freeze.md` reopen
checkpoint (signatures + hashes), update the signature-candidate doc to
"rulings applied", commit. No push unless authorized.

## Verification

Per task: `lake build <Module>` fresh-olean check, then the single-file
`lake env lean -DautoImplicit=false -Dpp.unicode.fun=true <file>`; final full
`lake build` with zero errors AND zero warnings; `python scripts/scan_lean.py
STC` (exit 1), `python scripts/validate_definition_ledger.py
docs/status/Definition-Ledger.json`; `git diff --check`.

## Unresolved questions

None blocking — all design forks resolved by the lead's rulings (subtype base
states over the empty-stutter fallback; error-only fibers; envelope-guarded
rules).
