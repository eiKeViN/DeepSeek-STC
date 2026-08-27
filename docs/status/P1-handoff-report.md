# P1 Handoff Report

| Field | Value |
|---|---|
| Plan | `DH-P1-EXEC-01` |
| Wave | P1 — relation and result foundations |
| Base commit | `02b50d25d78a0b216439732a1c597cf195c9a523` (`main`) |
| Final implementation commit | `02864d3c32e2b7bb02cb7ce3beaebae4476f45ce` |
| Branch | `codex/p1-relation-result` |
| Worktree at handoff | clean after the integration commit |
| Namespace | `STC` |
| Adapter boundary | not entered; no `STC.Adapter` declarations |

## 1. Task ownership and scope

- `P1-T01`: integration owner; `STC/Foundation/Relation.lean`.
- `P1-T02`: integration owner; `STC/Foundation/Result.lean`.
- `P1-T03`: integration owner; `STC/Examples/RelationResult.lean`, `STC/Bootstrap.lean`, and derived status.

The implementation follows P1-DEC-01. Relation vocabulary is owned by
`Foundation/Relation`; result carriers and relators are owned by
`Foundation/Result`. No `Effect`, `PartialOp`, `StageResult`, iterator, concrete
state, registry, coeffect store, or runtime declaration was added.

## 2. Preflight

The actual starting worktree was clean and detached at the accepted `main`
descendant:

```text
$ git status --short --branch
## HEAD (no branch)

$ git log -1 --oneline
02b50d2 docs: link paper URL, point to P1 plan, trim README authoritative material
```

The execution branch was then created as `codex/p1-relation-result` without
changing frozen inputs. The pinned tools were available:

```text
Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)
Lake version 5.0.0-src+d8b1897 (Lean version 4.33.0)
Python 3.12.3
```

The P0 gate was rerun before production edits:

```text
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
Definition-Ledger validation: PASS
  82/82 covered; duplicates 0; unknown 0
  H03 source hash OK: 8f99db87d7aa4d85...
  H04 source hash OK: 63d1fb68bcebb63e...
  no inferred transitive readiness

$ python scripts/scan_lean.py STC
<empty output; exit 1, clean by the scanner contract>

$ lake env lean STC/Bootstrap.lean
<empty output; exit 0>

$ lake build
ℹ [516/518] Replayed STC.Bootstrap
info: STC/Bootstrap.lean:21:0: 1
Build completed successfully (518 jobs).
```

The first cold-cache Lean invocation initialized the local Lake/Mathlib cache;
the commands above were repeated after initialization and are the successful
pre-edit gate results.

## 3. Changed paths and public declarations

### `STC/Foundation/Relation.lean`

Public declarations:

`RelSpec`, `RespectsOn`, `Respects`, `PointwiseRel`, `CrossRel`,
`OptionRel`, `optionRelSpec`, `PullbackRel`, `pullbackRelSpec`, and `equality`.

Checked generic theorem family:

`crossRel_of_respects_pointwise`, `pointwiseRel_of_crossRel`,
`respects_of_crossRel_self`, `respects_left_of_crossRel`,
`respects_right_of_crossRel`, `respects_id`, `respects_comp`,
`pointwiseRel_refl`, `pointwiseRel_symm`, `pointwiseRel_trans`, and
`compose_pointwiseRel`.

### `STC/Foundation/Result.lean`

Public declarations:

`EffectResult`, `Failure`, `ExecResult`, `EffectResultRel`, `FailureRel`,
`ExecRel`, `effectResultRelSpec`, `failureRelSpec`, `execRelSpec`,
`failureRelEq`, and `execRelEq`.

`Failure` retains `error`, `boundary`, and `prefixUndo`. `ExecRel` compares
success only with success and failure only with failure; mixed constructors
reduce to false. Error equality is available only through an explicit helper
or an explicitly supplied relation value.

### `STC/Examples/RelationResult.lean`

The finite fixture is `Fin 4`, partitioned into two nontrivial classes by
`toyRel`. It contains the orientation, relator, equality, and finite decision
checks plus the concrete `composed_pointwise_check` instance of the generic
composition theorem.

### `STC/Bootstrap.lean`

Imports the canonical Relation, Result, and RelationResult modules. The root
`STC.lean` remains the package entrypoint and was not structurally changed.

### Derived status

`docs/status/Definition-Ledger.json` now records `DH-P1-EXEC-01` and only
derived evidence changes. `docs/status/P1-scan-raw.txt` is empty because the
final scanner produced no lexical matches.

## 4. Compiler, build, validator, and scan evidence

All single-file checks used the repository's explicit options:

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Relation.lean
exit 0; no output

$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Result.lean
exit 0; no output

$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/RelationResult.lean
exit 0
{ pointwiseOrientation := true,
  crossOrientation := false,
  optionPositive := true,
  optionMixed := false,
  effectResult := true,
  failure := true,
  execSuccess := true,
  execMixed := false,
  equalityReflexive := true,
  equalityDistinctState := false }

$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
exit 0; no output

$ lake env lean STC/Bootstrap.lean
exit 0; no output

$ lake build
ℹ [636/639] Built STC.Examples.RelationResult (953ms)
info: STC/Examples/RelationResult.lean:209:0: { pointwiseOrientation := true,
  crossOrientation := false,
  optionPositive := true,
  optionMixed := false,
  effectResult := true,
  failure := true,
  execSuccess := true,
  execMixed := false,
  equalityReflexive := true,
  equalityDistinctState := false }
✔ [637/639] Built STC.Bootstrap (700ms)
✔ [638/639] Built STC (754ms)
Build completed successfully (639 jobs).

$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
Definition-Ledger validation: PASS
  82/82 covered; duplicates 0; unknown 0
  H03 source hash OK: 8f99db87d7aa4d85...
  H04 source hash OK: 63d1fb68bcebb63e...
  no inferred transitive readiness

$ python scripts/scan_lean.py STC
exit 1; stdout and stderr empty; raw output saved in P1-scan-raw.txt

$ git diff --check
exit 0
```

## 5. Evidence classification

| Evidence | Earned result |
|---|---|
| A | Relation/result API is mapped to ADR-01/ADR-06 and the P1 ownership decision; scope and repairs are explicit. |
| I | All four production/test modules elaborate, imports are acyclic, Bootstrap and the package build pass. |
| K | The generic relation bridge/closure proofs and all relation-spec fields are checked Lean proof terms; no placeholders, project-defined unchecked declarations, or `unsafe` code are present in `STC`. This is kernel proof evidence for the stated generic propositions only. |
| E | The finite `CheckReport` is evaluated by Lean and the exact output is recorded above. |
| R0 | Not earned; no adapter seam was implemented. |
| R1+ | Not earned; no runtime correspondence is claimed. |

The result relator shells are interface/alignment evidence in this wave. Their
lawful-effect, recovery, operation, iterator, and concrete observation uses
remain staged as required by the plan.

## 6. Finite test inputs and outputs

The relation on `Fin 4` relates values with the same class (`0,1` and `2,3`).
`badMap` maps related inputs `0` and `1` to different classes, so its
self-comparison has `PointwiseRel = true` while `CrossRel = false`. This is an
orientation counterexample to conflating the two liftings.

The recorded `CheckReport` is:

```text
pointwiseOrientation = true
crossOrientation = false
optionPositive = true
optionMixed = false
effectResult = true
failure = true
execSuccess = true
execMixed = false
equalityReflexive = true
equalityDistinctState = false
```

The positive result checks relate distinct states `0` and `1` and preserve the
identity undo pointwise. The positive failure check also preserves equal error,
related boundary, and pointwise prefix undo. The mixed Option/Exec checks are
negative by constructor tag, so no failure information is erased.

## 7. Ledger result and deferred boundaries

| Row | Delivery | Evidence | P1 interpretation |
|---|---|---|---|
| D1 | `planned` | `pending` | Twisted Effect composition remains part of the P2 Effect kernel; P1 supplies no D1 implementation. |
| D33 | `in_progress` | `aligned` | Generic pullback shell only; concrete State/Like observation remains ADR-02/03 dependent. |
| D34 | `planned` | `pending` | Typed operation tests and operation-induced indistinguishability remain a P3/P5 partial-operation obligation; P1's generic finite tests do not discharge this row. |
| D36 | `completed` | `proved` | Canonical relation vocabulary and checked relation laws are delivered. |
| D37 | `in_progress` | `aligned` | Result/selected-inverse relator shape is present; lawful effects and recovery remain later work. |
| L38 | `in_progress` | `aligned` | Relation bridges and equality specialization are present; full effect theorem transport remains staged. |
| D39 | `planned` | `pending` | Concrete partial/coeffect independence awaits P3/P5 and BD-COEFFECT. |
| T40 | `planned` | `pending` | Distinct-key theorem awaits ADR-02 store and P3/P5 operation layers. |
| D41 | `planned` | `pending` | Coeffect-mediated operations await ADR-02 partiality and P3/P5 definitions. |
| T42 | `planned` | `pending` | Mediated-effect independence awaits D39/D41 and coeffect/partiality dependencies. |

No H03 dependency list or H04 readiness field was changed, and no transitive
readiness was inferred from a compiling shell.

## 8. Provenance and frozen-input confirmation

H03 and H04 match the P0 frozen hashes exactly:

| Artifact | SHA-256 |
|---|---|
| H03 `DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json` | `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8` |
| H04 `DeepSeek-Harness-04-Formalization-Disposition-Specification.json` | `63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db` |

Workspace ADR hashes are unchanged and remain canonical under the P0 option-2
ruling:

| ADR artifact | Workspace SHA-256 |
|---|---|
| ADR-01 | `489a7e4d3d43e1bd12db99f185fe3931e1e4ee55dcade35238b0e1f69429c3fe` |
| ADR-02 | `7d83bd3380f082c5340c52b2b495f603ae1385567c6038a5b576d29276954a9a` |
| ADR-03 closure | `2ef858c0a4d99bdf792e98e779d4c452884690f1a3d68addcefec6d827469a35` |
| ADR-03 unified state/registry | `0c6861367cf3061358366e90b2e2848649d96f5ad792185ed5f2e186d0520d48` |
| ADR-04 | `80beaaf2c29930527fee17419ae74718ea26140058fda67bb834d8cc435e36cc` |
| ADR-05 | `86c555027a0a49bb40c95f1d612c12fcb6962d9801c5ed953ba9b1a7d1df04e9` |
| ADR-06 closure | `e1baf7b96b2df72d1289e6148be3d801dc2477aa7c9230201f113ee91f118fea` |
| ADR-06 historical spike | `7726a13f40dec56f2f6a57058d657808fe3da059577c36c5935c08b5b5c86a90` |

The ADR-01, ADR-02, and ADR-06-spike differences from the Blueprint companion
manifest are the already-resolved P0 option-2 reconciliation. The executing
agent did not replace, regenerate, or edit them. The Blueprint hash revision
remains the lead follow-up recorded by P0.

No frozen H03/H04 input, accepted ADR, Blueprint, Formal Reference, or
historical Lean spike was modified. No active production file contains
`CordisADR*`, `DeepSeekHarness`, or `Adapters.Cordis`.

## 9. Assumptions, counterexamples, and unresolved issues

- The P1 carrier decision uses structures for `EffectResult` and `Failure`, and
  a tagged `ExecResult` wrapper; this is the P1 plan's recommended layout and
  preserves named access to every required field.
- The error relation is a raw explicitly supplied predicate in `FailureRel` and
  `ExecRel`; `failureRelSpec` and `execRelSpec` accept a `RelSpec` when an
  equivalence shell is wanted. Equality is never inferred from a state
  relation.
- The finite `badMap` example is non-vacuous and demonstrates why
  same-input `PointwiseRel` cannot be replaced by related-input `CrossRel`.
- No empty relation, behavior-erasing observation, impossible invariant, or
  degenerate transition was used.
- P2 must add lawful effects and recovery; P3/P5 must add partial/coeffect
  operations and concrete observations. D37/L38 are intentionally not marked
  globally proved here.

The next planned wave is P2's shallow reversible Effect kernel. This handoff
does not claim Cordis runtime verification or any R0/R1+ refinement.

The current `HEAD` is a docs-only follow-up that finalizes this handoff metadata
after the implementation commit above.
