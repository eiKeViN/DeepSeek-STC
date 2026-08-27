# STC Metatheory: P0 Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P0-EXEC-01` |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Plan-generation snapshot | `9cf89966148469c088b3bf876e484030228bb683` |
| Status | `conditionally-executable; preflight records required` |
| Owner | delegated P0 execution Agent; reviewed by the project lead |
| Lean root namespace | `STC` |
| Adapter boundary | `STC.Adapter` |
| Scope | `P0-T02`, `P0-T03`, `P0-T04` |
| Prerequisite | `P0-T01` lead-reported complete; materialize/verify its record, do not redo its decisions |

## 1. Objective

Close the remaining P0 work in the repository before any P1 production definitions are
started.  The result must be a reproducible baseline, a machine-readable Definition
Ledger, and a minimal but honest Lean bootstrap plus scan protocol.

This is an execution and traceability phase.  It makes no new mathematical or
architectural decision and must not reopen ADR-01 through ADR-06.

## 2. Repository facts to verify

The plan was prepared against the following repository snapshot.  The executing Agent
must record the actual `HEAD` and working-tree state at the start; the snapshot hash above
is a reference, not permission to reset a newer checkout.

At plan generation, the repository did not yet contain a committed `P0-T01` status file or
`docs/status/` directory.  The lead has reported that T01 is complete, but the delegated
Agent must materialize that handoff in the repository (or record the exact location supplied
by the lead) before closing P0.  The minimum T01 record is:

```text
source-of-truth checkout/path
lean-toolchain contents
lakefile.toml and lake-manifest.json identity
Lean/Lake/Mathlib versions or revisions
initial HEAD and working-tree status
baseline command outcomes
```

| Item | Current repository value |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.33.0` |
| `lakefile.toml` | package `DeepSeek-STC`, version `0.1.0`, default target `STC` |
| Lean options | `autoImplicit = false`, `pp.unicode.fun = true` |
| Mathlib input revision | `v4.33.0` |
| Mathlib manifest revision | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| root module | `STC.lean` (currently a minimal Mathlib import and smoke `#eval`) |
| production tree | no substantive `STC/` modules yet; P0 must not pretend that P1 exists |

Do not discard uncommitted user work.  If the checkout is dirty, record the exact state and
stop for review rather than using a destructive reset.  The newly generated plan file itself
may be the one expected untracked file during this setup step; the lead must either commit
it before execution or list it explicitly as an allowed setup exception in the T01 record.
Any other dirty path is treated as user work and must not be overwritten.

## 3. Authoritative inputs and exclusions

### Required inputs

Use the repository copies whenever present:

```text
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json
docs/blueprint/architecture-decision/json/*.json
lean-toolchain
lakefile.toml
lake-manifest.json
STC.lean
```

The paper PDF is the primary mathematical source when a paper anchor must be checked;
it is a read-only external input for this repository and should not be copied into the
repository by this plan.

### Explicitly excluded inputs

The following are project-history documents, not dependencies of this formalization
pipeline, and must not be assigned to or required by the Agent:

```text
DeepSeek-Harness-00-Project-Guide.md
DeepSeek-Harness-02-Research-Ledger.md
```

The ADR Lean spikes under `docs/blueprint/architecture-decision/lean-spike/` are
historical compiler mirrors.  They may be consulted for provenance, but they must not be
imported as production modules and must remain read-only.

## 4. Task boundaries

### P0-T02 — Freeze baselines and record provenance

1. Read the lead's P0-T01 record and confirm the selected checkout and toolchain.
2. Record the current Git branch, commit, remote, and clean/dirty status.  Use an
   isolated branch such as `agent/p0-baseline` if the lead has not already provided one;
   do not push it without explicit approval.
3. Hash and verify the immutable H03/H04 baselines:

   ```text
   H03 = 8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8
   H04 = 63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db
   ```

4. Hash every accepted ADR artifact listed in the Blueprint and compare it with the
   Blueprint manifest.  The manifest-recorded values at plan generation are:

   | Artifact | Manifest SHA-256 |
   |---|---|
   | ADR-01 | `1963c468ebaca2cd86635e88881ecda373b8278d0895c3805c52717e0a056dd5` |
   | ADR-02 | `f1b8e298edb7405a4a67fa10869d621a2bfeab80d5e5cf6a86feb752878699e5` |
   | ADR-03 | `0c6861367cf3061358366e90b2e2848649d96f5ad792185ed5f2e186d0520d48` |
   | ADR-03-CLOSURE | `2ef858c0a4d99bdf792e98e779d4c452884690f1a3d68addcefec6d827469a35` |
   | ADR-04 | `80beaaf2c29930527fee17419ae74718ea26140058fda67bb834d8cc435e36cc` |
   | ADR-05 | `86c555027a0a49bb40c95f1d612c12fcb6962d9801c5ed953ba9b1a7d1df04e9` |
   | ADR-06-CLOSURE | `e1baf7b96b2df72d1289e6148be3d801dc2477aa7c9230201f113ee91f118fea` |
   | ADR-06-SPIKE | `91239ee5aece9a485453aefd805bfbc37fec11a9c6e4e46841234462d63b4de4` |

   The plan-generation checkout already exposes a reconciliation issue: the repository
   bytes for ADR-01, ADR-02, and the ADR-06 spike do not match the values recorded in the
   Blueprint (the repository currently contains older/pending variants).  The observed
   repository hashes are:

   | Artifact | Repository SHA-256 at plan generation | Disposition |
   |---|---|---|
   | ADR-01 | `489a7e4d3d43e1bd12db99f185fe3931e1e4ee55dcade35238b0e1f69429c3fe` | report mismatch; do not silently replace |
   | ADR-02 | `7d83bd3380f082c5340c52b2b495f603ae1385567c6038a5b576d29276954a9a` | report mismatch; do not silently replace |
   | ADR-06-SPIKE | `7726a13f40dec56f2f6a57058d657808fe3da059577c36c5935c08b5b5c86a90` | report mismatch; do not silently replace |

   Treat this as a baseline-reconciliation subgate.  The Agent may document the
   discrepancy, but P0-T02 cannot claim a fully verified immutable baseline until the lead
   explicitly chooses one of the following:

   1. promote the newer accepted artifacts into the repository and update the repository
      snapshot;
   2. declare the repository variants canonical and issue a reviewed Blueprint/hash
      revision; or
   3. retain both versions under explicit historical/current paths and update the manifest
      to identify which one production formalization consumes.

   Choosing among these options is a lead-level provenance decision, not an Agent-level
   formatting fix.

5. Write a machine-readable provenance record, preferably:

   ```text
   docs/status/P0-baseline.json
   ```

   If an existing repository convention dictates another path, record that path in the
   handoff.  Include source paths, versions, commit metadata, all hashes, commands, raw
   outcomes, and a timestamp.

Acceptance: H03/H04 and ADR files are unchanged and verified against the manifest; no graph
edge or disposition entry is edited.  A mismatch or missing file is `blocked`, not an
invitation to regenerate the frozen input.  The known ADR mismatches above must appear in
the handoff report even if the lead later resolves them in a separate provenance commit.

### P0-T03 — Build the Definition Ledger

Create a machine-readable ledger, preferably:

```text
docs/status/Definition-Ledger.json
```

Create the validator alongside it, preferably:

```text
scripts/validate_definition_ledger.py
```

It must contain exactly one row for each of these 82 items:

```text
D1 ... D74
SAT
R.base
R.withdraw
R.iter
A.async
R.fail
R.full
Table1
```

Each row must include at least:

```text
id
kind
paper_anchor
target_module
treatment
delivery_status
evidence_state
depends_on
adr_refs
deferred_reason
notes
```

Use `STC/...` production module paths.  Reflect the current repository honestly: since
there are not yet substantive production modules, most implementation evidence is
`planned` or `deferred`, not `proved` or `tested`.

The top-level ledger should retain source identity and separate baseline from current
evidence, for example:

```text
schema_version
source_graph { path, sha256 }
source_disposition { path, sha256 }
items [ ... ]
```

For each item, copy H03's node identity and H04's disposition fields where available
(`target_layer`, `treatment`, `paper_relation`, `blocking_decisions`, and `readiness`).
Add the current `target_module`, `delivery_status`, `evidence_state`, and
`deferred_reason` without overwriting the H04 baseline.  The validator must derive the
expected ID set from H03's `numbered_nodes` and `auxiliary_nodes`, join the corresponding
H04 rows by ID, and reject duplicates, omissions, unknown IDs, and any inferred readiness.

Use the Blueprint status vocabulary for `delivery_status` and `evidence_state`.  The
validator should be runnable as:

```bash
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
```

The ledger must distinguish:

- paper fidelity and traceability;
- an accepted architecture decision;
- a compiled interface (`I`);
- a proved semantic theorem (`K`);
- a finite executable test (`E`);
- an adapter seam (`R0`).

Where possible, retain the disposition fields already defined by H04 (`target_layer`,
`treatment`, `paper_relation`, `blocking_decisions`, and `readiness`) and add the current
repository/module/evidence fields alongside them.  Do not replace H04's vocabulary with a
new informal status scheme.

Run the validator and preserve its output in the handoff.  A successful check must report
82/82 covered, zero duplicates, matching H03/H04 source hashes, and no inferred transitive
readiness.  Do not edit H03/H04 to make the ledger fit.

### P0-T04 — Bootstrap hygiene

Create or update:

```text
STC/Bootstrap.lean
```

The bootstrap should import only production modules that actually exist at this
checkpoint, use the `STC` namespace, and provide a minimal root smoke check.  It must not
import the historical ADR spikes or the Blueprint's standalone bootstrap mirror.  If the
production tree is still empty, keep the bootstrap minimal and record that P1 modules are
not yet available; do not add fake declarations merely to make a future import path pass.

Make the package entrypoint explicit: either have the root `STC.lean` import
`STC.Bootstrap`, or make the chosen bootstrap file the target actually checked by the Lake
build.  A file that exists but is never imported by `lake build` does not establish the
bootstrap gate.

Define and run a strict scan protocol for active production Lean code.  Create the
production directory if needed for the bootstrap, but do not invent P1 declarations:

```text
STC/**/*.lean
```

At minimum scan Lean files for:

```text
sorry
admit
axiom
unsafe
```

Exclude `.lake`, generated files, `docs/blueprint/architecture-decision/lean-spike/`,
and other explicitly historical paths.  Preserve raw lexical output at:

```text
docs/status/P0-scan-raw.txt
```

Use an explicit Lean-file glob and capture stderr as well as stdout:

```bash
mkdir -p docs/status
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe)\b' STC 2>&1 \
  | tee docs/status/P0-scan-raw.txt
```

If `STC/` did not exist before the bootstrap step, record the initial
`directory-absent` result separately; do not treat an empty search as proof that future
production code is clean.  If a match is only in a comment or string, classify it
separately using source inspection; never hide a match in active code and never report a
comment as a live declaration.

Run the real commands from P0-T01, normally:

```bash
lake env lean STC/Bootstrap.lean
lake build
# Re-run the strict scan block above and preserve its rg_exit in the handoff.
```

Interpret the captured status explicitly: `rg_exit=1` means no lexical matches,
whereas `rg_exit=2` (or another unexpected value) indicates a scan error and must be
reported as such.  This keeps a clean scan distinguishable from a failed command.

If Lean/Lake cannot be executed, record `not_run` or `blocked` with the exact error and do
not claim an interface pass.  The command's nonzero result caused solely by an absent
`STC/` directory must be distinguished from a compiler failure; after creating the minimal
bootstrap, rerun the scan and record both outcomes.

## 5. Execution order and review gates

1. Verify the P0-T01 record and current Git state.
2. Complete P0-T02 and commit only the provenance/status artifacts.
3. Complete P0-T03 and validate the 82-row ledger.
4. Complete P0-T04 and run the bootstrap and strict scan.
5. Produce the handoff report below.
6. The project lead reviews and accepts P0 before P1 starts.

The Agent must not edit the Blueprint's task definitions, H03, H04, or accepted ADRs.  A
purely mechanical documentation inconsistency (for example, an obsolete namespace path)
may be reported to the lead as a separate patch; do not silently combine it with the P0
baseline commit.

## 6. Evidence and acceptance matrix

| Task | Expected evidence | Completion condition |
|---|---|---|
| P0-T02 | `A + H` | H03/H04 match; ADR provenance is explicit; the reconciliation subgate is resolved or honestly marked `blocked` |
| P0-T03 | `A` | exactly 82 unique traceability rows, with no false readiness claim |
| P0-T04 | `A + I` (and `E` only if a smoke execution actually runs) | bootstrap and scan protocol are honest, reproducible, and placeholder-free |

`K` is not earned by any P0 task.  `R0` and `R1+` remain deferred in P0.

## 7. Handoff report

Return a Markdown or JSON report containing:

1. completed task IDs;
2. branch and commit;
3. files added or changed;
4. exact commands and raw results;
5. H03/H04/ADR hash comparison;
6. ledger coverage and uniqueness result;
7. scan scope, exclusions, and findings;
8. separate `A/I/K/E/R0/R1+` evidence states;
9. blockers, mismatches, and unresolved questions;
10. confirmation that no frozen input or semantic ADR was modified.

Suggested commit units are:

```text
p0: record immutable baselines
p0: add definition ledger
p0: add STC bootstrap hygiene
```

Do not start P1 or redesign the module DAG until the lead has reviewed this handoff.
