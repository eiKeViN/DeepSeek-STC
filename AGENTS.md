# DeepSeek-STC Repository Instructions

These instructions govern the paper-first Lean formalization of the Spatiotemporal Composability (STC) metatheory.


## Authority model

Authority is question-relative, not one total ordering:

- The paper is authoritative for the literal claims made by the source.
- The Formal Reference and frozen H03/H04 baselines are audited interpretation and provenance records; they preserve claims and defects but do not make defective claims true.
- Accepted ADRs and superseding ADRs are normative for the repaired formal target selected by this project.
- The Lean kernel is authoritative for validity of elaborated declarations and checked proof terms, but compilation alone is only interface evidence.
- The Blueprint, execution plans, and AGENTS.md govern implementation workflow and remain subordinate to the accepted semantic decisions.
- STC.Adapter and future Cordis artifacts provide only explicit abstraction or refinement evidence; they do not define the metatheory retroactively.

When sources conflict, preserve the literal source claim, classify the issue, record the approved repair in an ADR, and implement only the ADR-approved target. Never silently rewrite a frozen baseline or treat a successful build as proof of semantic alignment.

**ADR status rule.** File location alone does not imply acceptance.  In particular, `docs/blueprint/architecture-decision/json/` may contain accepted, proposed, incomplete, or superseded packets.  Normative production status comes from the artifact's explicit status/acceptance record.  A proposed or incomplete packet is review/provenance evidence only, and compiler success would establish interface evidence rather than acceptance.

**Provenance ruling (2026-08-27).** Repository bytes are canonical for ADR-01, ADR-02, and the ADR-06 spike: they intentionally differ from the hashes recorded in the Blueprint companion manifest. The full hash record and the lead ruling live in `docs/status/P0-baseline.json`; a Blueprint hash revision is a pending lead follow-up. Do not "fix" these files or re-report the mismatch.


## Paper fidelity and proof integrity

- Keep literal paper statements distinct from repaired Lean targets.
- Record false, vacuous, ill-typed, non-computable, or under-specified claims before selecting a repair.
- Do not hide missing hypotheses in an oversized `WellFormed` predicate.
- Distinguish semantic propositions from executable data and algorithms.
- Do not claim that a metatheory theorem verifies the Cordis runtime without a separate refinement theorem.
- Production Lean must not contain `sorry`, `admit`, project-defined unchecked `axiom`, or `unsafe` declarations.
- Never manufacture a proof with an empty relation, impossible invariant, degenerate transition, or behavior-erasing observation.  If a statement is not proved, preserve a precise blocked obligation or counterexample.


## Repository map and boundaries

The metatheory namespace is `STC`.  Use the module families prescribed by the Blueprint:

```text
STC/Foundation
STC/Core
STC/State
STC/Alpha
STC/Examples
STC/Conformance
STC/Adapter
```

The accepted P10/P11 production families are `STC/Control/**`, `STC/Staging/**`, and
`STC/State/Support.lean` plus their additive bridge modules. `STC/Scoped/**` is the
completed independent P12 lane. P13 global modules are additive under the ownership
paths recorded in `docs/plans/P13-Execution-Plan.md`.

- `STC.Adapter` is the reserved abstract R0 abstraction/simulation seam.  Do not put concrete Cordis implementation declarations into the metatheory namespace; the `Cordis` name and its namespaces are reserved for a future runtime-side integration/refinement project.
- Frozen inputs (read-only): `docs/blueprint/baseline/` (H03 graph, H04 disposition, Formal Reference) and every explicitly accepted ADR artifact.  Proposed ADR packets in the same directory remain non-normative and may be edited only by a dedicated ADR repair/promotion task.
- `docs/blueprint/architecture-decision/lean-spike/` is historical and read-only: never import it from production modules and never edit it.
- Derived status records live in `docs/status/` (`P0-baseline.json` provenance; `Definition-Ledger.json` traceability).  They are reports generated from frozen inputs, never sources of truth.  Execution plans live in `docs/plans/`.

The current accepted architecture includes relation-parametric laws, explicit partiality and failure results, the positive finite state/registry shell, lifetime-safe `IncarnationId` with explicit alpha actions, ranked iterators, and the ADR-06 equivalence/transport contracts.  Do not reopen these decisions implicitly.


## Decision Packets and Pending Lanes

As of 2026-08-29, separate status records accept ADR-07, ADR-08, ADR-09, and ADR-10.
P10 Control, P11 Staging, and P11 Support Core are merged; this P11 integration
closeout adds their production bridges and finite evidence.  Acceptance and
compilation remain distinct from kernel theorem strength and runtime refinement.
ADR-10 is accepted architecturally and Scoped production is merged as P12. P13 owns
the old-paper single-realm global metatheory/conformance lane; Cordis refinement and
realm-aware global theorems remain pending.

Downstream integrations for accepted ADR-07..10 must preserve these reviewed boundaries:

- Control: orchestration and lifecycle are distinct relation classes combined by a typed labelled `Step`; the abstract semantics has no scheduler; `InFlight`, landing/abort boundaries, complete failure payloads, and freshness metadata boundaries remain explicit.
- Staging: `R+` is authoritative; `Rb` is an `AtomicProfile`-controlled finite macro/view with embed/project/stable-image, forward-simulation, and profile-relative adequacy contracts, never an independently maintained calculus.
- Support: `SupportOperator` is positive and its canonical support is a least fixed point; `SupportRel` points from provider/parent to dependent, induction names its converse, and `SupportWF`/`SupportOrder` or a rank certificate is explicit.  Support rank is not iterator rank and is never hidden inside `WellFormed`.
- Scoped coeffects: only an accepted, complete ADR-10 packet may make typed `RealmRef`, semantic/executable resolver separation, finite overrides, persistent isolate/intercept contexts, metadata precedence, physical distinctness, and one-way flat embedding normative.


## Lean file format conventions (mathlib style)

Formatting authority: the pinned mathlib sources in `.lake/packages/mathlib/` are the reference; these rules summarize them for `STC/` production modules.  Frozen spike files under `docs/blueprint/architecture-decision/lean-spike/` are exempt (read-only).

### File skeleton

Every production `.lean` file, top to bottom:

1. Optional file header comment (provenance/status note), then
2. `module` — Lean 4.33 module declaration; the module name defaults to the file path, so write it bare.
3. Imports, one per line, sorted alphabetically:
   - umbrella files (`STC.lean`, `STC/Bootstrap.lean`, future per-family roots) contain **only** imports plus a module docstring, all as `public import`;
   - leaf files also use `public import` (mathlib makes all imports public — they re-export transitively).  Plain `import` is for genuinely internal dependencies only.
4. `/-!` module docstring immediately after the imports:
   - `# Title` on the first line;
   - prose summary;
   - optional `## Main declarations` bullet list naming the file's API surface (`* `Finset.card`: ...` style).
5. `universe`, `variable`, `open`/`open scoped` statements after the module docstring.

### Documentation

- `/-- ... -/` docstrings on every important declaration (`def`, `structure`, `class`, `theorem`): one-line summary first, details after a blank line; mathlib sentence style, backticks around code.
- `/-! ... -/` block headers mark sections and declaration groups — never individual declarations.
- `## Main declarations` is required in umbrella files, encouraged in leaf files.

### Scoping

- Wrap every file's declarations in `@[expose] public section … end` (mathlib form).  The module system demands that exported theorems unfold only *exposed* definitions: with plain `public section`, every `rfl`/`change`/`simp [def]` proof over a public declaration fails with "Not a definitional equality".  `@[expose]` is not optional.
- One named `section Name … end Name` per concept; a concept's definitions and its theorems stay together inside it.
- Section-scoped `variable` replaces repeated per-declaration binders (`{α : Type u}`, `[DecidableEq α]`, explicit parameters exactly as mathlib writes them).  Type-family declarations (`Store (V)`, `PartialMap (α) (β)`, …) keep their explicit parameters.
- Section variables are auto-included only when used; where Lean over-includes an unused instance, drop it with `omit [Foo] in` (linter `unusedSectionVars`).
- Notations needed by several sections stay outside sections (precedent: ADR-03 closure spike).
- Prefer `abbrev` over `def` when proofs would otherwise need explicit `unfold` of the declaration.
- Split large proofs into per-case lemmas and assemble them in one theorem.

### Evaluation

- No top-level `#eval` over `@[expose]`d declarations in library modules.  Exposure marks declarations external, and the interpreter then needs the package's native shared library — which cannot be linked on Windows (DLL export limit of 65,535 symbols; `Mathlib:shared` link fails at ~203k symbols).  Executable checks are `example … := by decide` blocks that pin the expected value at elaboration time; `#eval` belongs to scratch/tooling files outside the library.
- Do not set `precompileModules`/shared-library facets on `lean_lib` targets: they pull the dependency's shared library into the link and fail the same way.

### Verification

Before committing, every touched file must pass `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true <file>` with zero errors and zero linter warnings.

For semantic search of Mathlib declarations (finding lemmas/instances by concept rather than by name), prefer the `mathlib-search` skill before falling back to `grep` over `.lake/packages/mathlib`.

## Working loop

When operating in a newly created Git worktree, initialize its ignored Lake
state before the first build.  This links a compatible existing dependency
checkout while keeping branch-specific build outputs local:

```bash
python scripts/prepare_worktree_lake.py
```

If no populated compatible worktree exists, run `lake update` once in a
checkout with network access and rerun the helper.  Do not share the entire
`.lake` directory between worktrees.

Before and after each major task or critical checkpoint, run the narrowest applicable checks and record their outputs.  During iteration, check each touched file individually, in import order (root module of the change set first, then each importer in turn), until every one exits 0 with zero warnings; the full `lake build` is the acceptance gate, not an iteration step.  Record the real exit code (redirect to a log, then `echo $?`): a pipeline through `head`/`grep` masks compiler failures.

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/<changed-file>.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
```

- Use the pinned Lean 4.33.0 / Mathlib v4.33.0 toolchain.
- `lake env lean` does not read lakefile `leanOptions`; pass the `-D` flags above explicitly or single-file checks disagree with the IDE and with `lake build`.  The CLI single-file check also does not reliably refresh `.olean` artifacts (the IDE language server owns the build directory and stale `.olean.hash` files can fake a passing check); when downstream files need the fresh `.olean` chain, run `lake build <Module.Name>` for that target.
- `scripts/scan_lean.py` exit codes: 0 = lexical match found (inspect and classify; a comment/string match is not a live declaration), 1 = clean, 2 = scan error.  A clean scan covers current files only, not future code.
- Keep the Definition Ledger current after each task: edit rows in place using the Blueprint vocabulary (delivery: `planned/in_progress/completed/blocked/deferred`; evidence: `pending/aligned/passed/proved/tested/seam_only/deferred/not_applicable`) and rerun the validator.  
- Do not rerun `gen_definition_ledger.py` after P0 — it regenerates from its P0 curation tables and would wipe later evidence.
- Keep commits focused, do not overwrite other agents' work, and report any baseline/hash or namespace mismatch instead of silently normalizing it.
