# Lean 4 proof & declaration debugging — reusable lessons

Collected from the P0-P2 formatting sessions, P3-P4 partial/iterator, P6 alpha
transport, the ADR-07..10 spike repairs, P12 Scoped, and P13 T01/T02/T02R/T03
(2026-08/09).  Entry format: symptom → root cause → fix.  Toolchain: Lean
4.33.0, mathlib v4.33.0.

## 1. Verification & process

### CLI checks must replicate project options

The command discipline is in AGENTS (Verification/Working loop).  The why:
`lake env lean` does **not** read lakefile `[leanOptions]`, and with the
default `autoImplicit := true` undeclared identifiers silently auto-bind as
implicit parameters — the file "compiles" while the IDE (which reads the
options) reports unknown-identifier errors.  `lake env lean` must also run
from the **repo root**; from a subdirectory it degrades to a bare elan env →
`unknown module prefix 'Mathlib'`, a false diagnostic.

### Fix errors in priority order

Syntax → type errors → unsolved goals/tactic failures → linter warnings.
Higher-priority errors make lower ones unreliable; a cascade (dozens of
"Invalid field notation", `sorry` placeholders, kernel "declaration has
metavariables") usually collapses to one root cause — fix the first real error
and re-check.

### Which binary actually ran

`lean`/`lake` invoked outside the repo resolve elan's *default* toolchain, not
the repo-pinned one (this environment had an uninstalled v4.33.1 default).
Minimal repros "passing" from `/tmp` can silently test the wrong toolchain.
Always run repros with `lake env lean` from the repo root (pinned toolchain +
LEAN_PATH).

### Experiment-first debugging

Bisect a repro into factors (import / namespace / def shape / tactic) — one
factor per scratch file; a batch of variants per compile cycle beats sequential
theorizing.  Iterate on a *copy* of the failing file (or a minimal
`/tmp` file importing the failing modules) and port the fixes back, so a
multi-error cascade does not churn the real file.  The IDE diagnostics can be
stale across edits; a fresh `lake build` / `lake env lean` output is
authoritative.

### Lake targets, .olean artifacts, and exit codes

- `lake build` builds only the `STC.lean` import closure; modules not yet
  imported by `STC/Bootstrap.lean` need explicit targets
  (`lake build STC.Core.Coeffect …`).
- The CLI single-file check does **not** reliably write `.olean` artifacts
  (the IDE language server owns the build directory), and a failed build can
  leave `.olean.hash` files without the `.olean` — the next CLI check then
  "passes" via a no-build cache hit.  Clean the stale `*.hash`/`*.trace`
  files or build the target explicitly: `lake build <Module.Name>`.
- Record real exit codes: redirect to a log and `echo $?`.  Piping through
  `head`/`grep` reports the pipeline's exit, masking compiler failures.

### Mathlib lookup habits

Grep the pinned sources (`.lake/packages/mathlib/Mathlib/…`) for lemma/instance
names instead of guessing (`Finmap.mem_keys`, `Finmap.lookup_insert_of_ne`,
`Finmap.lookup_isSome`, `Finset.disjoint_left.mp`, `instDecidableRelSubset`,
`Equiv.Perm` in `Logic/Equiv/Defs`).  `lake env lean` on a copy of a file with
`#check @decl` lines appended is the fastest way to inspect elaborated
signatures after a refactor.

## 2. Module system & exposure

### `@[expose] public section` is mandatory

Convention: AGENTS (Scoping).  Diagnostic: `theorem t : (f x).1 = x.1 := rfl`
fails with `Not a definitional equality: the left-hand side` in a `module`
file — exported theorems may only unfold *exposed* declarations, and plain
`public section` marks them public but not exposed.

`Unknown identifier` for an imported declaration: in `module` files
declarations default to **private**; only `public section` (+ exposure)
exports them.  `cannot import non-module X from module`: stale pre-`module`
oleans — build the dependency chain first.

### `#eval` over exposed declarations fails on Windows

Rule and rationale (DLL export cap, `by decide` pinning) live in AGENTS
(Evaluation section); full diagnosis:
`docs/status/eval-exposed-decls-debug-report.md`.  Symptom to recognize:
`Could not find native implementation of external declaration '…._redArg'`.

### Imports and attribute placement

`import` lines must precede any `/-! … -/` module doc block; `omit [X] in`
and `set_option … in` must precede the *docstring* of the declaration they
modify (the doc comment attaches to the next declaration; `omit` is not one →
`unexpected token 'omit'; expected 'lemma'`).

### Frozen `STC.StageResult` shadows `STC.State.StageResult`

Symptom: in a file with `open STC STC.State STC.Control`, `StageResult S N N
Unit` elaborates as a *3-parameter* type (P10's `STC.StageResult (S E Q :
Type u)`) and `Option (StageResult …)` fails with "Function expected at".  The
`open STC` brings the top-level frozen declaration, which wins over the T02R
`STC.State.StageResult` (4 parameters).  Fix: qualify `State.StageResult`
everywhere in the fixture; the 4-parameter one then elaborates.

### Frozen single-universe `StagingModel` forces one section universe

Symptom: instantiating `StagingModel` with mixed-universe carriers (e.g.
`GlobalState` with `Ambient : Type x` while the orchestration labels live at
`max u v w`) gives "stuck at solving universe constraint"; ULift with explicit
levels, ascription-based ULift, and pinned-universe `abbrev`s all fail with a
stuck `DecidableEq ?m` (the annotation changes the section-variable capture
order).  Root cause: the frozen `StagingModel` takes all six parameters in
*one* universe.  Fix: pin all section carriers at one universe
(`{Name : Type u} {Key : Type u} … {Ambient : Type u}`) — the concrete
Section-4 instantiations are single-universe anyway; record the restriction.

### Incremental comment-block discipline for fixing one declaration at a time

For a long file being repaired head-first: place ONE `-/` terminator right
before the section ending (the anchor), and silence a declaration by putting
`/-` in front of it (block comments nest).  Advance by: insert `/-` before
declaration #n+2, delete the `/-` before #n+1, fix #n+1.  Invariant: a single
active prefix; everything after it sits in one comment block closed by the
bottom anchor.

## 3. Decidability & typeclass synthesis

### `Decidable` synthesis does not unfold `def`s

Symptom: `decide (P x)` / `if h : P x then` fails with `failed to synthesize
Decidable (P x)` even though `P` unfolds to decidable components and the
instances are in scope.  Instance search never delta-reduces the compound
`def`, so no `instDecidableAnd`/`Finset.decidableMem` candidate matches.

Fixes, by situation:

- `if`/`by_cases` guards in **executable defs**: write the condition
  syntactically unfolded (`if n ∉ current ∧ n ∉ ledger.everIssued ∧ …`).
- `decide`-checked Props: a one-line bridge instance
  (`instance … : Decidable (P x) := by dsimp [P]; infer_instance`).
- **Decidability-critical carriers: make them `abbrev`** (reducible — the
  elaborator unfolds them where regular `def`s stay stuck).  This covers
  carrier types (`toyModel.Realm`) and proposition defs
  (`declaredSatisfied`, `targetSatisfied`) alike.
- Core signature to remember: `decidable_of_iff (a : Prop) (h : a ↔ b)
  [Decidable a] : Decidable b` — the plain Prop comes **first**.

### Bool-valued carriers and stuck match decidability

For executable predicates over opaque data (`Finmap.lookup`, `Quot`-based
values), `Decidable (match e with …)` synthesis fails: the synthesizer must
reduce the match scrutinee and the application blocks it.  Restructure to
Bool carriers with the coercion at the outside:

```lean
-- works: the coerced type is `(Bool expr) = true`, decidable without reducing
def activeNames (state : S) : Finset N :=
  state.registry.keys.filter fun name =>
    (Option.map (fun fiber => decide (p fiber)) (Finmap.lookup name state.registry)).getD false
```

Do **not** return a Prop from the `Option.map` lambda and let `getD`'s default
elaborate through `Coe Bool Prop` — the elaborated `getD (false = true)` term
is a stuck match for `Decidable` synthesis; use `decide` inside the lambda.

Related: `decide` needs a **closed** goal — free variables error with
`Expected type must not contain free variables`; use `simp` with the
structures reduced instead.

### Instance argument elaboration order

A theorem's implicit typeclass args are synthesized left-to-right **before**
later explicit args unify the type parameters — `f defaultX argThatPinsM`
fails with `cannot synthesize DecidableEq (Realm ?m)` even though the last
argument pins the carrier.  Fix: pin the type with the *first* explicit
argument, pass named args `(K := …) (M := …)`, or define pinned wrapper defs.

### Structure instance params must precede dependent parameters

`structure FlatEmbedding (M) (Flat Scoped) (ops : RealmStoreOps M Scoped)
(ρ : Resolver M)` where `Resolver M` carries `[DecidableEq K]`: the `ρ`
parameter's type elaborates with the *section* instance while the fields
elaborate with the *auto-included structure* instance — two distinct locals,
not defeq → `synthesized type class instance is not definitionally equal`
on every field.  Fix: put instance params first
(`(Flat Scoped : Type x) [DecidableEq K] (ops) (ρ)`).

### Decidable over infinite carriers

`Decidable` for a pointwise `∀ x, …` over an infinite carrier does not exist
(`CounterState = Nat × Nat`); finite carriers (`Fin n` + Fintype) do.  For
concrete instances construct directly: `exact isTrue (by …)` /
`exact isFalse (by intro h; cases h)` — or prefer data-level `Bool` checks.

### Fixture data defs: make them `abbrev` to unlock `rfl`/`decide`

Symptom: closed computations over a chain of fixture state/cell `def`s
(`Finmap.lookup n s8.registry = some …`) need ever-growing `simp` sets and
`congr`; `rfl`/`decide` stall.  Fix: convert the pure-data fixture defs
(states, cells, view maps) to `abbrev` — the kernel and `decide` then unfold
the whole chain, the lookup lemmas collapse to `congr`, and rule guards like
`hlook`/`hstage`/`hrank`/freshness become `rfl` or `by decide`.  `simp` args
that the linter reports unused afterwards are exactly the ones the
reducibility made obsolete — trim them.  Keep `def` only for declarations
with proof bodies (`rulesSem`) and for the stage/accumulator helpers (their
`if`/arithmetic needs the tactic-level control).

### `simp` cannot reduce `if`-conditions over Quot-blocked chains

Symptom: `unfold fixtureStage; simp` on a goal
`(if 0 < s3.ambient then …) = …` leaves the `if` intact — `s3.ambient` goes
through `editCell`'s `match Finmap.lookup …` whose scrutinee is Quot-based and
not definitionally reducible.  Fix: give the simp set the state-chain defs
*and* the payload helpers and the cells (`[s3, s2, s1, iterState, beginState,
editCell, updateFiber, allocate, iterPayload, beginPayload, rulesSem, cell1]`)
so the lookups are rewritten by the `updateFiber`/`allocate` lemmas; the
linter's unused-arg hints trim the set.  Where the head is a structure
projection (`rulesSem.stage …`), `change fixtureStage … = …` first pins the
reduced form (see §5).

### `decide`/`omega` over stuck projections

Symptom: `omega`/`decide` on a goal mentioning
`(State.StageResult.halt {…} 1).state.ambient + 1` reports "No usable
constraints" — the `StageResult.state` match-def projection is not unfolded.
Fix: `simp [State.StageResult.state]` (and `State.StageResult.inverse?`/
`.failure?` for hypotheses) before the arithmetic tactic.

### `unusedSectionVars` linter

Lean auto-includes section variables it considers used (often through a hidden
instance parameter of a mentioned def); the linter disagrees.  `omit
[DecidableEq K] in theorem …` when the statement is genuinely instance-free
(verify with `#check @theorem`); otherwise declare the binder explicitly —
explicit binders are not linted.

## 4. Lean 4.33 elaboration regressions & definition forms

Toolchain-level: minimal repros fail with the pinned binary alone (no imports,
no lake env), so they are not project conventions.

### `↔` in a nested `∀` fails to elaborate

`intro x y hxy` on `∀ {x y}, R x y → (Q ↔ R)` fails with "no additional
binders"; term-mode fails with metavar-typed binders; even
`∀ {x y}, R x y → True ↔ True` fails.  The paired-arrow body elaborates fine.
Workaround: write `(Q → R) ∧ (R → Q)` in **definition statements** (the poison
is in statement elaboration, landing on every downstream consumer); top-level
`↔` goals are fine.  Consider re-testing on v4.33.1.

### Proposition evaluation is stuck

`decide (¬ P)` reports "typeclass instance problem is stuck"; `match P with`
reports "redundant alternative" — even though `P` reduces to `False` and a
bare `P → False` proof works.  Don't evaluate propositions: compute on the
**data** (a `Bool`-valued constructor match over concrete values) and keep the
semantic statement as a theorem beside it.

### `rfl`/`decide`/`simp only` over closed `if`s

`simp only [defs]` leaves `(if r = r then some v else s r)` intact; `rfl`
reduces it through the `Decidable` instance — but only when the scrutinee is
not a variable.  With hypotheses (`q ≠ r`), use `simp only [defs]` then
`grind only` (or `by_cases`).  For a chain needing a closed-`if` reduction,
`rw [show … = … from rfl]` works where `simp only` does not.

### WF-recursive (`termination_by`) defs

- `rw [def]` → "Invalid rewrite argument"; `simp [def]` → looping
  (`def.eq_1`); `unfold def` works.
- After `unfold`, `simp only [h]` on a `match _hrun :` scrutinee makes no
  progress (motive binder) while `rw [h]` rewrites it — and `rw` closes the
  goal itself when the result is `rfl` (a trailing `rfl` is then an orphan
  "No goals to be solved").
- Several `rw` rules in one call do **not** iota-reduce between rules — split
  with `simp only []`: `unfold execFrom; rw [hyield]; simp only []; rw [hinner]`.
- `rw [thm (premise := by rfl)]` with a metavariable premise fails — supply
  the hypothesis explicitly; `rw` with an uninstantiated premise puts the
  **main goal first** (use `pick_goal 2` or chain bottom-up).
- **The kernel cannot reduce a WF-fix in `decide`**: pin executable evidence
  with **equation theorems** instead (`execFrom … = .success {…}` by the
  rw-chain, then `unfold field; rw [trace_eq]`).
- A `match h : …` binder used only in `decreasing_by` triggers
  `unusedVariables` — rename to `_h`.

### Structure-literal projections reduce asymmetrically

`exact hs.2` / `simpa using ⟨…⟩` fail with "Type mismatch": the term's type is
already the unfolded form while the expected type still shows
`{ … }.prefixUndo` unreduced.  In order of preference: `cases hr` on an
`op input = some r` equality (substitutes definitionally); `change <unfolded
form>` before `exact`; annotate tuples with the **unfolded** type; remember
`Option.some.inj hr` returns `{…} = r` — for `subst`/`rw` use
`(Option.some.inj hr).symm`.

Multi-line `{ field := … }` literals in **theorem statements** hit
`unexpected identifier; expected '}'` (after `=`, a multi-line `{…}` is
ambiguous with a binder block): one line, or an ascribed intermediate def.
Record literals inside `change` targets need type ascriptions
(`({ state := … } : OpResult …)`), else "invalid {...} notation".

Structure **literals cannot reference their own fields**
(`replay := fun _ s => controlEdit …` inside the literal fails — the field
name is not in scope).  Hoist helpers:
`def factorSelectedMap …; def factorControlEdit …` then reference the helpers.

### `local notation` inside structure field types

`structure P … [DecidableEq Name] [DecidableEq Key] where f : GState → Prop`
with `local notation "GState" => GlobalState Name Key …` fails with a stuck
`DecidableEq ?m.2` instance problem (Lean 4.33 elaboration bug around notation
expansion in structure headers).  Expand the notation manually in the field
types; the structure's own `[DecidableEq …]` binders must stay (section
instances are shadowed by the structure params and do not apply).

### Section-variable auto-inclusion skips local-notation header expansion

Also applies to implicit section-parameterized `abbrev`s used in declaration
headers (the R.base `BaseState` subtype hit `DecidableEq ?m` stuck — the
abbrev's auto-included implicit params never resolve in a header).  Fix:
spell the carrier's parameters explicitly in the `abbrev` binder list (they
shadow the section variables) and reference it through a local notation
whose RHS passes every argument explicitly; instance params still resolve
via typeclass search in headers (same as the `GState` notation).  Related:
a `dite`/`if h : P` over an undecidable ∀-Prop (`Decidable (StagingStable
state)` synthesis fails) — for a semantic projection use `by classical` and
mark the enclosing def `noncomputable`; then `simp [base.2]` discharges the
positive branch.

### Section-variable auto-inclusion skips local-notation header expansion

Symptom: a local notation whose RHS needs a section variable to fill an
implicit parameter elaborates fine in terms (`#check`, def bodies) but fails
with `don't know how to synthesize implicit argument 'Key'` when the notation
expands in a **declaration header** (`def foo (sem : GSem)`).  The
auto-inclusion of section variables for implicit parameters does not run
inside the notation expansion in header positions.  Fix: make the parameter
**explicit** in the carrier structure by writing it in the binder list —
`structure ComponentSemantics (Key : Type u) (State : Type u) …` shadows the
section variable (legal, preserves the API) — and pass it explicitly in the
notation.  Watch out for the sibling trap: with the parameter *implicit*,
`ComponentSemantics Key State …` mis-elaborates because the bare constant
reference auto-applies the section `Key` first, shifting every argument.

### Inductive constructor headers: expand notations, use arrow form

Symptom (constructor-indexed rules): `| insert {before : GState} {child :
GCell} : (hfresh : …) → … : Result` with section-level local notations fails
with "Unknown identifier hfresh"/"unexpected token ':'" — the same
notation-in-header elaboration bug as structures.  Fix: expand `GState`/
`GCell` manually in the constructor *binder* types (the result type may keep
the notation).  Second: a colon-form constructor whose premise chain includes
a multi-line `∀ (x : T) (y : T), …` premise fails to parse ("unexpected token
':'"); write every premise line ending in `→` and the result last, with no
trailing colon.  Third: `∀ name cell', P` breaks under `autoImplicit=false`
in constructor premises too — bind explicitly `∀ (name : Name) (cell' : GCell)`.

### Named case patterns on fixed-index constructors bind explicit fields only

Symptom: `cases h with | iter hlook hphase htarget hstage hrank =>` works and
binds the explicit fields in order, but the constructor's *implicit* fields
(cell, the stage-result state) appear as `cell✝`/`after✝` — names that cannot
be written in source; `rcases`/`⟨⟩` patterns over such fixed-index
constructors shift unpredictably ("hreal unknown", wrong bindings).  Fixes:
(a) carry the needed data in the label payloads instead (the stage/landing
result, accumulator middle, launch token — also mandated by the rich-label
convention), so label `cases` bind them by name; (b) for equalities like
`hlook : lookup n s.registry = some c`, `cases hlook with | refl` substitutes
`c` by name — but only when the motive does not force the Quot-reduction;
(c) `Option.some.inj`-style: `have hcell := (Option.some.inj hlook).symm; rw
[hcell]; simp` closes projections over the record without naming its base.

### Multi-line record *updates* are parse poison everywhere

Symptom: `{ cell with phase := …,
 committedView := … }` spanning lines
fails with "unexpected identifier; expected '}'" — as a def body, inside
`change` targets, and inside tactic terms.  A multi-line structure *literal*
after `:=` in a def is fine, but an *inline* multi-line literal inside a
field (`component := { key := 1, …,
 iteratorCode := … }`) is not.  Fix:
single-line every record update and every inline literal; for the larger
updates hoist helpers (`beginPayload sem cell flight`, `iterPayload …`) whose
body is a single-line update.

### `if` binders under `autoImplicit=false`

Symptom: `if _ : P then …` mis-elaborates; and `split at h with hpos` fails
to parse ("unexpected token 'with'").  Fix: name the binder in the def
(`if _hpos : P then …` silences the unused-binder linter too).  In proofs,
avoid `split` on the `if` (its branch hypotheses get unreferable `h✝` names):
use `by_cases hpos : P` then `rw [dif_pos hpos] at h` / `rw [dif_neg hpos] at h`
to reduce the conditional — the named hypothesis then feeds `omega`.

### `autoImplicit=false` breaks membership-∀ `fun` binders

`fun m hm => …` against `∀ m ∈ l, P m` mis-elaborates `hm : S` (the element
type) in **some positions** (fun-arguments to applications and
structure-literal fields; theorem statements elaborate fine).  Write the
expanded form `∀ (m : T), m ∈ l → P m` and annotate binders explicitly:
`fun (m : T) (hm : m ∈ l) => …`.

### Reserved keywords and identifiers

`local`, `prefix`, `new`, `meta` are Lean keywords; `at` is a reserved token;
`not` is Coq syntax (use `¬`).  Parse errors land on binders/fields named
after them — rename (`localVal`, `prefixUndo`, `atKey`, `localOp`, `newVal`,
`metadata`) and update all uses in one pass.  Local binders named like
constructors in scope (`intro a b hab` next to `Toy.a`) trigger the
constructor-resemblance linter — rename.

### Universe linter on structures

"universes `w`, `x`, `y` only occur together" on a structure with per-field
universes: collapse the field universes to one and drop the unused universe
declaration.

### Section/notation scoping

Local notations are scoped to their section — notations used by several
sections must be declared outside them.  Section variables are auto-included
only when used; `#check @decl` after refactoring catches signature drift.
Type-family declarations keep their explicit parameters even when the same
names are section variables (shadowing is legal and preserves the API).

## 5. Tactic pitfalls

### `simp` def-listing; cross-module wrapper heads

Equation lemmas of match-defs are not `@[simp]` by default — `simp` never
unfolds `OptionRel`: list the def (`simp [OptionRel] at h ⊢`).  Cross-module,
`simp only [P5.coeffect_lookup_erase]` on a goal whose head is `Coeffect.lookup`
reports "made no progress" while `rw`/`exact` work: simp's preprocessing
normalizes the lemma LHS but not the goal subterm heads for def-wrapped store
operations.  Use `rw`/`exact` for the wrapper lemmas; direct Mathlib
`Finmap.lookup_*` lemmas work in `simp` after `change`/`unfold` to the
`Finmap.*` form.

`simp only [lemmas]` excludes the default simp set (no-confusion,
`Option.map_some/map_none` disappear) — prefer plain `simp [defs, hyps]`.
Unused simp arguments (`unusedSimpArgs`) are safe to remove.

### `unfold … at h` leaves beta-redexes

`unfold liftProvide at h` substitutes the body but does not beta-reduce the
application or the dite/match in `h`; `rw` then finds no occurrence.  Put the
def in the simp set instead: `by_cases hnone : …` then
`simp [liftProvide, hnone] at h` — unfolds, beta-reduces, reduces the dite,
and closes contradiction branches.  (Avoid `split`'s auto-names `h_1`/`h_2`;
prefer `by_cases` with an explicit name.)

### `cases` / `subst` context rules

- `cases e with` without a named equation does **not** split hypotheses that
  mention `e` — use `cases h : e with`; the named equation then rewrites
  `h`-style hypotheses via `simp [OptionRel, hl, hr] at hlr`.
- `cases h : e with` *generalizes goal occurrences of `e`* — afterwards
  `rw [h]` on the goal fails ("pattern not found"); drop the redundant rw.
- `cases p0` **clears `p0`** — use the branch binder in the branch.
- `subst` only reads top-level equality hypotheses (extract from composites
  first) and can silently eat `rcases`-bound context — prefer
  `rw [← hEq] at hn` / `simp […, ← hEq]` in that situation.
- `rw` at a **projection** (`rw […] at hmem.2`) fails ("expected single
  reference to variable") — destructure first
  (`rcases hmem with ⟨_hkeys, hnonempty⟩`).

### `rw` matching, direction, and goal shape

- `rw` does not unfold target defs when matching (a structure-update
  projection may even reduce away): list the defs
  (`rw [boundProvider, updateFiber_lookup_eq]`), use `simp [defs]`, or
  `change`-pin the goal to the exact reduced form before the rw.
- Direction: `rw [iff]` rewrites LHS→RHS; goals in `≠ ∅` form need
  `rw [← nonempty_iff_ne_empty]`.  After a `simp` has already reduced a
  singleton membership to an equality (`hk : key = 10`), don't re-`rw
  [Finset.mem_singleton]`.
- `rw`'s argument unification against lemmas with symmetric-looking binders
  can pick the wrong instantiation (see the Finmap entry in §7) — pin with a
  `show`-wrapped closed statement or test in a scratch file.
- `apply congrArg` on `map f s = map g s` can pick a bad unifier — use
  `congr 1`.

### `constructor` splits one level only

For an n-ary conjunction goal, `constructor` splits off the first conjunct
and leaves the rest as one goal; n consecutive `·` blocks then misalign.
Use `refine ⟨?_, ?_, …⟩` with one hole per conjunct.

### Trivial-goal leftovers after `<;>` case splits

`cases a <;> cases b <;> cases c <;> simp […]` closes every branch except the
single nontrivial one; the remaining goal then takes the direct proof.  A bare
`exact htrans` after the split fails with `expected True → True → True` — the
first remaining goal is a trivial branch.

### Match-def equations on free-variable sub-patterns

`simp [toyLifecycle, …] at hstep` leaves the whole `match` for a `.divert
owner choice` case where `choice` is a variable — the def's equations need
constructor scrutinees.  `cases choice` first, then `simp … at hstep` per
constructor.

### `simp at h` over a def-application hypothesis

`simp at h` errors "made no progress" for `h : toyModel.baseOrch …` — `h`'s
type is a structure *projection*; the set must unfold both the record and the
underlying def: `simp [toyModel, toyBaseOrch] at h`.

### `omega` needs the defs unfolded

`ext <;> omega` fails with counterexamples mentioning raw def terms — insert
`simp [def]` before `omega`.

### `congr` over-decomposes arithmetic values

Symptom: on `some {before with ambient := before.ambient + (a+b)} = some
{before with ambient := (before.ambient + b) + a}`, `congr 1` (twice) or bare
`congr` descends into the ambient *value*, producing nonsense subgoals like
`before.ambient = before.ambient + b` ("e_ambient.e_a").  Fix: prefer
rewriting the arithmetic side to definitional equality and let `rfl` close:
`rw [Nat.add_assoc, Nat.add_comm b a]`, `rw [Nat.sub_add_cancel hpos]`,
`rw [Nat.add_zero]`; alternatively `grind only` closes the whole
record-with-arithmetic equality.

### `unfold` of a def under a structure-projection head

Symptom: `unfold fixtureStage at hstage` on a hypothesis/goal headed by
`rulesSem.stage …` (the literal's field) fails ("did not unfold").  Fix:
`change fixtureStage <args> = …` first to pin the reduced form, or include
the structure literal (`rulesSem`) in the simp set.

### `simpa using h` direction

When `simpa […] using h` reports a type mismatch and the simplified `h` is
`A = cell'` while the goal is `cell' = A`, use `using h.symm`.

### Data-conjunct guards: simp + decide, birth via a `congr` history lemma

For guards like `CanonicalInitialCell s (some 1) 2 cell2`, the data conjuncts
close with `simp [CanonicalInitialCell, Registered, <state-chain defs>,
Finmap.lookup_insert]; decide` — the `∃ fiber, lookup 1 s.registry = some
fiber` needs `Finmap.lookup_insert` in the set.  The birth clause
(`1 = nextBirth s`) survives because the history projection goes through the
Quot-blocked `editCell` match: prove a separate `s4_history : s4.allocationHistory
= [1] := by congr` and `rw [s4_history]`.  Disjointness guards (`∀ name cell',
lookup … → Disjoint …`) need `by_cases hname : name = 1`: the positive branch
recovers the cell via `simpa […, Finmap.lookup_insert] using h.symm` + `subst`,
the negative branch closes by `rw [Finmap.lookup_insert_of_ne (a := 1) (a' :=
name) (s := s0.registry) hname, Finmap.lookup_empty] at h; cases h`.

### Dot-notation `.mp` and explicit parameter annotations

`Equiv.apply_eq_iff_eq.mp` fails ("unknown constant") because the theorem's
first parameter `(f : α ≃ β)` is explicit — write
`(Equiv.apply_eq_iff_eq (χ : Equiv.Perm N)).mp (…)`.  For under-determined
implicit params, annotate at the call site:
`raiseLabel (Q := Q) (V := V) owner …`.

## 6. Well-foundedness & induction

### `WellFounded` is a structure in Lean 4.33

`intro name` on a goal `WellFounded r` (or a def wrapping it) fails with "no
additional binders" — it is a structure, not a `def ∀`.  Use
`unfold ParentAcyclic` (cross-module defs need the explicit unfold), then
`constructor` (the `apply` field) then `intro name; constructor` for `Acc`.

### Induction over a rank certificate (`≤`-indexed simple induction)

`Nat.strong_induction_on` is mathlib-only (core has `Nat.strongRecOn`).
Core-only pattern that keeps premises tight:

```lean
let P : Nat → Prop := fun n => ∀ q input, it.rank q ≤ n → <conclusion q input>
have hAll : ∀ n, P n := by
  intro n; induction n with
  | zero => intro q input hle; cases hrun : it.run q input with
    | halt _ => …
    | yield _ next => have hlt := it.next_lt hrun; omega   -- rank 0 cannot yield
    | raise _ => …
  | succ n ih => intro q input hle; cases hrun : it.run q input with
    | yield result next => have hrec := ih next result.state (by omega)  -- rank next ≤ n
    …
exact hAll (it.rank q) q input (Nat.le_refl (it.rank q))
```

Do not put the bound `n` inside the conclusion (the IH then only gives
`≤ n + 1`, but `1 + scf ≤ n + 1` needs `≤ n`); use the rank-parameterized
conclusion (`≤ it.rank q + 1`).

### Induction generalizing; case-pattern arity

When other hypotheses depend on the target list, the induction motive includes
them and the IH takes restricted copies in context order — bundle them into one
structure plus a `restrict` theorem so the IH takes exactly one extra
argument, or pass the copies explicitly (`ih (fun e' he' => hlawful e' (by
simp [he'])) …`).  In `with` patterns, implicit constructor binders count
toward the arity ("5 provided, but 3 expected"); for `Perm.swap` the induction
assigns `perm := x :: y :: l`, `maps := y :: x :: l` — let the goal's displayed
direction decide the relation order, don't guess `R.symm`.

## 7. Mathlib / core API gotchas

### `Finmap.insert` carries `[DecidableEq]` — `exact Finmap.lookup_insert` sticks

`exact Finmap.lookup_insert` on a goal `Finmap.lookup a (Finmap.insert a b s) = some b`
fails with `typeclass instance problem is stuck: DecidableEq ?m` even though the
goal's insert elaborated fine: elaborating the bare theorem constant with `a` as a
metavariable must elaborate `insert a b s`, which needs `[DecidableEq ?m]`.  `rw
[Finmap.lookup_insert]` works — the rewrite tactic elaborates the lemma against the
goal, pinning `a` first.  Same family as the instance-elaboration-order trap above.

### `Finmap.lookup_insert_of_ne` binder order

The actual signature: `{a a'} {b : β a} (s) (h : a' ≠ a) :
lookup a' (insert a b s) = lookup a' s` — the **queried key is `a'`**, the
inserted key is `a`.  To rewrite `lookup key (insert 10 1 ∅)`, pass the
hypothesis directly (`hkey : key ≠ 10`), not `Ne.symm hkey`.  `rw`'s argument
unification can still pick the wrong instantiation — pin with a `show`-wrapped
statement (or test in a scratch file first).  With *named* arguments the same
trap returns in a new shape: for the query `name` over `insert 1 …` use
`(a := 1) (a' := name)` — writing `(a := name) (a' := 1)` yields the premise
type `1 ≠ name` and an "Application type mismatch" against `hname : name ≠ 1`.

### `Option.ne_none_iff_exists` has the reversed `∃`

Core states `o ≠ none ↔ ∃ a, some a = o` — `rcases … .mp hneq with ⟨cell,
hcell⟩` gives `hcell : some cell = o`; use `hcell.symm` before `rw`.

### Finset empty/nonempty lemma names

`Finset.eq_empty_iff_forall_notMem` (capital M; no `not_mem` spelling) and
`Finset.nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅` exist; there is **no**
`Finset.mem_empty`/`not_mem_empty` theorem — `simp` closes `x ∈ ∅` goals
through the Multiset-level reduction anyway.

### `Finset.toList` needs `[LinearOrder α]`

For DecidableEq-only carriers, iterate via `Multiset`/`Finset.filter` forms
instead of `toList` (e.g. build views by `Multiset.map`/`filterMap` over
`Finmap.entries`, not `Finset.toList` folds).

### `Finset.insert` is not a constant

It is only the `Insert` typeclass instance: plain `insert a s` works; dot
notation (`s.insert a`) and `open Finset (insert)` fail.  A local `insert`
def shadows the notation — write `Insert.insert` in statements.  Finmap
exposes `keys_erase` but **no** `keys_insert` — prove `domain_insert` via
`Finset.ext` + `change j ∈ Finmap.insert k v s ↔ j ∈ Insert.insert k
(Finmap.keys s)` + `rw [Finmap.mem_insert, Finset.mem_insert, Finmap.mem_keys]`.

### `Finmap.ext_lookup` changes the goal head

After `apply Finmap.ext_lookup`, the goal head is `Finmap.lookup`, not the
wrapper `Coeffect.lookup` — prove the pointwise law **first** with the goal in
wrapper form, then apply `ext_lookup` and use the pointwise theorem.

### Nat / Bool arithmetic lemmas

`Nat.add_sub_cancel_right (n m) : (n + m) - m = n` exists in core
`Init/Data/Nat/Lemmas` but is **not** `[simp]` (the attribute sits on
`Nat.add_sub_cancel'`); `Nat.succ_sub_one : succ n - 1 = n := rfl`;
`Bool.not_not` closes `!(!b) = b` explicitly.

### `List.Perm` notation and module path

`~` is a scoped infix (write `List.Perm` explicitly, no `open scoped`);
`Mathlib/Data/List/Perm` is a directory — import
`Mathlib.Data.List.Perm.Basic`.  Use `pairwise_map` then `pairwise_iff_get`;
`List.Pairwise.imp` is unusable (implicit-lambda elaboration) — avoid it.

## 8. Semantic design gotchas

### Unprovable generic laws that read arbitrary data

A structure law like `landSound : … → landingWitness flight state` cannot be
proved for the toy instance when the witness was defined from an arbitrary
data-carried predicate — no premise makes it true for all flights.  This is a
semantic design bug, not a tactic issue: no proof exists.  Keep the
architecture, weaken only the toy instance (witness := `fun _ _ => True`
matching the toy's `admissible`), and record the repair.  Also: a clause like
`.unload` must clear what the target state claims (`traceMeta := []`), or the
finite witness is inconsistent.
