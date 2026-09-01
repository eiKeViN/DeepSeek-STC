# Lean 4 proof & declaration debugging — reusable lessons

Collected from the P0-P2 formatting/fixing sessions and the P3-P4 partial/iterator
session (2026-08).  Each entry: symptom → root cause → fix.  Toolchain: Lean 4.33.0,
mathlib v4.33.0.

## Verification discipline

### CLI checks must replicate project options

Symptom: file compiles clean under `lake env lean <file>`, IDE reports unknown-identifier
errors.

Root cause: `lake env lean` does **not** read lakefile `[leanOptions]`; with the default
`autoImplicit := true`, undeclared identifiers silently auto-bind as implicit parameters
and the file "compiles".

Fix: always `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true <file>` (mirror of
the lakefile options).  Check single files only after `lake build` produced fresh oleans
for their imports (module-system files refuse stale non-`module` imports).

### Fix errors in priority order, one step at a time

Syntax errors → type errors → unsolved goals/tactic failures → linter warnings.  Unsolved
goals are reported on the `by`/`=>` line, not at the offending tactic.  Higher-priority
errors make lower ones unreliable; a cascade (dozens of "Invalid field notation", `sorry`
placeholders) usually collapses to one root cause.

## Module system (Lean 4.33)

### `Not a definitional equality: the left-hand side`

Symptom: `theorem t : (f x).1 = x.1 := rfl` fails in a `module` file.

Root cause: exported (public) theorems may only unfold *exposed* definitions; plain
`public section` marks declarations public but not exposed.

Fix: wrap declarations in `@[expose] public section … end` (mathlib's universal form).
Minimal repro confirms: same theorem + `public section` fails, + `@[expose] public
section` passes.

### `Unknown identifier` for an imported declaration

Root cause: in `module` files declarations default to **private**; only `public section`
(plus exposure) exports them.

### `cannot import non-module X from module`

Root cause: stale pre-`module` oleans in the build dir.  `lake build` the dependency
chain first.

### `#eval` over exposed declarations fails on Windows

Symptom: `Could not find native implementation of external declaration '…._redArg'`.

Root cause: `@[expose]` extern-izes declarations; the interpreter demands compiled native
symbols.  The package shared library cannot be linked on Windows (PE export cap 65,535;
mathlib exports ~203k → `Mathlib:shared` fails: `ld.lld: too many exported symbols`).
`supportInterpreter` exists only on `lean_exe` configs (silently ignored under
`[[lean_lib]]`); `precompileModules = true` pulls the dependency's shared library and
fails the same way.

Fix: no top-level `#eval` over exposed declarations in library modules; pin executable
checks with `example report = { … } := by decide` (runs the same computation at
elaboration).  Full write-up: `docs/status/eval-exposed-decls-debug-report.md`.

## Typeclass & decidability

### `Decidable` synthesis through a `def` fails

Symptom: `decide (SatisfiesExec σ d)` / `if SatisfiesExec …` fails with
`failed to synthesize Decidable (SatisfiesExec σ d)` even though `[DecidableEq K]` is in
scope.

Root cause: TC synthesis does not unfold the `def`; mathlib's
`instDecidableRelSubset [DecidableEq]` matches only the unfolded `d ⊆ σ.keys`.

Fix: a one-line instance that documents the contract:

```lean
instance instDecidableSatisfiesExec (σ : Store V) (d : ExecSpec K) :
    Decidable (SatisfiesExec σ d) := by
  dsimp [SatisfiesExec]
  infer_instance
```

### `unusedSectionVars` linter: auto-included-but-unused instance

Symptom: warning "automatically included section variable(s) unused in theorem X:
[DecidableEq K]".

Root cause: Lean auto-includes section variables it considers used (often through a
hidden instance parameter of a mentioned def); the linter disagrees.

Fix: `omit [DecidableEq K] in theorem …` **when the statement is genuinely
instance-free** (check with `#check @theorem` after).  If the statement truly needs the
instance (it appears through a def's hidden param), keep it and accept the warning or
declare the binder explicitly in the declaration — explicit binders are not linted.

## Tactic-level pitfalls

### `simp` won't unfold match-definitions unless listed

Symptom: `simp made no progress` (×N, one per goal branch) on goals containing a
match-defined predicate.

Root cause: equation lemmas of match-defs are not `@[simp]` by default; plain `simp`
never unfolds `OptionRel`.

Fix: `simp [OptionRel] at h ⊢` — list the def explicitly.

### `subst` cannot see equalities inside composite hypotheses

Symptom: `subst out₂` fails with "did not find equation for eliminating 'out₂'" though
`hrs : A ∧ B ∧ out₁ = out₂` is in context.

Root cause: `subst` only reads top-level equality hypotheses.

Fix: extract first: `have hout : out₁ = out₂ := hrs.2.2` then `subst out₂`.

### `match h : …` binder used only in `decreasing_by`

Symptom: linter "Variable name `h` is not explicitly referenced" on a recursive
`match h : it.run q γ with`.

Fix: rename to `_h` (both in the match and in `decreasing_by exact it.next_lt _h`).

### Trivial-goal leftovers after `<;>` case splits

Pattern that works: `cases a <;> cases b <;> cases c <;> simp [Pred] at hab hbc ⊢` closes
every branch except the single nontrivial one; the remaining goal then takes the direct
proof (`exact htrans hab hbc`).  A bare `exact htrans` after the split fails with
`expected True → True → True` — the first remaining goal is a trivial branch, not the
interesting one.

### Unused simp arguments are safe to remove

Linter `unusedSimpArgs` lists exactly which arguments `simp` did not need; removing them
never breaks the proof.  Same for the `Try simp at hc instead of simpa using hc` advice.

### Constructor-resemblance warnings

Local binders named like constructors in scope (`intro a b hab` next to `Toy.a`/`Toy.b`)
trigger the linter; rename the binders (`intro x y hxy`).

## Lean 4.33 keyword & universe traps

### New reserved keywords break old binders

Symptom: `unexpected token 'local'; expected '=>'` (and a parse-error cascade).

Root cause: `local` and `prefix` became reserved keywords; old spike files use them as
binder names.

Fix: rename binders (`localVal`, `prefixUndo`).  Grep any imported legacy file for
`\blocal\b`, `\bprefix\b`, `\bmatch\b` used as identifiers.

### Universe linter on structures

Symptom: "universes `w`, `x`, `y` only occur together" on a structure with
`Op : K → Type w`, `Arg : (k : K) → Op k → Type x`, `Out : (k : K) → Op k → Type y`.

Fix: collapse the field universes to one (`Type w` everywhere) and drop the unused
universe declaration.

## Section/notation scoping

- Local notations are **scoped** to their section — a notation used by several sections
  must be declared outside them (fails as `Unknown identifier` + autoImplicit errors
  under project options).
- Section variables are auto-included only when used; `#check @decl` after refactoring
  catches unintended signature drift (dropped/added instance params).
- Type-family declarations (`Store (V : K → Type v)`, `PartialMap (α) (β)`) keep their
  explicit parameters even when the same names are section variables (shadowing is
  legal and preserves the API).

## Lean 4.33.0 elaboration regressions (P3/P4 session)

These are toolchain-level: minimal repros fail with the pinned `v4.33.0` binary alone
(no imports, no lake env), so they are not caused by project conventions.

### `↔` in a nested `∀` fails to elaborate

Symptom: on a goal of shape `∀ {x y}, R.rel x y → (Q ↔ R)`, `intro x y hxy` fails with
"`introN` failed: There are no additional binders"; term-mode (`fun {x y} hxy => …`)
fails with "Type mismatch" and metavar-typed binders.  Even `∀ {x y}, R x y → True ↔
True` fails.  The arrow body (`Q → R`) and the paired-arrow form both elaborate fine.

Workaround: write the paired-arrow form `(Q → R) ∧ (R → Q)` in **definition
statements** (the poison is in statement elaboration, so it lands on every downstream
consumer).  Top-level `↔` goals are fine (`constructor`, `Iff.intro`).  Applied in
`STC/Core/Partial.lean` (`DefinednessStable`, `OperationIndependenceContract`) with a
docstring note.  Consider reporting upstream / re-testing on v4.33.1.

### Proposition evaluation is stuck: `decide (¬ P)`, `if h : P`, `match P with`

Symptom: `decide (¬ StageRelC … (.halt …) (.raise …))` reports "typeclass instance
problem is stuck" / "failed to synthesize"; `match P with | True => … | False => …`
reports "redundant alternative" and won't reduce — even though `P` reduces to `False`
(and `rfl` on a bare `P → False` proof works).

Fix: don't evaluate propositions — compute on the **data**: a `Bool`-valued constructor
match over the concrete values (`match (.halt r), (.raise e) with | .halt _, .halt _ =>
false | … | _, _ => true`), and keep the semantic statement as a `K`-level theorem
(`¬ StageRelC …` by `intro h; cases h`) beside it.  Same pairing used for the
reflexivity check (`execSuccess_refl` theorem + constructor-match `Bool`).

### `simp only []` does not reduce closed `if c` conditions

Symptom: `simp only []` on `(if (3 : Nat) = 0 then 1 else 2) = 2` reports "made no
progress"; the `if` stays stuck even though `rfl` and `decide` reduce it.

Fix: when a chain needs such a reduction, use `rw [show … = … from rfl]` with explicit
equalities (rfl-level defeq does reduce closed decidables), or `decide` for the whole
closed goal.

### WF-recursive (`termination_by`) defs: unfold/rw/decide behavior

- `rw [def]` → "Invalid rewrite argument" (no rw-usable equation).
- `simp [def]` → infinite loop ("Possibly looping simp theorem `def.eq_1`", recursion
  depth exceeded).
- `unfold def` → works; after it, `simp only [h]` on the `match _hrun :` scrutinee
  makes **no progress** (motive binder), while `rw [h]` rewrites it — and `rw` closes
  the goal itself when the result is `rfl`.
- Several `rw` rules in one call do **not** iota-reduce between rules (the match keeps
  its `result_1`/`next_1` names, so the second rule's LHS doesn't match).  Split with
  `simp only []` between dependent rewrites:
  `unfold execFrom; rw [hyield]; simp only []; rw [hinner]`.
- `rw [thm (hyield := by rfl)]` with a metavariable premise fails to elaborate the
  premise — supply the hypothesis explicitly: `(hyield := (show counterIterator.run …
  = .yield … from rfl))`.
- `rw` over a theorem with an uninstantiated premise puts the **main goal first**,
  premise goals after: use `pick_goal 2` to discharge the premise first, or chain
  bottom-up per-stage theorems (`execCount0 → execCount1 → …`), one `rw` + one
  `pick_goal 2` + `exact prev` each.
- **The kernel cannot reduce a WF-fix in `decide`**: `example : report = … := by
  decide` gets stuck at "did not reduce to `isTrue` or `isFalse`" over `execFrom`.
  Pin executable evidence with **equation theorems** instead: prove
  `execFrom … = .success {…}` by the rw-chain above, then `unfold field; rw [trace_eq]`
  in the report pinning (`rw` then `rfl` — `rw` often discharges the goal itself, so a
  trailing `rfl` may error "No goals to be solved").

### Structure-literal projections reduce asymmetrically

Symptom: `exact hs.2` / `simpa using ⟨hrel, hst, …⟩` fail with "Type mismatch" where
the term's type is already the unfolded form but the expected type still shows
`{ error := …, boundary := …, prefixUndo := … }.prefixUndo` (or `Respects R {..}.undo`)
unreduced.

Fixes that worked, in order of preference:
- `cases hr` on `op input = some r` (or `cases h` on a stage equality) substitutes the
  record **definitionally**, avoiding projection reduction entirely;
- `change <fully unfolded form>` before `exact` (`change ∀ {x y}, R.rel x y → R.rel
  (f x) (f y); exact hs.2` for `Respects` goals);
- annotate tuples with the **unfolded** type instead of a record literal
  (`: R.rel l.state r.state ∧ PointwiseRel R (u ∘ v) (u' ∘ v')` rather than
  `: EffectResultRel R {…} {…}`), and add the relator to the `only` set
  (`simpa only [ExecRel, FailureRel] using …` — the goal side needs `FailureRel`
  unfolded even when the term side doesn't).
- `Option.some.inj hr` returns `{…} = r`; for `subst`/`rw` you need the other
  direction: `(Option.some.inj hr).symm`.
- Multi-line record literals with field projections (`{ error := f.error, boundary :=
  f.boundary, … }`) hit parser errors ("unexpected identifier; expected '}'") in some
  contexts; the anonymous constructor `⟨f.error, f.boundary, …⟩` parses everywhere —
  prefer it, and don't name a local binder after a constructor (`.failure failure`).

### Induction over a rank certificate: `≤`-indexed simple induction

`Nat.strong_induction_on` is **mathlib-only** in this build (core has
`Nat.strongRecOn`).  Core-only pattern that also keeps premises tight:

```lean
let P : Nat → Prop := fun n => ∀ q input, it.rank q ≤ n → <conclusion q input>
have hAll : ∀ n, P n := by
  intro n; induction n with
  | zero => intro q input hle; cases hrun : it.run q input with
    | halt _ => …
    | raise _ => …
    | yield _ next => have hlt := it.next_lt hrun; omega   -- rank 0 cannot yield
  | succ n ih => intro q input hle; cases hrun : it.run q input with
    | yield result next => have hrec := ih next result.state (by omega)  -- rank next ≤ n
    …
exact hAll (it.rank q) q input (Nat.le_refl (it.rank q))
```

Do not put the bound `n` inside the conclusion (`stageCountFrom … ≤ n + 1` fails in
the succ step: the IH then only gives `≤ n + 1`, but `1 + scf ≤ n + 1` needs `≤ n`);
use the rank-parameterized conclusion (`≤ it.rank q + 1`) instead.

### omega needs the defs unfolded

`omega` does not unfold definitions: `ext <;> omega` on `(inc1 input).undo (inc1
input).state = input` fails with a counterexample that mentions the raw `inc1` terms.
Fix: `ext <;> simp [inc1] <;> omega` (also inside `⟨by ext <;> omega, …⟩` tuples).

### Decidable over infinite carriers

`unfold ExecRel EffectResultRel PointwiseRel; infer_instance` fails for
`(equality CounterState)` with `CounterState = Nat × Nat`: the pointwise `∀ x, …` over
an infinite carrier has no `Decidable`.  Finite carriers (`Fin n` + Fintype imports)
work.  For concrete instances construct the instance directly:
`exact isTrue (by constructor <;> …)` / `exact isFalse (by intro h; cases h)` — or
prefer the data-level `Bool` checks (see above).

## Experiment-first debugging discipline (P3/P4)

- **Check which binary actually ran.**  `lean`/`lake` invoked from outside the repo
  resolve elan's *default* toolchain — in this environment v4.33.1 (uninstalled;
  downloads blocked), not the repo-pinned v4.33.0.  Minimal repros "passing" from
  `/tmp` were silently testing the wrong toolchain.  Always run repros with
  `lake env lean` from the repo root (pinned toolchain + LEAN_PATH), or the pinned
  binary path directly.
- Bisect a repro into factors (import / namespace / def shape / tactic) — one factor
  per test file; a single batch of variants per compile cycle beats sequential
  theorizing (each compile is seconds).
- The IDE diagnostics can be stale across edits; trust a fresh `lake build` /
  `lake env lean` output.

## Mathlib lookup habits

- Grep the pinned mathlib sources (`.lake/packages/mathlib/Mathlib/…`) for lemma/instance
  names instead of guessing: `Finmap.mem_keys`, `Finmap.mem_insert`,
  `Finmap.lookup_insert_of_ne`, `Finmap.lookup_erase_ne`, `Finmap.lookup_isSome`,
  `Finset.disjoint_left.mp`, `instDecidableRelSubset` (Finset/Defs), `Equiv.Perm`
  (Logic/Equiv/Defs — needs `import Mathlib.Logic.Equiv.Defs`, Std alone lacks it).
- `lake env lean` on a copy of a file with `#check @decl` lines appended is the fastest
  way to inspect elaborated signatures after a refactor.

## P6 alpha transport & ADR 07-10 spike repair (2026-08-28)

Lessons from writing `STC/Alpha/*` and from fixing the four failing ADR-07..10
standalone spikes.  Toolchain unchanged (Lean 4.33.0, mathlib v4.33.0).

### Typeclass search does not unfold compound predicate `def`s

Symptom: `Decidable (AllocationAllowed …)` (a `def` over a conjunction of decidable
components) fails to synthesize; the trace shows only unrelated candidate instances.

Root cause: instance search never delta-reduces the compound `def`, so no
`instDecidableAnd`/`Finset.decidableMem` candidate matches.

Fix (two recipes):
- For `if`/`by_cases` guards in executable defs, write the condition syntactically
  unfolded (`if n ∉ current ∧ n ∉ ledger.everIssued ∧ …`); keep the compound `def`
  for theorem statements.
- For `decide`-checked Props, declare a bridge instance:
  `instance … : Decidable (SupportRel s a b) := by unfold SupportRel Precedes
  ParentEdge; infer_instance` (ADR-09 spike).

### Structure instance params must precede dependent parameters

Symptom: `synthesized type class instance is not definitionally equal to expression
inferred by typing rules` on every field of a structure literal.

Root cause: `structure FlatEmbedding (M) (Flat Scoped) (ops : RealmStoreOps M Scoped)
(ρ : Resolver M)` where `Resolver M` carries `[DecidableEq K]`.  The `ρ` parameter's
type is elaborated with the *section* instance, while the fields elaborate with the
*auto-included structure* instance — two distinct local constants, not defeq.

Fix: put instance params first: `(Flat Scoped : Type x) [DecidableEq K] (ops) (ρ)`.
Same trap as a trailing `[DecidableEq K]` after dependent params — reordering is the fix.

### Unprovable generic laws that read arbitrary data

Symptom: a structure law like `landSound : … → landingWitness flight state` cannot be
proved for the toy instance.

Root cause: the witness was defined from an arbitrary data-carried predicate
(`flight.landingWitness.admissible state.raw`); no premise makes it true for all
flights.  This is a semantic design bug, not a tactic issue — no proof exists.

Fix: keep the architecture, weaken only the toy instance (witness := `fun _ _ => True`,
matching the toy's `admissible := fun _ => True` flights) — and record the repair.
Also: a clause like `.unload` must clear what the target state claims
(`traceMeta := []`), or the finite witness is inconsistent.

### Reserved identifiers: `meta`, `at`, `not`

Symptom: parse errors `unexpected token 'meta'` / `unexpected token 'at'`; `not P`
elaborates as an unknown identifier.

Root cause: `meta` is a Lean keyword; `at` is a reserved token (both unusable as field/
parameter names); `not` is Coq syntax, Lean uses `¬`/`Not`.

Fix: rename fields (`meta` → `metadata`, `at` → `atKey` with a docstring note),
`not P` → `¬ P`.

### Imports must precede `/-!` doc headers

Symptom: `invalid 'import' command, it must be used in the beginning of the file` —
the import sits *after* a `/-! … -/` module doc block (ADR-10 spike).

Fix: `import` lines first, then the doc block, then `set_option`s.  Related: `omit
[X] in` and `set_option … in` must also precede the *docstring* of the declaration
(the doc comment attaches to the next declaration; `omit` is not one →
`unexpected token 'omit'; expected 'lemma'`).

### Multi-line `{ field := … }` literals in theorem statements

Symptom: `unexpected identifier; expected '}'` on a two-line structure literal in a
theorem statement (single-line form compiles).

Root cause: after `=`, a multi-line `{…}` is ambiguous with a binder block.

Fix: one line, or an ascribed intermediate def (`(.success {…} : ExecResult S E)`).

### `cases` / `subst` context pitfalls

- `cases h : e with` *generalizes goal occurrences of `e`* — afterwards `rw [h]` on
  the goal fails ("pattern not found"); drop the redundant rw (ADR-08).
- `cases p0` **clears `p0`** — in the branch use the branch binder
  (`h.parents (some n0) hp0 n0 rfl`).
- `subst x` where hypotheses depend on `x` can silently eat rcases-bound context
  (later `unknown identifier` cascades).  Prefer `rw [← hEq] at hn` and
  `simp […, ← hEq]` over `subst` in that situation.

### Match-def equations don't fire on free-variable sub-patterns

Symptom: `simp [toyLifecycle, …] at hstep` leaves the whole `match` for the
`.divert owner choice` case, where `choice` is a variable.

Root cause: the def's equations for `.divert .abort`/`.divert .land` require
constructor scrutinees; a free variable matches neither, so the unfolded match stays.

Fix: `cases choice` first, then `simp … at hstep` per constructor
(ADR-07 toyTerminal_has_no_lifecycle_successor).

### `simp at h` over a def-application hypothesis

Symptom: `simp at h` errors "made no progress" for `h : toyBaseOrch .retire .inactive
.inactive`.

Root cause: `h`'s type is a *structure projection* (`toyModel.baseOrch …`); the set
must unfold both the record (`toyModel`) and the underlying def (`toyBaseOrch`).

Fix: `simp [toyModel, toyBaseOrch] at h` — constructor-inequality conjuncts
(`.inactive = .active`) then reduce to `False` and close the goal.

### `rfl` / `grind only` over closed `if`s

`simp only [defs]` leaves `(if r = r then some v else s r)` intact; `rfl` reduces it
through the `Decidable` instance (`isTrue rfl`) — but only when the scrutinee is not
a variable.  For store-law goals with hypotheses (`q ≠ r`), the ADR-10 spike pattern
is `simp only [toyLookup, toyInsert]` then `grind only` (or `by_cases`).  Dead `omega`
after a closing `simp` chain triggers `unusedTactic`/`unreachableTactic` — remove.

### Dot-notation `.mp` needs the explicit argument first

`Equiv.apply_eq_iff_eq.mp` fails ("unknown constant") because the theorem's first
parameter `(f : α ≃ β)` is explicit; write
`(Equiv.apply_eq_iff_eq (χ : Equiv.Perm N)).mp (…)`.

### `Finset.insert` is not a constant

It is only the `Insert` typeclass instance: plain `insert a s` works; dot notation
(`s.insert a`) and `open Finset (insert)` both fail ("environment does not contain
`Finset.insert`").  Same family: `Finset.decidableNonempty`, `Finset.mem_map_equiv`
(simp), `List.pairwise_map`/`pairwise_iff_get` (`Mathlib.Data.List.Pairwise`;
apply `iff_get` *after* `pairwise_map` so both sides range over the same list and the
`Fin` index types line up).  `List.Pairwise.imp` is unusable (implicit-lambda
elaboration); avoid it.

### Explicit `Q`/`V` annotations for under-determined implicit params

Symptom: `don't know how to synthesize implicit argument V/Q` in a theorem statement
whose def (`raiseLabel owner (… : ExecResult S E)`) cannot pin implicit carrier params.

Fix: annotate at the call site: `raiseLabel (Q := Q) (V := V) owner …`; similarly
`(.inactive : ToyBase) = .active` when the disjunct alone cannot determine the type.

### Process

- `lake env lean` must run from the **repo root**; from a subdirectory (no lakefile)
  it degrades to a bare elan env → `unknown module prefix 'Mathlib'` — a false
  diagnostic that looks like a file defect (ADR 07-10 first pass).
- Spike-repair hygiene: keep the architecture, fix only what the compiler forces;
  record semantic repairs (unload-clears-traceMeta, trivially-true landing witness,
  `at`→`atKey`) explicitly for review; re-check every spike for **zero** warnings
  (incl. `defProposition`: proposition-valued `def` → `theorem`).

## P12 Scoped & P13 T01 sessions (2026-08-29..09-01)

### `autoImplicit=false` breaks membership-∀ `fun` binders in argument positions

Symptom: `fun m hm => …` against `∀ m ∈ l, P m` mis-elaborates `hm : S`
(the element type) instead of `hm : m ∈ l` — but only in SOME positions:
plain theorem statements and `have h : ∀ m ∈ l, …` annotations elaborate
fine, while fun-arguments to applications and structure-literal fields fail.

Root cause: with `autoImplicit=false`, the auto-bound-implicit inference the
membership-binder relies on is fragile in dependent positions.

Fix: in NEW declarations, write the expanded form `∀ (m : T), m ∈ l → P m`
and always annotate binders explicitly: `fun (m : T) (hm : m ∈ l) => …`;
`intro (e' : Effect S) (he' : e' ∈ rest)`.

### Instance arguments elaborate before later explicit args pin type parameters

Symptom: `resolverUpdate_hit defaultResolver .dep toyDepBRef` fails with
"cannot synthesize DecidableEq (RealmModel.Realm ?m)" even though the last
argument pins `M := toyModel`.

Root cause: a theorem's implicit typeclass args are synthesized left-to-right
before the later explicit args unify the type parameters.

Fix: pin the type with the FIRST explicit argument (use `depBResolver` as ρ),
or pass named args `(K := ToyKey) (M := toyModel)`, or define pinned wrapper
defs (`toyResolverUpdateOps : ResolverUpdate toyModel := defaultResolverUpdate`)
and use those in example statements.

### Cross-module `simp` cannot use P5 wrapper lemmas; `rw`/`exact` can

Symptom: `simp only [Coeffect.coeffect_lookup_erase]` on a goal whose head is
`Coeffect.lookup` reports "made no progress"/unused, while
`rw [Coeffect.coeffect_lookup_erase]` and `exact` work fine cross-module.

Root cause: simp's preprocessing normalizes the lemma LHS but not the goal
subterm heads the same way for these def-wrapped store operations
(`Coeffect.lookup`/`insert`/`erase` vs `Finmap.*`); the matcher then fails.

Fix: use `rw`/`exact` for the P5 wrapper lemmas (`coeffect_lookup_*`); direct
Mathlib `Finmap.lookup_*` lemmas work inside `simp` after `change`/`unfold` to
the `Finmap.*` form.  Same head-mismatch applies to `Finmap.mem_insert` vs a
goal written with `Coeffect.insert`: `change` the goal to `Finmap.insert` first.

### `Finmap.ext_lookup` changes the goal head

Symptom: after `apply Finmap.ext_lookup`, P5 lemmas stop matching even via
`rw` (the earlier wrapper trick fails).

Root cause: `ext_lookup`'s conclusion is `Finmap.lookup x s₁ = Finmap.lookup x
s₂` — the goal head is now `Finmap.lookup`, not `Coeffect.lookup`.

Fix: prove the pointwise law FIRST with the goal in `Coeffect.lookup` form
(the wrapper heads match), then apply `Finmap.ext_lookup` and use the
pointwise theorem.

### `change` does not unfold regular `def`s; `rfl` does

Symptom: `change ToyRealm.depB = ToyRealm.depB` fails on goal
`depBRef.token = ToyRealm.depB`.

Root cause: `change` checks defeq at reducible transparency; semireducible
defs (toy model projections, resolver wrappers) don't unfold.

Fix: for closed-def equalities just use `rfl` (the kernel unfolds everything
semireducible); reserve `change` for projection-of-literal / dite reductions.
Structure literals inside `change` targets need type ascriptions
(`({ state := …, undo := …, outcome := () } : OpResult (Store …) Unit)`), else
"invalid {...} notation, expected type is not known".

### `rcases hlook : e with …` rewrites the motive — do not re-`rw`

Symptom: in a branch of `rcases hlook : lookup k store with _ | value`, the
obligation `∀ v, lookup k store = some v → P v` arrives with `lookup k store`
ALREADY replaced by the branch shape (`hv : none = some v`, or
`hall` expecting `some value = some value`).

Root cause: `rcases` with a named equation generalizes the scrutinee in the
motive (an `Option.casesOn` with a `lookup k store = x` motive), substituting
the branch variable before the branch proof runs.

Fix: in the `none` branch, `cases hv` directly (no `rw [hlook]`); in the
`some` branch, close the `hall` side with `apply hall; rfl` and prove the
forward direction with `Option.some.inj hv` (no `simpa [hlook]`).

### `unfold … at h` leaves beta-redexes; `simp [def, hyp] at h` is more robust

Symptom: after `unfold liftProvide at h`, `rw [insert_erase_restore …]` finds
no occurrence; the hypothesis still shows `(fun store => …) store = some r`.

Root cause: `unfold` substitutes the def body but does not beta-reduce the
application or the dite/match in `h`; `rw`/`split` then see unreduced terms.

Fix: put the def in the simp set instead: `by_cases hnone : …` then
`simp [liftProvide, hnone] at h` — it unfolds, beta-reduces, reduces the
dite/match, and closes contradiction branches.  `split at h` also works for
dites and names the branch premises `h_1`/`h_2` — avoid relying on those
auto-names; prefer `by_cases` with an explicit name.

### `simp only [lemmas]` excludes the default simp set

Symptom: `simp only [liftKeyLocal, hlook, hnew] at h` leaves
`none = some r` and `Option.map f none` unreduced — goals that plain
`simp [..]` closes by no-confusion/map reduction.

Root cause: `simp only` uses exactly the listed lemmas; the built-in
no-confusion and `Option.map_some`/`map_none` reductions live in the default
set and are dropped.

Fix: prefer plain `simp [defs, hyps]`; use `simp only` only when the target
form is fully known.  (Related: `rw` closes goals that become `rfl` — a
trailing `rfl` after such `rw` is an orphan "No goals to be solved".)

### Induction where other hypotheses depend on the target list

Symptom: `induction effects generalizing input with | cons e rest ih => …`
gives an IH whose leading arguments are restricted copies of EVERY context
hypothesis whose type mentions `effects` (`∀ (hlawful' : ∀ e ∈ rest, …)`,
`∀ (hcomm' : …)`, …); wrong arg orders produce baffling
"expected `m ∈ rest → …`" mismatches.

Root cause: the induction motive includes all target-dependent context
hypotheses, so the IH generalizes them too (in context order).

Fix: (a) bundle such hypotheses into one structure —
`structure InverseWordLaw … where respects …; commutes …` plus a
`restrict` theorem — so the IH takes exactly one extra argument; (b) pass the
restricted copies explicitly:
`ih (fun e' he' => hlawful e' (by simp [he'])) …`; (c) the `trans` case of a
`List.Perm` induction restricts via `h₂₃.subset` (`List.Perm.subset`:
`l₁ ~ l₂ → l₁ ⊆ l₂`); the `swap` case's map side is the constructor's own
list (`x ∈ y :: x :: l` by `simp`).

### Induction case-pattern arity and constructor sides

Symptom: `induction hperm generalizing s with | cons m l₁ l₂ h₁₂ ih => …`
reports "5 provided, but 3 expected"; later the swap case's goal needs
`R.rel (x (y s)) (y (x s))` (the opposite of the naive direction).

Root cause: implicit constructor binders are nameable in `with` patterns and
count toward the arity (`| cons m h₁₂ ih` — the sublists are inaccessibles);
in `Perm.swap` the induction assigns `perm := x :: y :: l`,
`maps := y :: x :: l`, so the goal order follows that assignment.

Fix: count only constructor args + IH; let the goal's displayed direction
decide `hxy` (no guessing `R.symm`).

### List.Perm notation and module layout (mathlib 4.33)

Symptom: `(hperm : perm ~ maps)` fails to parse ("unexpected token '~'");
`import Mathlib.Data.List.Perm` says the module does not exist.

Root cause: `~` is a SCOPED infix (`scoped infixl:50 " ~ " => Perm` in core
`Init/Data/List/Basic`); `Mathlib/Data/List/Perm` is a directory — the module
is `Mathlib.Data.List.Perm.Basic` (re-exports `Batteries.Data.List.Perm`).

Fix: write `List.Perm` explicitly (no `open scoped` dependency), import
`Mathlib.Data.List.Perm.Basic`.

### Nat successor-subtraction lemmas (core 4.33)

Symptom: `simp` does not close `(input.1 + 1) - 1 = input.1`.

Root cause: `Nat.add_sub_cancel_right (n m) : (n + m) - m = n` exists in core
`Init/Data/Nat/Lemmas` but is NOT `[simp]` there (the attribute sits on
`Nat.add_sub_cancel'`); `Nat.succ_sub_one : succ n - 1 = n := rfl`.

Fix: `exact Nat.add_sub_cancel_right input.1 1` (or `Nat.succ_sub_one` for the
`succ` spelling); `Bool.not_not` likewise closes `!(!b) = b` explicitly.

### Finmap domain laws and the `Insert.insert` shadowing

Symptom: `Finmap.keys_insert` does not exist; in `namespace STC.Coeffect`,
`insert k (Domain store)` in a theorem statement resolves to the LOCAL
store-`insert` def and the statement becomes ill-typed.

Root cause: Finmap exposes `keys_erase` but no `keys_insert`; `insert` is an
`Insert` typeclass notation, shadowed by the local `Coeffect.insert` constant.

Fix: prove `domain_insert` via `Finset.ext` + `change j ∈ Finmap.insert k v s
↔ j ∈ Insert.insert k (Finmap.keys s)` + `rw [Finmap.mem_insert,
Finset.mem_insert, Finmap.mem_keys]`; write `Insert.insert` in statements.

### Decidability carriers: prefer `abbrev` + `decidable_of_iff` arg order

Symptom: `decide (x = y)` where `x : toyModel.Realm` fails to synthesize
`Decidable`; `decide (declaredSatisfied d store)` fails although the Finset-∀
instance exists.

Root cause: instance synthesis runs at `.instances` transparency, which does
NOT unfold regular `def`s — `toyModel.Realm` / `declaredSatisfied` stay stuck.
(Extends the existing "Decidable synthesis through a def fails" entry with the
`decide`/abbrev corollary.)

Fix: make decidability-relevant carriers `abbrev` (`toyModel`, `ToyValue`,
`ToyFlatModel`, `declaredSatisfied`); for token equality in reports use a
comparison function over the reduced type
(`toyTokenEq (a b : ToyRealm) : Bool := decide (a = b)`).  Note the core
signature `decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b`
— the plain Prop comes first.

### `new` and `local` are keywords

Symptom: parse errors ("unexpected token 'local'") on binder
`(local : V k → Option (V k))`; unknown identifier `new` when the map-lambda
binder was renamed inconsistently.

Root cause: `new` and `local` are Lean modifier keywords (add to the existing
`meta`/`at`/`not` list); `local` fails at parse, `new` at elaboration.

Fix: rename to `localOp`/`newVal` — rename the lambda binder AND all its body
uses in one pass.

### Lake: default target vs explicit module targets; IDE diagnostics are stale

Symptom: `lake build` reports the old job count and never builds new modules;
IDE diagnostics disagree with `lake build` output.

Root cause: `defaultTargets = ["STC"]` builds only the `STC.lean` import
closure; modules not yet imported by `STC/Bootstrap.lean` are absent.  IDE
diagnostics lag edits and show cascades from superseded errors.

Fix: build new modules with explicit targets
(`lake build STC.Core.Coeffect STC.Examples.PrerequisiteCoeffect`); treat
`lake build <target>` output (not the IDE pane) as the authoritative error
list; per-file `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true`
after the oleans exist catches linter warnings.
