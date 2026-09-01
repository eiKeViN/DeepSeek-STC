# Lean 4 proof & declaration debugging — reusable lessons

Collected from the P0-P2 formatting sessions, P3-P4 partial/iterator, P6 alpha
transport, the ADR-07..10 spike repairs, P12 Scoped, and P13 T01/T02
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

### `Finmap.lookup_insert_of_ne` binder order

The actual signature: `{a a'} {b : β a} (s) (h : a' ≠ a) :
lookup a' (insert a b s) = lookup a' s` — the **queried key is `a'`**, the
inserted key is `a`.  To rewrite `lookup key (insert 10 1 ∅)`, pass the
hypothesis directly (`hkey : key ≠ 10`), not `Ne.symm hkey`.  `rw`'s argument
unification can still pick the wrong instantiation — pin with a `show`-wrapped
statement (or test in a scratch file first).

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
