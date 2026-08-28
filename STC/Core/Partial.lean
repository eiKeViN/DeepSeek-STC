module

public import STC.Core.Effect

/-!
# Partial operations and failure contracts

The explicit partial-operation layer: an `Option`-tagged carrier whose `none` is mathematical
undefinedness, plus the ADR-06 operation contracts, the D19-level independence predicate, and
the explicit bridges into the P1/P2 `Failure`/`ExecResult` carriers.  `Option` is never
converted into a failure diagnostic: the undefined branch reaches `ExecResult.failure` only
through an explicit handler that supplies error, boundary, and prefix undo.

## Main declarations

* `OpResult`, `PartialOp`, `PartialMap`, `pcomp`, `pcompOp`: the partial carriers;
* `DefinedAt`, `OpResultRel`, `opResultRelSpec`: definedness and the result relator;
* `WeakOperationRespects`, `OperationRespects`, `DefinednessStable`, `OutcomeStable`,
  `SelectedInverseCoherent`, `SelectedInverseStableOp`, `OperationRecovers`,
  `OperationForeignStability`: the ADR-06 operation contract family;
* `EffectIndependence`, `OperationIndependenceContract`: independence contracts;
* `opResultToEffectResult`, `opResultToExecSuccess`, `partialOpToExec`: failure bridges.
-/

universe u v w

namespace STC

variable {S : Type u} {A : Type v}

@[expose] public section

/-! ### The partial carriers -/

section PartialCarriers

/-- One successful partial application: the successor state, the selected inverse, and
the outcome payload. -/
structure OpResult (S : Type u) (A : Type v) where
  state : S
  undo : S → S
  outcome : A

/-- A partial operation: `none` is mathematical undefinedness, never a failure
diagnostic. -/
abbrev PartialOp (S : Type u) (A : Type v) := S → Option (OpResult S A)

/-- A partial map. -/
abbrev PartialMap (α : Type u) (β : Type v) := α → Option β

/-- Kleisli composition of partial maps. -/
def pcomp {α : Type u} {β : Type v} {γ : Type w}
    (f : PartialMap α β) (g : PartialMap β γ) : PartialMap α γ :=
  fun x => (f x).bind g

/-- The partial operation induced by a total effect: always defined, unit outcome. -/
def totalPartialOp (e : Effect S) : PartialOp S Unit :=
  fun input => some { state := (e input).state, undo := (e input).undo, outcome := () }

/-- Definedness of a partial operation at an input: the existence of a successful
result.  Stated with an explicit witness so that definedness consumers obtain the
selected result directly. -/
def DefinedAt (op : PartialOp S A) (input : S) : Prop :=
  ∃ r, op input = some r

/-- The full partial-result relator: related successor states, pointwise-related
selected inverses, and related outcomes. -/
def OpResultRel (R : RelSpec S) (O : A → A → Prop)
    (left right : OpResult S A) : Prop :=
  R.rel left.state right.state ∧ PointwiseRel R left.undo right.undo ∧
    O left.outcome right.outcome

/-- `OpResultRel` lifts two `RelSpec`s to a `RelSpec` on partial results. -/
def opResultRelSpec (R : RelSpec S) (T : RelSpec A) : RelSpec (OpResult S A) where
  rel := OpResultRel R T.rel
  refl := by
    intro result
    exact ⟨R.refl result.state, pointwiseRel_refl R result.undo,
      T.refl result.outcome⟩
  symm := by
    intro left right h
    exact ⟨R.symm h.1, pointwiseRel_symm h.2.1, T.symm h.2.2⟩
  trans := by
    intro left middle right h₁ h₂
    exact ⟨R.trans h₁.1 h₂.1, pointwiseRel_trans h₁.2.1 h₂.2.1,
      T.trans h₁.2.2 h₂.2.2⟩

/-- Sequential composition of partial operations: the second operation runs on the
first successor state, selected inverses compose in reverse execution order, and the
second outcome is retained. -/
def pcompOp (first : PartialOp S A) (second : PartialOp S A) : PartialOp S A :=
  fun input =>
    (first input).bind fun r =>
      (second r.state).map fun s =>
        { state := s.state, undo := r.undo ∘ s.undo, outcome := s.outcome }

end PartialCarriers

/-! ### The ADR-06 operation contracts -/

section OperationContracts

/-- The weak partial-result relation: related states and outcomes, without the
selected-inverse relator. -/
def WeakOpRel (R : RelSpec S) (O : A → A → Prop)
    (left right : OpResult S A) : Prop :=
  R.rel left.state right.state ∧ O left.outcome right.outcome

/-- Weak operation respect: related inputs yield related optional results modulo the
weak relation. -/
def WeakOperationRespects (R : RelSpec S) (O : A → A → Prop)
    (op : PartialOp S A) : Prop :=
  ∀ {x y}, R.rel x y → OptionRel (WeakOpRel R O) (op x) (op y)

/-- Full operation respect: related inputs yield related optional results with
related states, pointwise-related selected inverses, and related outcomes. -/
def OperationRespects (R : RelSpec S) (O : A → A → Prop)
    (op : PartialOp S A) : Prop :=
  ∀ {x y}, R.rel x y → OptionRel (OpResultRel R O) (op x) (op y)

/-- Common definedness on related inputs, in both directions.  Written as a
conjunction of implications rather than `↔`: the pinned Lean 4.33.0 toolchain
fails to elaborate `↔` in the codomain of a nested `∀` (verified on a minimal
`True ↔ True` example), so production statements avoid that shape. -/
def DefinednessStable (R : RelSpec S) (op : PartialOp S A) : Prop :=
  ∀ {x y}, R.rel x y →
    (DefinedAt op x → DefinedAt op y) ∧ (DefinedAt op y → DefinedAt op x)

/-- Outcome stability on related, defined inputs. -/
def OutcomeStable (R : RelSpec S) (O : A → A → Prop)
    (op : PartialOp S A) : Prop :=
  ∀ {x y}, R.rel x y → ∀ rl rr, op x = some rl → op y = some rr →
    O rl.outcome rr.outcome

/-- The selected inverses of related runs agree pointwise. -/
def SelectedInverseCoherent (R : RelSpec S) (op : PartialOp S A) : Prop :=
  ∀ {x y}, R.rel x y → ∀ rl rr, op x = some rl → op y = some rr →
    PointwiseRel R rl.undo rr.undo

/-- Every selected inverse preserves the relation. -/
def SelectedInverseStableOp (R : RelSpec S) (op : PartialOp S A) : Prop :=
  ∀ input r, op input = some r → Respects R r.undo

/-- Every defined run recovers its input up to the relation. -/
def OperationRecovers (R : RelSpec S) (op : PartialOp S A) : Prop :=
  ∀ input r, op input = some r → R.rel (r.undo r.state) input

/-- Foreign stability: the selected inverse commutes with a foreign map up to the
relation on related inputs. -/
def OperationForeignStability (R : RelSpec S) (op : PartialOp S A)
    (t : S → S) : Prop :=
  ∀ input r, op input = some r → CrossRel R (r.undo ∘ t) (t ∘ r.undo)

end OperationContracts

/-! ### Independence contracts -/

section Independence

/-- D19-level independence of two total effects: swapped execution orders agree as
related results with pointwise-related composed inverses. -/
def EffectIndependence (R : RelSpec S) (first second : Effect S) : Prop :=
  ∀ input, EffectResultRel R (seqRun first second input) (seqRun second first input)

/-- Pairwise independence of two partial operations: swapped orders agree on
definedness and on the full optional result relation. -/
structure OperationIndependenceContract (R : RelSpec S) (O : A → A → Prop)
    (first second : PartialOp S A) : Prop where
  definedness_stable : ∀ input,
    (DefinedAt (pcompOp first second) input → DefinedAt (pcompOp second first) input) ∧
      (DefinedAt (pcompOp second first) input → DefinedAt (pcompOp first second) input)
  swapped_related : ∀ input,
    OptionRel (OpResultRel R O) (pcompOp first second input)
      (pcompOp second first input)

end Independence

/-! ### Contract decomposition -/

section ContractDecomposition

/-- Full operation respect forces common definedness. -/
theorem operationRespects_definednessStable {R : RelSpec S} {O : A → A → Prop}
    {op : PartialOp S A} (h : OperationRespects R O op) :
    DefinednessStable R op := by
  intro x y hxy
  constructor
  · intro hx
    rcases hx with ⟨rx, hxr⟩
    have hrel := h hxy
    cases hyr : op y with
    | none => simp [OptionRel, hxr, hyr] at hrel
    | some ry => exact ⟨ry, hyr⟩
  · intro hy
    rcases hy with ⟨ry, hyr⟩
    have hrel := h hxy
    cases hxr : op x with
    | none => simp [OptionRel, hxr, hyr] at hrel
    | some rx => exact ⟨rx, hxr⟩

/-- Full operation respect forces outcome stability. -/
theorem operationRespects_outcomeStable {R : RelSpec S} {O : A → A → Prop}
    {op : PartialOp S A} (h : OperationRespects R O op) :
    OutcomeStable R O op := by
  intro x y hxy rl rr hx hy
  have hrel := h hxy
  simp [OptionRel, OpResultRel, hx, hy] at hrel
  exact hrel.2.2

/-- Full operation respect forces selected-inverse coherence. -/
theorem operationRespects_selectedInverseCoherent {R : RelSpec S}
    {O : A → A → Prop} {op : PartialOp S A} (h : OperationRespects R O op) :
    SelectedInverseCoherent R op := by
  intro x y hxy rl rr hx hy
  have hrel := h hxy
  simp [OptionRel, OpResultRel, hx, hy] at hrel
  exact hrel.2.1

/-- Kleisli composition of partial maps is associative. -/
theorem pcomp_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type w}
    (f : PartialMap α β) (g : PartialMap β γ) (h : PartialMap γ δ) :
    pcomp (pcomp f g) h = pcomp f (pcomp g h) := by
  funext x
  cases hfx : f x with
  | none => simp [pcomp, hfx]
  | some y =>
    cases hgy : g y with
    | none => simp [pcomp, hfx, hgy]
    | some z => simp [pcomp, hfx, hgy]

end ContractDecomposition

/-! ### Total-effect embeddings -/

section TotalEmbedding

/-- The total embedding of a lawful effect is a fully respecting partial operation. -/
theorem totalPartialOp_respects {R : RelSpec S} {e : Effect S}
    (h : IsLawfulEffect R e) :
    OperationRespects R (equality Unit).rel (totalPartialOp e) := by
  intro x y hxy
  have hrun : EffectResultRel R (e x) (e y) := h.run_respects hxy
  simp only [totalPartialOp, OptionRel, OpResultRel]
  exact ⟨hrun.1, hrun.2, rfl⟩

/-- The total embedding of a lawful effect recovers every input. -/
theorem totalPartialOp_recovers {R : RelSpec S} {e : Effect S}
    (h : IsLawfulEffect R e) :
    OperationRecovers R (totalPartialOp e) := by
  intro input r hr
  have : r = { state := (e input).state, undo := (e input).undo, outcome := () } := by
    simpa [totalPartialOp] using (Option.some.inj hr).symm
  subst r
  exact h.recovers input

/-- The total embedding of a lawful effect selects only relation-preserving inverses. -/
theorem totalPartialOp_stable {R : RelSpec S} {e : Effect S}
    (h : IsLawfulEffect R e) :
    SelectedInverseStableOp R (totalPartialOp e) := by
  intro input r hr
  cases hr
  exact h.undo_respects input

end TotalEmbedding

/-! ### Failure bridges -/

section FailureBridge

variable {E : Type w}

/-- Project a successful partial result onto the success-only effect carrier, erasing
the outcome payload. -/
def opResultToEffectResult (r : OpResult S A) : EffectResult S :=
  { state := r.state, undo := r.undo }

/-- Embed a successful partial result into the execution carrier via the explicit
success-only bridge. -/
def opResultToExecSuccess (r : OpResult S A) : ExecResult S E :=
  effectResultToExec (opResultToEffectResult r)

/-- Execute a partial operation into the execution carrier; the undefined branch is
resolved only by an explicit diagnostic handler supplying error, boundary, and prefix
undo.  A `none` alone never fabricates a failure. -/
def partialOpToExec (onNone : S → Failure S E) (op : PartialOp S A)
    (input : S) : ExecResult S E :=
  match op input with
  | none => .failure (onNone input)
  | some r => opResultToExecSuccess r

/-- A successful partial execution embeds the selected state and inverse. -/
theorem partialOpToExec_some (onNone : S → Failure S E) (op : PartialOp S A)
    (input : S) (r : OpResult S A) (h : op input = some r) :
    partialOpToExec onNone op input = .success (opResultToEffectResult r) := by
  simp [partialOpToExec, opResultToExecSuccess, effectResultToExec, h]

/-- An undefined partial execution returns exactly the handler's failure. -/
theorem partialOpToExec_none (onNone : S → Failure S E) (op : PartialOp S A)
    (input : S) (h : op input = none) :
    partialOpToExec onNone op input = .failure (onNone input) := by
  simp [partialOpToExec, h]

end FailureBridge

end

end STC
