module

public import STC.Foundation.Relation

/-!
# Result carriers and their relations

Raw result carriers retain the selected state and every inverse field.  `ExecResult`
distinguishes successful runs from failures that keep the failing boundary state and the
undo of the already successful prefix.

## Main declarations

* `EffectResult`: one successful effect application;
* `Failure`: error, boundary state, and prefix undo of a failing run;
* `ExecResult`: the disjoint success/failure carrier;
* `EffectResultRel`, `FailureRel`, `ExecRel`: relation liftings;
* `effectResultRelSpec`, `failureRelSpec`, `execRelSpec`: the lifted `RelSpec`s;
* `failureRelEq`, `execRelEq`: equality specializations for diagnostics.
-/

universe u v

namespace STC

variable {S : Type u} {E : Type v}

@[expose] public section

/-! ### Raw result carriers -/

section Results

/-- One successful effect application: the successor state and the selected inverse. -/
structure EffectResult (S : Type u) where
  state : S
  undo : S → S

/-- A failing run retains the error, the failing boundary state, and the undo of the
already successful prefix. -/
structure Failure (S : Type u) (E : Type v) where
  error : E
  boundary : S
  prefixUndo : S → S

/-- The disjoint success/failure execution carrier. -/
inductive ExecResult (S : Type u) (E : Type v) where
  | success (result : EffectResult S)
  | failure (failure : Failure S E)

/-- The explicit success-only bridge from `EffectResult` to `ExecResult`: a
successful effect application embeds without inventing error or boundary data. -/
def effectResultToExec (result : EffectResult S) : ExecResult S E :=
  .success result

end Results

/-! ### Relation liftings -/

section ResultRelations

/-- The output relation of one successful effect application: related successor states
and pointwise-related selected inverses. -/
def EffectResultRel (R : RelSpec S)
    (left right : EffectResult S) : Prop :=
  R.rel left.state right.state ∧ PointwiseRel R left.undo right.undo

/-- The relation of failing runs: related errors, related boundary states, and
pointwise-related prefix undos. -/
def FailureRel (R : RelSpec S) (errorRel : E → E → Prop)
    (left right : Failure S E) : Prop :=
  errorRel left.error right.error ∧
    R.rel left.boundary right.boundary ∧
      PointwiseRel R left.prefixUndo right.prefixUndo

/-- The tagged execution relation: constructor tags are never silently identified. -/
def ExecRel (R : RelSpec S) (errorRel : E → E → Prop) :
    ExecResult S E → ExecResult S E → Prop
  | .success left, .success right => EffectResultRel R left right
  | .failure left, .failure right => FailureRel R errorRel left right
  | _, _ => False

/-- `EffectResultRel` is an explicit `RelSpec`. -/
def effectResultRelSpec (R : RelSpec S) : RelSpec (EffectResult S) where
  rel := EffectResultRel R
  refl := by
    intro result
    exact ⟨R.refl result.state, pointwiseRel_refl R result.undo⟩
  symm := by
    intro left right h
    exact ⟨R.symm h.1, pointwiseRel_symm h.2⟩
  trans := by
    intro left middle right h₁ h₂
    exact ⟨R.trans h₁.1 h₂.1, pointwiseRel_trans h₁.2 h₂.2⟩

/-- `FailureRel` is an explicit `RelSpec` once an error relation is selected. -/
def failureRelSpec (R : RelSpec S) (T : RelSpec E) :
    RelSpec (Failure S E) where
  rel := FailureRel R T.rel
  refl := by
    intro failure
    exact ⟨T.refl failure.error, R.refl failure.boundary,
      pointwiseRel_refl R failure.prefixUndo⟩
  symm := by
    intro left right h
    exact ⟨T.symm h.1, R.symm h.2.1, pointwiseRel_symm h.2.2⟩
  trans := by
    intro left middle right h₁ h₂
    exact ⟨T.trans h₁.1 h₂.1, R.trans h₁.2.1 h₂.2.1,
      pointwiseRel_trans h₁.2.2 h₂.2.2⟩

/-- `ExecRel` is an explicit `RelSpec` once an error relation is selected. -/
def execRelSpec (R : RelSpec S) (T : RelSpec E) :
    RelSpec (ExecResult S E) where
  rel := ExecRel R T.rel
  refl := by
    intro result
    cases result with
    | success result =>
        exact (effectResultRelSpec R).refl result
    | failure failure =>
        exact (failureRelSpec R T).refl failure
  symm := by
    intro left right h
    cases left <;> cases right <;> simp [ExecRel] at h ⊢
    · exact (effectResultRelSpec R).symm h
    · exact (failureRelSpec R T).symm h
  trans := by
    intro left middle right h₁ h₂
    cases left <;> cases middle <;> cases right <;>
      simp [ExecRel] at h₁ h₂ ⊢
    · exact (effectResultRelSpec R).trans h₁ h₂
    · exact (failureRelSpec R T).trans h₁ h₂

end ResultRelations

/-! ### Equality specializations -/

section EqualityResults

/-- Equality for failure diagnostics is available only through an explicit choice. -/
def failureRelEq (R : RelSpec S) (left right : Failure S E) : Prop :=
  FailureRel R (equality E).rel left right

/-- Equality for execution diagnostics is available only through an explicit choice. -/
def execRelEq (R : RelSpec S) : ExecResult S E → ExecResult S E → Prop :=
  ExecRel R (equality E).rel

end EqualityResults

end

end STC
