import STC.Foundation.Relation

universe u v

namespace STC

variable {S : Type u} {E : Type v}

/-! Raw result carriers retain the selected state and every inverse field. -/

structure EffectResult (S : Type u) where
  state : S
  undo : S → S

structure Failure (S : Type u) (E : Type v) where
  error : E
  boundary : S
  prefixUndo : S → S

inductive ExecResult (S : Type u) (E : Type v) where
  | success (result : EffectResult S)
  | failure (failure : Failure S E)

def EffectResultRel (R : RelSpec S)
    (left right : EffectResult S) : Prop :=
  R.rel left.state right.state ∧ PointwiseRel R left.undo right.undo

def FailureRel (R : RelSpec S) (errorRel : E → E → Prop)
    (left right : Failure S E) : Prop :=
  errorRel left.error right.error ∧
    R.rel left.boundary right.boundary ∧
      PointwiseRel R left.prefixUndo right.prefixUndo

def ExecRel (R : RelSpec S) (errorRel : E → E → Prop) :
    ExecResult S E → ExecResult S E → Prop
  | .success left, .success right => EffectResultRel R left right
  | .failure left, .failure right => FailureRel R errorRel left right
  | _, _ => False

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

/- Equality for diagnostics is available only through an explicit choice. -/
def failureRelEq (R : RelSpec S) (left right : Failure S E) : Prop :=
  FailureRel R (equality E).rel left right

def execRelEq (R : RelSpec S) : ExecResult S E → ExecResult S E → Prop :=
  ExecRel R (equality E).rel

end STC
