module

public import STC.Foundation.Relation

/-!
# Relation-parametric transport

Small reusable compatibility lemmas for the later observation and replay
interfaces.  Each relation remains an explicit argument.
-/

universe u v w

namespace STC

@[expose] public section

section Transport

variable {A : Type u} {B : Type v} {C : Type w}

/-- A map transports one relation into another. -/
def RelMap (R : RelSpec A) (S : RelSpec B) (f : A → B) : Prop :=
  RespectsOn R.rel S.rel f

theorem relMap_id (R : RelSpec A) : RelMap R R id := by
  intro x y h
  exact h

theorem relMap_comp (R : RelSpec A) (S : RelSpec B) (T : RelSpec C)
    (f : A → B) (g : B → C) (hf : RelMap R S f) (hg : RelMap S T g) :
    RelMap R T (g ∘ f) := by
  intro x y h
  exact hg (hf h)

/-- A relation-preserving map lifts an optional relation pointwise. -/
theorem optionRel_map (R : RelSpec A) (S : RelSpec B) (f : A → B)
    (hf : RelMap R S f) {x y : Option A}
    (h : OptionRel R.rel x y) : OptionRel S.rel (x.map f) (y.map f) := by
  cases x with
  | none => cases y <;> simp [OptionRel] at h ⊢
  | some x =>
      cases y with
      | none => simp [OptionRel] at h ⊢
      | some y => simp [OptionRel] at h ⊢; exact hf h

/-- Pointwise relation transport through two related maps. -/
def PointwiseMap (_R : RelSpec A) (S : RelSpec B)
    (f g : A → B) : Prop := ∀ x, S.rel (f x) (g x)

theorem pointwiseMap_trans (S : RelSpec B) {f g h : A → B}
    (hfg : PointwiseMap (equality A) S f g)
    (hgh : PointwiseMap (equality A) S g h) :
    PointwiseMap (equality A) S f h := by
  intro x
  exact S.trans (hfg x) (hgh x)

end Transport

end

end STC
