module

/-!
# Explicit relation specifications

`RelSpec` is the metatheory's explicit equivalence carrier: a relation value with
reflexivity, symmetry, and transitivity, passed as data rather than installed as a global
`Setoid` instance, because one carrier may carry several simultaneous observational
relations.

## Main declarations

* `RelSpec`: explicit equivalence specification;
* `RespectsOn`, `Respects`: relation preservation for maps;
* `PointwiseRel`, `CrossRel`: same-input and related-input map relations;
* `OptionRel`, `optionRelSpec`: the tagged optional-result relator;
* `PullbackRel`, `pullbackRelSpec`: observation pullbacks;
* `equality`: the explicit equality specialization.
-/

universe u v

namespace STC

variable {α : Type u} {β : Type v}

@[expose] public section

/-! ### Equivalence carriers and map relations -/

section Relations

/-- An explicit equivalence value: a relation with reflexivity, symmetry, and
transitivity. It is passed as data, not installed as a global `Setoid` instance. -/
structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- Heterogeneous relation preservation. -/
def RespectsOn (R : α → α → Prop) (S : β → β → Prop) (f : α → β) : Prop :=
  ∀ {x y}, R x y → S (f x) (f y)

/-- An endomorphism preserves the selected relation. -/
def Respects (R : RelSpec α) (f : α → α) : Prop :=
  RespectsOn R.rel R.rel f

/-- Same-input agreement of two endomorphisms. -/
def PointwiseRel (R : RelSpec α) (f g : α → α) : Prop :=
  ∀ x, R.rel (f x) (g x)

/-- Related-input comparison of two endomorphisms. -/
def CrossRel (R : RelSpec α) (f g : α → α) : Prop :=
  ∀ {x y}, R.rel x y → R.rel (f x) (g y)

/-- Respects plus pointwise agreement yields related-input agreement. -/
theorem crossRel_of_respects_pointwise
    {R : RelSpec α} {f g : α → α}
    (hf : Respects R f) (hfg : PointwiseRel R f g) :
    CrossRel R f g := by
  intro x y hxy
  exact R.trans (hf hxy) (hfg y)

/-- Related-input agreement yields same-input agreement on reflexive inputs. -/
theorem pointwiseRel_of_crossRel
    {R : RelSpec α} {f g : α → α}
    (hfg : CrossRel R f g) : PointwiseRel R f g := by
  intro x
  exact hfg (R.refl x)

/-- Self-cross agreement is exactly respect. -/
theorem respects_of_crossRel_self
    {R : RelSpec α} {f : α → α}
    (hff : CrossRel R f f) : Respects R f := by
  intro x y hxy
  exact hff hxy

/-- For an equivalence, cross-input agreement entails properness of the left map. -/
theorem respects_left_of_crossRel
    {R : RelSpec α} {f g : α → α}
    (hfg : CrossRel R f g) : Respects R f := by
  intro x y hxy
  have hpoint : PointwiseRel R f g := pointwiseRel_of_crossRel hfg
  exact R.trans (hfg hxy) (R.symm (hpoint y))

/-- For an equivalence, cross-input agreement entails properness of the right map. -/
theorem respects_right_of_crossRel
    {R : RelSpec α} {f g : α → α}
    (hfg : CrossRel R f g) : Respects R g := by
  intro x y hxy
  have hpoint : PointwiseRel R f g := pointwiseRel_of_crossRel hfg
  exact R.trans (R.symm (hpoint x)) (hfg hxy)

/-- The identity map respects every relation. -/
theorem respects_id (R : RelSpec α) : Respects R id := by
  intro x y hxy
  exact hxy

/-- Respect is closed under composition. -/
theorem respects_comp {R : RelSpec α}
    {f g : α → α} (hf : Respects R f) (hg : Respects R g) :
    Respects R (f ∘ g) := by
  intro x y hxy
  exact hf (hg hxy)

/-- Pointwise agreement is reflexive. -/
theorem pointwiseRel_refl (R : RelSpec α) (f : α → α) :
    PointwiseRel R f f := by
  intro x
  exact R.refl (f x)

/-- Pointwise agreement is symmetric. -/
theorem pointwiseRel_symm {R : RelSpec α}
    {f g : α → α} (h : PointwiseRel R f g) :
    PointwiseRel R g f := by
  intro x
  exact R.symm (h x)

/-- Pointwise agreement is transitive. -/
theorem pointwiseRel_trans {R : RelSpec α}
    {f g h : α → α} (h₁ : PointwiseRel R f g)
    (h₂ : PointwiseRel R g h) : PointwiseRel R f h := by
  intro x
  exact R.trans (h₁ x) (h₂ x)

/-- Pointwise agreement composes when the outer map respects the relation. -/
theorem compose_pointwiseRel
    {R : RelSpec α} {f g h k : α → α}
    (hf : Respects R f) (hfg : PointwiseRel R f g)
    (hhk : PointwiseRel R h k) :
    PointwiseRel R (f ∘ h) (g ∘ k) := by
  intro x
  exact R.trans (hf (hhk x)) (hfg (k x))

end Relations

/-! ### Optional results -/

section OptionResults

/-- Tagged optional-result relation: constructor tags are never silently
identified, and `some` values are compared by the supplied payload relation. -/
def OptionRel (R : α → α → Prop) : Option α → Option α → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

/-- The optional-result relation lifts a `RelSpec` to `RelSpec (Option α)`. -/
def optionRelSpec {α : Type u} (R : RelSpec α) : RelSpec (Option α) where
  rel := OptionRel R.rel
  refl := by
    intro x
    cases x with
    | none => trivial
    | some x => exact R.refl x
  symm := by
    intro x y h
    cases x <;> cases y <;> simp [OptionRel] at h ⊢
    exact R.symm h
  trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp [OptionRel] at hxy hyz ⊢
    exact R.trans hxy hyz

end OptionResults

/-! ### Observation pullbacks -/

section Pullbacks

/-- Kernel equivalence of a concrete observation. -/
def PullbackRel {State : Type u} {Obs : Type v}
    (project : State → Obs) (R : RelSpec Obs) : State → State → Prop :=
  fun x y => R.rel (project x) (project y)

/-- The observation kernel is an explicit `RelSpec`. -/
def pullbackRelSpec {State : Type u} {Obs : Type v}
    (project : State → Obs) (R : RelSpec Obs) : RelSpec State where
  rel := PullbackRel project R
  refl := by
    intro x
    exact R.refl (project x)
  symm := by
    intro x y hxy
    exact R.symm hxy
  trans := by
    intro x y z hxy hyz
    exact R.trans hxy hyz

end Pullbacks

/-! ### The equality specialization -/

section Equality

/-- Equality is one explicit specialization, never a global relation instance. -/
def equality (α : Type u) : RelSpec α where
  rel := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

end Equality

end

end STC
