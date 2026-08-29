module

public import STC.State.Support

/-!
# Support closure uniqueness

This module adds the rank-based uniqueness theorem for the positive support
operator.  The carrier and operator remain defined in `STC.State.Support`.
-/

universe u v

namespace STC

@[expose] public section

section Closure

variable {N : Type u} {K : Type v} [DecidableEq N] [DecidableEq K]

private theorem support_member_of_order_induction
    (s : SupportSnapshot N K) (o : SupportOrder s) {A : Set N}
    (hfixed : SupportOperator s A = A) :
    ∀ x : {n // n ∈ s.dom}, x.1 ∈ A → x.1 ∈ SupportSet s := by
  intro x
  refine WellFounded.induction (C := fun y : {n // n ∈ s.dom} =>
    y.1 ∈ A → y.1 ∈ SupportSet s) (supportDep_wellFounded s o) x ?_
  intro x ih hxA B hB
  have hxClause : SupportClause s A x.1 := by
    have hxOp : x.1 ∈ SupportOperator s A := by
      rw [hfixed]
      exact hxA
    exact hxOp
  have hparent : ParentSupported s B x.1 := by
    rcases hxClause.2.2.1 with hroot | ⟨p, hparent, hpA⟩
    · exact Or.inl hroot
    · have hpOp : p ∈ SupportOperator s A := by
        rw [hfixed]
        exact hpA
      have hpDom : p ∈ s.dom := hpOp.1
      have hpB : p ∈ B := by
        apply supportSet_least s hB
        apply ih ⟨p, hpDom⟩
        exact Or.inr hparent
        exact hpA
      exact Or.inr ⟨p, hparent, hpB⟩
  have hproviders : ProvidersSupported s B x.1 := by
    intro k hk
    rcases hxClause.2.2.2 k hk with ⟨m, hmA, hmk⟩
    have hmOp : m ∈ SupportOperator s A := by
      rw [hfixed]
      exact hmA
    have hmDom : m ∈ s.dom := hmOp.1
    have hmB : m ∈ B := by
      apply supportSet_least s hB
      apply ih ⟨m, hmDom⟩
      apply Or.inl
      refine ⟨k, ?_⟩
      exact Finset.mem_inter.mpr ⟨hmk, hk⟩
      exact hmA
    exact ⟨m, hmB, hmk⟩
  exact hB ⟨x.property, hxClause.2.1, hparent, hproviders⟩

/-- A ranked support order makes the positive fixed point unique. -/
theorem supportSet_eq_of_fixed
    (s : SupportSnapshot N K) (o : SupportOrder s) {A : Set N}
    (hfixed : SupportOperator s A = A) :
    SupportSet s = A := by
  apply Set.Subset.antisymm
  · apply supportSet_least s
    intro n hn
    exact hfixed ▸ hn
  · intro n hn
    have hOp : n ∈ SupportOperator s A := by
      rw [hfixed]
      exact hn
    exact support_member_of_order_induction s o hfixed ⟨n, hOp.1⟩ hn

/-- The uniqueness theorem in inclusion form. -/
theorem supportSet_eq_of_inclusions
    (s : SupportSnapshot N K) (o : SupportOrder s) {A : Set N}
    (hforward : A ⊆ SupportOperator s A)
    (hbackward : SupportOperator s A ⊆ A) :
    SupportSet s = A :=
  supportSet_eq_of_fixed s o (Set.Subset.antisymm hbackward hforward)

/-- No-late-registration supplies the order required by fixed-point uniqueness. -/
theorem supportSet_eq_of_fixed_noLate
    (s : SupportSnapshot N K) (freeze : NoLateRegistration s)
    {A : Set N} (hfixed : SupportOperator s A = A) :
    SupportSet s = A :=
  supportSet_eq_of_fixed s freeze.toOrder hfixed

end Closure

end

end STC
