module

public import STC.Alpha.Trace
public import STC.State.Support.Closure

/-!
# Alpha transport for support snapshots

Incarnation names are reindexed by a permutation while provision keys remain
fixed.  The transport API covers support relations, the positive operator,
canonical support, and rank certificates.
-/

universe u v

namespace STC

@[expose] public section

section AlphaSupport

variable {N : Type u} {K : Type v} [DecidableEq N] [DecidableEq K]

/-- Reindex a set of incarnation names by the inverse permutation. -/
def renameSet (χ : Equiv.Perm N) (A : Set N) : Set N :=
  {n | χ.symm n ∈ A}

omit [DecidableEq N] in
theorem renameSet_mem (χ : Equiv.Perm N) (A : Set N) (n : N) :
    n ∈ renameSet χ A ↔ χ.symm n ∈ A := Iff.rfl

omit [DecidableEq N] in
theorem renameSet_comp (χ ψ : Equiv.Perm N) (A : Set N) :
    renameSet χ (renameSet ψ A) = renameSet (χ * ψ) A := by
  ext n
  change χ.symm n ∈ renameSet ψ A ↔ (χ * ψ).symm n ∈ A
  have hinv : (χ * ψ).symm = ψ.symm * χ.symm := by
    change (χ * ψ)⁻¹ = ψ⁻¹ * χ⁻¹
    exact mul_inv_rev χ ψ
  rw [hinv]
  simp [renameSet]

/-- Rename only the incarnation carrier of a committed support snapshot. -/
def renameSnapshot (χ : Equiv.Perm N) (s : SupportSnapshot N K) :
    SupportSnapshot N K where
  dom := renameFinset χ s.dom
  retired := fun n => s.retired (χ.symm n)
  parent := fun n => renameParentRef χ (s.parent (χ.symm n))
  requires := fun n => s.requires (χ.symm n)
  provides := fun n => s.provides (χ.symm n)
  birth := fun n => s.birth (χ.symm n)

theorem renameSnapshot_dom (χ : Equiv.Perm N) (s : SupportSnapshot N K) (n : N) :
    χ n ∈ (renameSnapshot χ s).dom ↔ n ∈ s.dom := by
  simp [renameSnapshot, renameFinset_mem]

theorem precedes_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) {a b : N} :
    Precedes (renameSnapshot χ s) (χ a) (χ b) ↔ Precedes s a b := by
  simp [Precedes, renameSnapshot]

theorem parentEdge_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) {a b : N} :
    ParentEdge (renameSnapshot χ s) (χ a) (χ b) ↔ ParentEdge s a b := by
  simp [ParentEdge, renameSnapshot, renameParentRef]

theorem supportRel_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) {a b : N} :
    SupportRel (renameSnapshot χ s) (χ a) (χ b) ↔ SupportRel s a b := by
  simp [SupportRel, precedes_rename, parentEdge_rename]

theorem supportDep_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) {a b : N} :
    SupportDep (renameSnapshot χ s) (χ b) (χ a) ↔ SupportDep s b a := by
  exact supportRel_rename χ s

theorem supportClause_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K)
    {A : Set N} {n : N} :
    SupportClause (renameSnapshot χ s) (renameSet χ A) (χ n) ↔
      SupportClause s A n := by
  constructor
  · intro h
    refine ⟨(renameSnapshot_dom χ s n).mp (by simpa using h.1), ?_, ?_, ?_⟩
    · simpa [renameSnapshot] using h.2.1
    · rcases h.2.2.1 with hroot | ⟨p, hp, hpA⟩
      · exact Or.inl (by simpa [renameSnapshot, renameParentRef] using hroot)
      · let q := χ.symm p
        have hparent : s.parent n = some q := by
          have := congrArg (Option.map χ.symm) hp
          simpa [renameSnapshot, renameParentRef, q] using this
        exact Or.inr ⟨q, hparent, by simpa [renameSet, q] using hpA⟩
    · intro k hk
      rcases h.2.2.2 k (by simpa [renameSnapshot] using hk) with ⟨m, hm, hkm⟩
      refine ⟨χ.symm m, ?_, ?_⟩
      · simpa [renameSet] using hm
      · simpa [renameSnapshot] using hkm
  · intro h
    refine ⟨(renameSnapshot_dom χ s n).mpr h.1, ?_, ?_, ?_⟩
    · simpa [renameSnapshot] using h.2.1
    · rcases h.2.2.1 with hroot | ⟨p, hp, hpA⟩
      · exact Or.inl (by simpa [renameSnapshot, renameParentRef] using hroot)
      · refine Or.inr ⟨χ p, ?_, ?_⟩
        · simp [renameSnapshot, renameParentRef, hp]
        · simpa [renameSet] using hpA
    · intro k hk
      rcases h.2.2.2 k (by simpa [renameSnapshot] using hk) with ⟨m, hm, hkm⟩
      refine ⟨χ m, ?_, ?_⟩
      · simpa [renameSet] using hm
      · simpa [renameSnapshot] using hkm

theorem supportOperator_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K)
    (A : Set N) (n : N) :
    χ n ∈ SupportOperator (renameSnapshot χ s) (renameSet χ A) ↔
      n ∈ SupportOperator s A :=
  supportClause_rename χ s

theorem prefixed_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K)
    (A : Set N) :
    Prefixed s A ↔
      Prefixed (renameSnapshot χ s) (renameSet χ A) := by
  constructor
  · intro h n hn
    have hn' : χ.symm n ∈ SupportOperator s A :=
      (supportOperator_rename χ s A (χ.symm n)).mp (by simpa using hn)
    simpa [renameSet] using h hn'
  · intro h n hn
    have hn' : χ n ∈ SupportOperator (renameSnapshot χ s) (renameSet χ A) :=
      (supportOperator_rename χ s A n).mpr hn
    have := h hn'
    simpa [renameSet] using this

theorem supportSet_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) {n : N} :
    χ n ∈ SupportSet (renameSnapshot χ s) ↔ n ∈ SupportSet s := by
  constructor
  · intro h A hA
    have hA' := (prefixed_rename χ s A).mp hA
    have hm := h (renameSet χ A) hA'
    simpa [renameSet] using hm
  · intro h A hA
    let B := renameSet χ.symm A
    have hBA : renameSet χ B = A := by
      ext x
      simp [B, renameSet]
    have hB : Prefixed s B := (prefixed_rename χ s B).mpr (by simpa [hBA] using hA)
    have hm := h B hB
    simpa [B, renameSet] using hm

/-- Transport a support order by reindexing its rank function. -/
def renameOrder (χ : Equiv.Perm N) (s : SupportSnapshot N K)
    (o : SupportOrder s) : SupportOrder (renameSnapshot χ s) where
  rank := fun n => o.rank (χ.symm n)
  edge_lt := by
    intro a b ha hb hab
    let a' := χ.symm a
    let b' := χ.symm b
    apply o.edge_lt
    · exact (renameSnapshot_dom χ s a').mp (by simpa [a'] using ha)
    · exact (renameSnapshot_dom χ s b').mp (by simpa [b'] using hb)
    · exact (supportRel_rename χ s).mp (by simpa [a', b'] using hab)

theorem supportWF_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) :
    SupportWF (renameSnapshot χ s) ↔ SupportWF s := by
  constructor
  · rintro ⟨o⟩
    refine ⟨{ rank := fun n => o.rank (χ n), edge_lt := ?_ }⟩
    intro a b ha hb hab
    exact o.edge_lt ((renameSnapshot_dom χ s a).mpr ha)
      ((renameSnapshot_dom χ s b).mpr hb) ((supportRel_rename χ s).mpr hab)
  · rintro ⟨o⟩
    exact ⟨renameOrder χ s o⟩

theorem noLate_rename (χ : Equiv.Perm N) (s : SupportSnapshot N K) :
    NoLateRegistration (renameSnapshot χ s) ↔ NoLateRegistration s := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro a b ha hb hab
    have := h.birth_strict (a := χ a) (b := χ b)
      ((renameSnapshot_dom χ s a).mpr ha) ((renameSnapshot_dom χ s b).mpr hb)
      ((supportRel_rename χ s).mpr hab)
    simpa [renameSnapshot] using this
  · intro h
    refine ⟨?_⟩
    intro a b ha hb hab
    have := h.birth_strict (a := χ.symm a) (b := χ.symm b)
      ((renameSnapshot_dom χ s (χ.symm a)).mp (by simpa using ha))
      ((renameSnapshot_dom χ s (χ.symm b)).mp (by simpa using hb))
      ((supportRel_rename χ s).mp (by simpa using hab))
    simpa [renameSnapshot] using this

end AlphaSupport

end

end STC
