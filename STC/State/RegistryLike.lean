import STC.Foundation.Relation

/-!
# Finite uniform registries

This module defines the abstract finite fiber-registry interface. Carrier
equality and canonical ordering are deliberately absent: semantic comparison
is pointwise through `RegistryObs`.

## Main declarations

* `RegistryLike`: lookup, update, finite-domain, and frame laws.
* `RegistryObs`: order-insensitive pointwise observation.
* `insertFresh?` and `erasePresent?`: checked policy wrappers.
-/

universe u v w

namespace STC

/-- A finite uniform registry with explicit lookup, update, and domain laws. -/
structure RegistryLike (K V R : Type u) [DecidableEq K] where
  empty : R
  lookup : R → K → Option V
  insert : R → K → V → R
  erase : R → K → R
  domain : R → List K
  domain_nodup : ∀ r, (domain r).Nodup
  lookup_empty : ∀ k, lookup empty k = none
  lookup_insert_eq : ∀ r k v, lookup (insert r k v) k = some v
  lookup_insert_ne : ∀ r k k' v, k' ≠ k →
    lookup (insert r k v) k' = lookup r k'
  lookup_erase_eq : ∀ r k, lookup (erase r k) k = none
  lookup_erase_ne : ∀ r k k', k' ≠ k →
    lookup (erase r k) k' = lookup r k'
  mem_domain_iff : ∀ r k, k ∈ domain r ↔ (lookup r k).isSome

variable {K V R : Type u} [DecidableEq K]

/-- Pointwise, tag-strict observation of two registry carriers. -/
def RegistryObs (api : RegistryLike K V R) (VRel : RelSpec V)
    (left right : R) : Prop :=
  ∀ k, OptionRel VRel.rel (api.lookup left k) (api.lookup right k)

/-- Registry observation packaged as an explicit equivalence specification. -/
def registryObsSpec (api : RegistryLike K V R)
    (VRel : RelSpec V) : RelSpec R where
  rel := RegistryObs api VRel
  refl := by
    intro r k
    exact (optionRelSpec VRel).refl (api.lookup r k)
  symm := by
    intro left right h k
    exact (optionRelSpec VRel).symm (h k)
  trans := by
    intro left middle right h₁ h₂ k
    exact (optionRelSpec VRel).trans (h₁ k) (h₂ k)

theorem registryObs_lookup
    (api : RegistryLike K V R) (VRel : RelSpec V)
    {left right : R} (h : RegistryObs api VRel left right) (k : K) :
    OptionRel VRel.rel (api.lookup left k) (api.lookup right k) :=
  h k

theorem registryObs_same_domain
    (api : RegistryLike K V R) (VRel : RelSpec V)
    {left right : R} (h : RegistryObs api VRel left right) (k : K) :
    (k ∈ api.domain left) ↔ k ∈ api.domain right := by
  rw [api.mem_domain_iff, api.mem_domain_iff]
  have hk := h k
  cases hl : api.lookup left k with
  | none =>
      cases hr : api.lookup right k with
      | none => simp
      | some vr => simp [OptionRel, hl, hr] at hk
  | some vl =>
      cases hr : api.lookup right k with
      | none => simp [OptionRel, hl, hr] at hk
      | some vr =>
          simp [hl, hr] at hk ⊢

theorem registryObs_insert
    (api : RegistryLike K V R) (VRel : RelSpec V)
    {left right : R} (h : RegistryObs api VRel left right)
    {k : K} {leftValue rightValue : V} (hv : VRel.rel leftValue rightValue) :
    RegistryObs api VRel (api.insert left k leftValue)
      (api.insert right k rightValue) := by
  intro key
  by_cases hkey : key = k
  · subst key
    rw [api.lookup_insert_eq, api.lookup_insert_eq]
    exact hv
  · rw [api.lookup_insert_ne left k key leftValue hkey,
      api.lookup_insert_ne right k key rightValue hkey]
    exact h key

theorem registryObs_erase
    (api : RegistryLike K V R) (VRel : RelSpec V)
    {left right : R} (h : RegistryObs api VRel left right) (k : K) :
    RegistryObs api VRel (api.erase left k) (api.erase right k) := by
  intro key
  by_cases hkey : key = k
  · subst key
    rw [api.lookup_erase_eq, api.lookup_erase_eq]
    trivial
  · rw [api.lookup_erase_ne left k key hkey,
      api.lookup_erase_ne right k key hkey]
    exact h key

theorem domain_insert_iff
    (api : RegistryLike K V R) (r : R) (k : K) (v : V) (key : K) :
    key ∈ api.domain (api.insert r k v) ↔
      key = k ∨ key ∈ api.domain r := by
  rw [api.mem_domain_iff]
  by_cases hkey : key = k
  · subst key
    rw [api.lookup_insert_eq]
    simp
  · rw [api.lookup_insert_ne _ _ _ _ hkey, api.mem_domain_iff]
    cases api.lookup r key <;> simp [hkey]

theorem domain_erase_iff
    (api : RegistryLike K V R) (r : R) (k : K) (key : K) :
    key ∈ api.domain (api.erase r k) ↔
      key ≠ k ∧ key ∈ api.domain r := by
  rw [api.mem_domain_iff]
  by_cases hkey : key = k
  · subst key
    rw [api.lookup_erase_eq]
    simp
  · rw [api.lookup_erase_ne _ _ _ hkey, api.mem_domain_iff]
    cases api.lookup r key <;> simp [hkey]

/-- Insert only when the key is absent. -/
def insertFresh? (api : RegistryLike K V R)
    (r : R) (k : K) (v : V) : Option R :=
  if (api.lookup r k).isSome then none else some (api.insert r k v)

/-- Erase only when the key is present, retaining its previous value. -/
def erasePresent? (api : RegistryLike K V R)
    (r : R) (k : K) : Option (V × R) :=
  match api.lookup r k with
  | none => none
  | some old => some (old, api.erase r k)

theorem insertFresh?_eq_none_iff
    (api : RegistryLike K V R) (r : R) (k : K) (v : V) :
    insertFresh? api r k v = none ↔ (api.lookup r k).isSome := by
  cases h : api.lookup r k <;> simp [insertFresh?, h]

theorem insertFresh?_success
    (api : RegistryLike K V R) (r : R) (k : K) (v : V)
    (h : api.lookup r k = none) :
    insertFresh? api r k v = some (api.insert r k v) ∧
      api.lookup (api.insert r k v) k = some v := by
  constructor
  · simp [insertFresh?, h]
  · exact api.lookup_insert_eq r k v

theorem erasePresent?_eq_none_iff
    (api : RegistryLike K V R) (r : R) (k : K) :
    erasePresent? api r k = none ↔ api.lookup r k = none := by
  cases h : api.lookup r k <;> simp [erasePresent?, h]

theorem erasePresent?_success
    (api : RegistryLike K V R) (r : R) (k : K) (old : V)
    (h : api.lookup r k = some old) :
    erasePresent? api r k = some (old, api.erase r k) ∧
      api.lookup (api.erase r k) k = none := by
  constructor
  · simp [erasePresent?, h]
  · exact api.lookup_erase_eq r k

theorem erase_insert_of_absent_obs
    (api : RegistryLike K V R) (VRel : RelSpec V)
    (r : R) (k : K) (v : V) (h : api.lookup r k = none) :
    RegistryObs api VRel (api.erase (api.insert r k v) k) r := by
  intro key
  by_cases hkey : key = k
  · subst key
    rw [api.lookup_erase_eq, h]
    trivial
  · rw [api.lookup_erase_ne _ _ _ hkey, api.lookup_insert_ne _ _ _ _ hkey]
    exact (optionRelSpec VRel).refl _

theorem insert_erase_of_lookup_obs
    (api : RegistryLike K V R) (VRel : RelSpec V)
    (r : R) (k : K) (old : V) (h : api.lookup r k = some old) :
    RegistryObs api VRel (api.insert (api.erase r k) k old) r := by
  intro key
  by_cases hkey : key = k
  · subst key
    rw [api.lookup_insert_eq, h]
    exact VRel.refl old
  · rw [api.lookup_insert_ne _ _ _ _ hkey, api.lookup_erase_ne _ _ _ hkey]
    exact (optionRelSpec VRel).refl _

end STC
