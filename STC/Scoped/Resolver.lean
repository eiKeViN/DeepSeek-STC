module

public import Mathlib.Data.Finset.Basic
public import STC.Scoped.Model

/-!
# Resolver specification, executable resolver, and updates

The ADR-10 two-layer resolver boundary.  The semantic layer is a
proposition-valued relation `ResolverSpec`: it may remain abstract or
nondeterministic and says which `RealmRef`s are admissible for a logical key.
The executable layer `Resolver` chooses one typed reference per key and carries
a finite override-support envelope: outside `overrideKeys` it resolves to the
model default.  `ResolverSatisfies` is the checked bridge between the layers;
no coercion silently identifies a deterministic function with a relational
specification.

`resolverUpdate` is the concrete executable update: it replaces the reference
at one key, preserves every other key, and grows the support by at most the
updated key.  `ResolverUpdate` is the abstract interface consumed by the
persistent isolation derivation.

## Main declarations

* `ResolverSpec`, `ResolverSatisfies`: the semantic layer and its satisfaction;
* `Resolver`, `ResolverTypePreserving`, `defaultResolver`: the executable layer;
* `resolverUpdate` with hit, miss, support-growth, and preservation laws;
* `ResolverUpdate` and `defaultResolverUpdate`: the abstract update interface.
-/

universe u v w

namespace STC.Scoped

@[expose] public section

/-! ### Semantic specification -/

section ResolverSpec

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}

/-- A semantic resolver specification: which references are admissible per key.

Ambiguity is allowed; the executable layer must prove which admissible choice
it makes through `ResolverSatisfies`. -/
def ResolverSpec (M : RealmModel K V) :=
  (k : K) → RealmRef M k → Prop

end ResolverSpec

/-! ### Executable resolver with finite support -/

section Resolver

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq K]

/-- An executable resolver chooses one typed realm and has finite override support. -/
structure Resolver (M : RealmModel K V) [DecidableEq K] where
  resolve : (k : K) → RealmRef M k
  overrideKeys : Finset K
  finite_support :
    ∀ {k}, k ∉ overrideKeys →
      (resolve k).token = (RealmRef.defaultRef M k).token

/-- A selected executable resolver refines a semantic resolver specification. -/
def ResolverSatisfies (ρ : Resolver M) (spec : ResolverSpec M) : Prop :=
  ∀ k, spec k (ρ.resolve k)

/-- The type-preservation proposition exposed by every executable resolver. -/
def ResolverTypePreserving (ρ : Resolver M) : Prop :=
  ∀ k, M.keyOf (ρ.resolve k).token = k

/-- Every executable resolver is type preserving by construction. -/
theorem resolver_type_preserving (ρ : Resolver M) : ResolverTypePreserving ρ := by
  intro k
  exact (ρ.resolve k).key_eq

/-- The resolver with no overrides: every key resolves to its model default. -/
def defaultResolver : Resolver M where
  resolve := fun k => RealmRef.defaultRef M k
  overrideKeys := ∅
  finite_support := by
    intro k _
    rfl

/-- The default resolver satisfies any specification that admits every default reference. -/
theorem resolverSatisfies_default (spec : ResolverSpec M)
    (h : ∀ k, spec k (RealmRef.defaultRef M k)) :
    ResolverSatisfies defaultResolver spec := by
  intro k
  exact h k

end Resolver

/-! ### Concrete executable update -/

section ResolverUpdateLaws

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq K] [DecidableEq M.Realm]

/-- Replace the reference at `k` by `rr`; support grows only when the physical token changes. -/
def resolverUpdate (ρ : Resolver M) (k : K) (rr : RealmRef M k) : Resolver M where
  resolve j := if h : j = k then h ▸ rr else ρ.resolve j
  overrideKeys :=
    if (ρ.resolve k).token = rr.token then ρ.overrideKeys else insert k ρ.overrideKeys
  finite_support := by
    intro j hj
    by_cases hjk : j = k
    · subst j
      by_cases htok : (ρ.resolve k).token = rr.token
      · have hnotin : k ∉ ρ.overrideKeys := by
          simpa [htok] using hj
        have hres : (if h : k = k then h ▸ rr else ρ.resolve k) = rr := by
          rw [dif_pos rfl]
        calc
          (if h : k = k then h ▸ rr else ρ.resolve k).token = rr.token :=
            congrArg RealmRef.token hres
          _ = (ρ.resolve k).token := htok.symm
          _ = (RealmRef.defaultRef M k).token := ρ.finite_support hnotin
      · exfalso
        exact hj (by simp [htok])
    · have hnotin : j ∉ ρ.overrideKeys := by
        by_cases htok : (ρ.resolve k).token = rr.token
        · simpa [htok] using hj
        · intro hmem
          exact hj (by simp [htok, hmem])
      rw [dif_neg hjk]
      exact ρ.finite_support hnotin

/-- The update hits its key: the new reference is exactly the one supplied. -/
theorem resolverUpdate_hit (ρ : Resolver M) (k : K) (rr : RealmRef M k) :
    (resolverUpdate ρ k rr).resolve k = rr := by
  change (if h : k = k then h ▸ rr else ρ.resolve k) = rr
  rw [dif_pos rfl]

/-- The update misses other keys: their references are preserved. -/
theorem resolverUpdate_miss (ρ : Resolver M) (k : K) (rr : RealmRef M k) {j : K}
    (h : j ≠ k) :
    (resolverUpdate ρ k rr).resolve j = ρ.resolve j := by
  change (if h' : j = k then h' ▸ rr else ρ.resolve j) = ρ.resolve j
  rw [dif_neg h]

/-- The update grows the override support by at most the updated key. -/
theorem resolverUpdate_support_subset (ρ : Resolver M) (k : K) (rr : RealmRef M k) :
    (resolverUpdate ρ k rr).overrideKeys ⊆ insert k ρ.overrideKeys := by
  change
    (if h : (ρ.resolve k).token = rr.token then ρ.overrideKeys else insert k ρ.overrideKeys)
      ⊆ insert k ρ.overrideKeys
  intro j hj
  by_cases htok : (ρ.resolve k).token = rr.token
  · exact Finset.mem_insert_of_mem (by simpa [htok] using hj)
  · simpa [htok] using hj

/-- Updating with the currently selected reference preserves resolution pointwise. -/
theorem resolverUpdate_idem_resolve (ρ : Resolver M) (k : K) :
    (resolverUpdate ρ k (ρ.resolve k)).resolve = ρ.resolve := by
  funext j
  by_cases h : j = k
  · subst j
    change (if h' : k = k then h' ▸ ρ.resolve k else ρ.resolve k) = ρ.resolve k
    rw [dif_pos rfl]
  · change (if h' : j = k then h' ▸ ρ.resolve k else ρ.resolve j) = ρ.resolve j
    rw [dif_neg h]

/-- Updating with the currently selected reference preserves the override support. -/
theorem resolverUpdate_idem_overrideKeys (ρ : Resolver M) (k : K) :
    (resolverUpdate ρ k (ρ.resolve k)).overrideKeys = ρ.overrideKeys := by
  change
    (if h : (ρ.resolve k).token = (ρ.resolve k).token then ρ.overrideKeys
      else insert k ρ.overrideKeys) = ρ.overrideKeys
  rw [dif_pos rfl]

/-- Updating with the currently selected reference leaves the whole resolver unchanged. -/
theorem resolverUpdate_idem (ρ : Resolver M) (k : K) :
    resolverUpdate ρ k (ρ.resolve k) = ρ := by
  unfold resolverUpdate
  cases ρ with
  | mk resolve overrideKeys finite_support =>
    congr
    · funext j
      by_cases h : j = k
      · subst j
        change (if h' : k = k then h' ▸ resolve k else resolve k) = resolve k
        rw [dif_pos rfl]
      · change (if h' : j = k then h' ▸ resolve k else resolve j) = resolve j
        rw [dif_neg h]
    · change
        (if h' : (resolve k).token = (resolve k).token then overrideKeys
          else insert k overrideKeys) = overrideKeys
      rw [dif_pos rfl]

/-- An updated resolver still satisfies the specification when the new reference is admissible. -/
theorem resolverUpdate_satisfies (ρ : Resolver M) (spec : ResolverSpec M) {k : K}
    (rr : RealmRef M k) (hρ : ResolverSatisfies ρ spec) (hk : spec k rr) :
    ResolverSatisfies (resolverUpdate ρ k rr) spec := by
  intro j
  by_cases h : j = k
  · subst j
    rw [resolverUpdate_hit ρ k rr]
    exact hk
  · rw [resolverUpdate_miss ρ k rr h]
    exact hρ j

end ResolverUpdateLaws

/-! ### Abstract update interface -/

section ResolverUpdateInterface

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq K]

/-- The abstract operation and laws required to derive an isolation resolver. -/
structure ResolverUpdate (M : RealmModel K V) [DecidableEq K] where
  isolate : Resolver M → (k : K) → RealmRef M k → Resolver M
  isolate_same :
    ∀ (ρ : Resolver M) (k : K) (rr : RealmRef M k),
      (isolate ρ k rr).resolve k = rr
  isolate_other :
    ∀ (ρ : Resolver M) (k : K) (rr : RealmRef M k) (j : K),
      j ≠ k → (isolate ρ k rr).resolve j = ρ.resolve j
  support_bound :
    ∀ (ρ : Resolver M) (k : K) (rr : RealmRef M k),
      (isolate ρ k rr).overrideKeys ⊆ insert k ρ.overrideKeys

end ResolverUpdateInterface

/-! ### Default update instance -/

section DefaultResolverUpdate

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq K] [DecidableEq M.Realm]

/-- The concrete executable update as an instance of the abstract interface. -/
def defaultResolverUpdate : ResolverUpdate M where
  isolate := resolverUpdate
  isolate_same := by
    intro ρ k rr
    exact resolverUpdate_hit ρ k rr
  isolate_other := by
    intro ρ k rr j h
    exact resolverUpdate_miss ρ k rr h
  support_bound := by
    intro ρ k rr
    exact resolverUpdate_support_subset ρ k rr

end DefaultResolverUpdate

end

end STC.Scoped
