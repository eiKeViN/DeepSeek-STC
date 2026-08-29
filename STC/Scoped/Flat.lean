module

public import STC.Scoped.Context

/-!
# One-way flat embedding

The ADR-10 flat-model boundary.  `FlatEmbedding` packages a one-way embedding
from a flat store into a scoped store with the three commuting diagrams:
scoped lookup, insert, and erase on the image agree with the flat operations.
The ADR conditions for the concrete toy are an identity resolver, no physical
aliasing, and neutral interception metadata; they are ambient conditions of the
instance, not fields of the contract.

This layer defines no arbitrary flatten/unflatten equivalence, universal
projection, or surjectivity claim: an arbitrary realm configuration is not
asserted to flatten faithfully.  `FlatImage` names the stable image and the
image laws state the restriction explicitly.

## Main declarations

* `FlatEmbedding` and its three commuting diagrams;
* `FlatImage` with `flatImage_self`, `flatImage_scopedInsert`,
  `flatImage_scopedErase`;
* `flatEmbedding_lookup_insert`, `flatEmbedding_lookup_erase`: derived
  lookup-after-update laws on the image.
-/

universe u v w x

namespace STC.Scoped

@[expose] public section

section FlatEmbedding

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {FlatStore ScopedStore : Type x}
variable [DecidableEq K]
variable {ops : RealmStoreOps M ScopedStore} {ρ : Resolver M}

/-- A flat-to-scoped embedding with lookup, insert, and erase commuting laws. -/
structure FlatEmbedding (M : RealmModel K V)
    (FlatStore ScopedStore : Type x) [DecidableEq K]
    (ops : RealmStoreOps M ScopedStore)
    (ρ : Resolver M) where
  embed : FlatStore → ScopedStore
  flatLookup : FlatStore → (k : K) → Option (V k)
  flatInsert : FlatStore → (k : K) → V k → FlatStore
  flatErase : FlatStore → K → FlatStore
  embed_lookup :
    ∀ (s : FlatStore) (k : K),
      scopedLookup ops ρ (embed s) k = flatLookup s k
  embed_insert :
    ∀ (s : FlatStore) (k : K) (v : V k),
      scopedInsert ops ρ (embed s) k v = embed (flatInsert s k v)
  embed_erase :
    ∀ (s : FlatStore) (k : K),
      scopedErase ops ρ (embed s) k = embed (flatErase s k)

/-- The stable image of the flat embedding: exactly the embedded flat stores. -/
def FlatImage (E : FlatEmbedding M FlatStore ScopedStore ops ρ)
    (s : ScopedStore) : Prop :=
  ∃ t : FlatStore, s = E.embed t

/-- Every embedded flat store is in the image. -/
theorem flatImage_self (E : FlatEmbedding M FlatStore ScopedStore ops ρ) (t : FlatStore) :
    FlatImage E (E.embed t) :=
  ⟨t, rfl⟩

/-- Scoped insertion stays inside the image. -/
theorem flatImage_scopedInsert (E : FlatEmbedding M FlatStore ScopedStore ops ρ)
    (t : FlatStore) (k : K) (v : V k) :
    FlatImage E (scopedInsert ops ρ (E.embed t) k v) :=
  ⟨E.flatInsert t k v, E.embed_insert t k v⟩

/-- Scoped erasure stays inside the image. -/
theorem flatImage_scopedErase (E : FlatEmbedding M FlatStore ScopedStore ops ρ)
    (t : FlatStore) (k : K) :
    FlatImage E (scopedErase ops ρ (E.embed t) k) :=
  ⟨E.flatErase t k, E.embed_erase t k⟩

/-- Scoped lookup on the image agrees with the flat lookup. -/
theorem flatImage_lookup (E : FlatEmbedding M FlatStore ScopedStore ops ρ)
    (t : FlatStore) (k : K) :
    scopedLookup ops ρ (E.embed t) k = E.flatLookup t k :=
  E.embed_lookup t k

/-- A flat insertion followed by a scoped lookup returns the inserted value. -/
theorem flatEmbedding_lookup_insert (E : FlatEmbedding M FlatStore ScopedStore ops ρ)
    (t : FlatStore) (k : K) (v : V k) :
    scopedLookup ops ρ (E.embed (E.flatInsert t k v)) k = some v := by
  rw [← E.embed_insert t k v]
  exact scopedLookup_insert_self ops ρ (E.embed t) k v

/-- A flat erasure followed by a scoped lookup returns none. -/
theorem flatEmbedding_lookup_erase (E : FlatEmbedding M FlatStore ScopedStore ops ρ)
    (t : FlatStore) (k : K) :
    scopedLookup ops ρ (E.embed (E.flatErase t k)) k = none := by
  rw [← E.embed_erase t k]
  exact scopedLookup_erase_self ops ρ (E.embed t) k

end FlatEmbedding

end

end STC.Scoped
