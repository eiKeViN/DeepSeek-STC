module

public import STC.Scoped.Store

/-!
# Metadata, interception, and persistent derived contexts

The ADR-10 context layer.  `MetaAlgebra` carries the per-key metadata monoid
with explicit identity and associativity laws; bias is deliberately not part of
those laws.  `MetadataPrecedence` states right-biased override separately: a
generic monoid instance provides no priority guarantee.
`InterceptionSpec` keeps presence (the finite support) apart from the
`Option (Meta k)` payload, so `none` is not confused with a present metadata
value.

`ScopedContext` is the persistent carrier: resolver, realm store, and inherited
metadata.  `deriveIsolate` derives a child through the `ResolverUpdate`
interface and changes only the resolver; `deriveIntercept` merges inherited
metadata with the new specification and changes only `contextMeta`.  The parent
is never mutated.  Provider behavior is an explicit `ProviderAdapter` boundary:
`effectiveMeta` merges declared metadata first and the context operand second,
so a present context metadata wins through `MetadataPrecedence`.

## Main declarations

* `MetaAlgebra`, `MetadataPrecedence`, `InterceptionSpec`;
* `ScopedContext`, `deriveIsolate`, `deriveIntercept` with their persistence
  and precedence laws;
* `effectiveMeta`, `ProviderAdapter`, `provideWith` and its precedence,
  neutrality, and key-locality laws.
-/

universe u v w x y

namespace STC.Scoped

@[expose] public section

/-! ### Metadata algebra and precedence -/

section MetaAlgebra

variable {K : Type u} {Meta : K → Type y}

/-- A per-key metadata monoid.  Bias is deliberately not part of these laws. -/
structure MetaAlgebra (K : Type u) (Meta : K → Type y) where
  empty : (k : K) → Meta k
  merge : (k : K) → Meta k → Meta k → Meta k
  left_id : ∀ k x, merge k (empty k) x = x
  right_id : ∀ k x, merge k x (empty k) = x
  assoc : ∀ k x y z, merge k (merge k x y) z = merge k x (merge k y z)

/-- Right priority is an additional law for a concrete metadata algebra. -/
structure MetadataPrecedence (A : MetaAlgebra K Meta) where
  present : (k : K) → Meta k → Prop
  right_wins :
    ∀ (k : K) (old new : Meta k), present k new →
      A.merge k old new = new

end MetaAlgebra

/-! ### Interception specification -/

section InterceptionSpec

variable {K : Type u} {Meta : K → Type y}
variable [DecidableEq K]

/-- A finite interception specification keeps presence separate from metadata. -/
structure InterceptionSpec (K : Type u) (Meta : K → Type y)
    [DecidableEq K] where
  /-- `at` is a reserved token in Lean, so the field is named `atKey`. -/
  atKey : (k : K) → Option (Meta k)
  support : Finset K
  support_sound :
    ∀ {k : K} {m : Meta k}, atKey k = some m → k ∈ support
  support_complete :
    ∀ {k : K}, k ∈ support → ∃ m : Meta k, atKey k = some m

/-- Support membership is exactly presence of an interception payload. -/
theorem interceptionSpec_support_iff (spec : InterceptionSpec K Meta) (k : K) :
    k ∈ spec.support ↔ ∃ m : Meta k, spec.atKey k = some m := by
  constructor
  · intro h
    exact spec.support_complete h
  · rintro ⟨m, hm⟩
    exact spec.support_sound hm

end InterceptionSpec

/-! ### Persistent scoped contexts -/

section ScopedContext

variable {K : Type u} {V : K → Type v} {Meta : K → Type y}
variable {M : RealmModel K V} {Store : Type x}
variable [DecidableEq K]

/-- Persistent scoped state: resolver, realm store, and inherited metadata. -/
structure ScopedContext (M : RealmModel K V)
    (Meta : K → Type y) (Store : Type x) [DecidableEq K] where
  resolver : Resolver M
  realms : Store
  contextMeta : (k : K) → Meta k

/-- Isolation derives a child context through an explicit resolver-update API. -/
def deriveIsolate (u : ResolverUpdate M)
    (c : ScopedContext M Meta Store) (k : K) (rr : RealmRef M k) :
    ScopedContext M Meta Store :=
  { c with resolver := u.isolate c.resolver k rr }

/-- Interception derives a child context by merging inherited and new metadata. -/
def deriveIntercept (A : MetaAlgebra K Meta)
    (c : ScopedContext M Meta Store)
    (spec : InterceptionSpec K Meta) : ScopedContext M Meta Store :=
  { c with
    contextMeta := fun k =>
      A.merge k (c.contextMeta k)
        (match spec.atKey k with
        | some m => m
        | none => A.empty k) }

/-- Isolation leaves the realm store and interception metadata definitionally unchanged. -/
theorem deriveIsolate_persistent (u : ResolverUpdate M)
    (c : ScopedContext M Meta Store) (k : K) (rr : RealmRef M k) :
    (deriveIsolate u c k rr).realms = c.realms ∧
      (deriveIsolate u c k rr).contextMeta = c.contextMeta := by
  exact ⟨rfl, rfl⟩

/-- Isolation updates exactly the selected key. -/
theorem deriveIsolate_resolver_hit (u : ResolverUpdate M)
    (c : ScopedContext M Meta Store) (k : K) (rr : RealmRef M k) :
    (deriveIsolate u c k rr).resolver.resolve k = rr :=
  u.isolate_same c.resolver k rr

/-- Isolation preserves every other key's resolution. -/
theorem deriveIsolate_resolver_miss (u : ResolverUpdate M)
    (c : ScopedContext M Meta Store) (k : K) (rr : RealmRef M k) {j : K} (h : j ≠ k) :
    (deriveIsolate u c k rr).resolver.resolve j = c.resolver.resolve j :=
  u.isolate_other c.resolver k rr j h

/-- Isolation grows the override support by at most the selected key. -/
theorem deriveIsolate_support_bound (u : ResolverUpdate M)
    (c : ScopedContext M Meta Store) (k : K) (rr : RealmRef M k) :
    (deriveIsolate u c k rr).resolver.overrideKeys ⊆ insert k c.resolver.overrideKeys :=
  u.support_bound c.resolver k rr

/-- Interception leaves the resolver and realm store definitionally unchanged. -/
theorem deriveIntercept_persistent (A : MetaAlgebra K Meta)
    (c : ScopedContext M Meta Store)
    (spec : InterceptionSpec K Meta) :
    (deriveIntercept A c spec).resolver = c.resolver ∧
      (deriveIntercept A c spec).realms = c.realms := by
  exact ⟨rfl, rfl⟩

/-- A present interception payload wins over the inherited metadata by right precedence. -/
theorem deriveIntercept_merge_present (A : MetaAlgebra K Meta) (P : MetadataPrecedence A)
    (c : ScopedContext M Meta Store) (spec : InterceptionSpec K Meta) {k : K} {m : Meta k}
    (h : spec.atKey k = some m) (hp : P.present k m) :
    (deriveIntercept A c spec).contextMeta k = m := by
  change A.merge k (c.contextMeta k)
    (match spec.atKey k with
    | some m => m
    | none => A.empty k) = m
  rw [h]
  exact P.right_wins k (c.contextMeta k) m hp

/-- An absent interception payload leaves the inherited metadata unchanged. -/
theorem deriveIntercept_merge_absent (A : MetaAlgebra K Meta)
    (c : ScopedContext M Meta Store) (spec : InterceptionSpec K Meta) {k : K}
    (h : spec.atKey k = none) :
    (deriveIntercept A c spec).contextMeta k = c.contextMeta k := by
  change A.merge k (c.contextMeta k)
    (match spec.atKey k with
    | some m => m
    | none => A.empty k) = c.contextMeta k
  rw [h]
  exact A.right_id k (c.contextMeta k)

/-- Context-level frame law: an insertion at `k` leaves a physically distinct `j` alone. -/
theorem scopedContext_insert_frame (ops : RealmStoreOps M Store)
    (c : ScopedContext M Meta Store) (k : K) (v : V k) {j : K}
    (h : PhysicalDistinct c.resolver k j) :
    scopedLookup ops c.resolver (scopedInsert ops c.resolver c.realms k v) j =
      scopedLookup ops c.resolver c.realms j :=
  scopedLookup_insert_frame ops c.resolver c.realms k v h

end ScopedContext

/-! ### Provider adapter boundary -/

section ProviderAdapter

variable {K : Type u} {V : K → Type v} {Meta : K → Type y}
variable {M : RealmModel K V}

/-- Provider behavior is an explicit adapter, not implied by storage metadata. -/
structure ProviderAdapter (M : RealmModel K V) (Meta : K → Type y) where
  apply : (k : K) → Meta k → V k → V k

/-- Effective provider metadata: declared first, context second. -/
def effectiveMeta (A : MetaAlgebra K Meta)
    (declared inherited : (k : K) → Meta k) (k : K) : Meta k :=
  A.merge k (declared k) (inherited k)

/-- The context operand has precedence whenever it is present. -/
theorem effectiveMeta_context_precedence (A : MetaAlgebra K Meta) (P : MetadataPrecedence A)
    (declared inherited : (k : K) → Meta k) {k : K} (hp : P.present k (inherited k)) :
    effectiveMeta A declared inherited k = inherited k :=
  P.right_wins k (declared k) (inherited k) hp

/-- Provider application combines declared and inherited metadata through the algebra. -/
def provideWith (A : MetaAlgebra K Meta) (adapter : ProviderAdapter M Meta)
    (declared inherited : (k : K) → Meta k) (k : K) (v : V k) : V k :=
  adapter.apply k (effectiveMeta A declared inherited k) v

/-- Provider application sees exactly the inherited metadata when it is present. -/
theorem provideWith_context_precedence (A : MetaAlgebra K Meta) (P : MetadataPrecedence A)
    (adapter : ProviderAdapter M Meta)
    (declared inherited : (k : K) → Meta k) {k : K} (v : V k)
    (hp : P.present k (inherited k)) :
    provideWith A adapter declared inherited k v = adapter.apply k (inherited k) v := by
  unfold provideWith
  rw [effectiveMeta_context_precedence A P declared inherited hp]

/-- With neutral inherited metadata, provider application sees exactly the declared metadata. -/
theorem provideWith_neutral_context (A : MetaAlgebra K Meta) (adapter : ProviderAdapter M Meta)
    (declared : (k : K) → Meta k) (k : K) (v : V k) :
    provideWith A adapter declared A.empty k v = adapter.apply k (declared k) v := by
  unfold provideWith effectiveMeta
  rw [A.right_id]

/-- Provider application stays within the selected logical key's value family and metadata. -/
theorem provideWith_key_local (A : MetaAlgebra K Meta) (adapter : ProviderAdapter M Meta)
    {declared inherited declared' inherited' : (k : K) → Meta k} {k : K} (v : V k)
    (hd : declared k = declared' k) (hi : inherited k = inherited' k) :
    provideWith A adapter declared inherited k v = provideWith A adapter declared' inherited' k v := by
  unfold provideWith effectiveMeta
  rw [hd, hi]

end ProviderAdapter

end

end STC.Scoped
