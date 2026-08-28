/-!
  ADR-10: scoped coeffect and realm architecture.

  This is a standalone architecture spike.  It deliberately does not import
  ADR-02's Finmap or any P5 State implementation.  The semantic resolver is a
  proposition-valued relation; the executable resolver chooses a total,
  type-preserving RealmRef and records finite override support.  A persistent
  context combines that resolver with an abstract realm-store interface and
  per-key interception metadata.

  The finite Toy at the end uses Bool keys and Nat values.  It demonstrates
  identity resolution, typed lookup/update/erase, metadata right precedence,
  and the one-way flat embedding.  Lifecycle, control, and runtime/refinement
  semantics are intentionally outside this spike.
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option pp.unicode.fun true

universe u v w x y

namespace STCADR10

/-! ## 1. Typed realms and the two resolver layers -/

section TypedResolver

variable {K : Type u} {V : K → Type v}

/-- A model relates physical realm tokens to logical keys. -/
structure RealmModel (K : Type u) (V : K → Type v) where
  realmType : Type w
  keyOf : realmType → K
  default : (k : K) → realmType
  default_key : ∀ k, keyOf (default k) = k

variable {M : RealmModel K V} {k : K}
variable [DecidableEq K]

/-- A resolved realm carries the equality needed to transport dependent values. -/
structure RealmRef (M : RealmModel K V) (k : K) where
  token : M.realmType
  key_eq : M.keyOf token = k

/-- Transport a value from the physical key of a token to its logical key. -/
def RealmRef.cast (r : RealmRef M k) : V (M.keyOf r.token) → V k :=
  fun value => Eq.mp (congrArg V r.key_eq) value

/-- Transport a logical value back to the physical value type of a token. -/
def RealmRef.castInv (r : RealmRef M k) : V k → V (M.keyOf r.token) :=
  fun value => Eq.mpr (congrArg V r.key_eq) value

/-- The model-provided default reference for a logical key. -/
def defaultRef (M : RealmModel K V) (k : K) : RealmRef M k :=
  { token := M.default k
    key_eq := M.default_key k }

/-- A semantic resolver specification; it need not choose one implementation. -/
def ResolverSpec (M : RealmModel K V) :=
  ∀ (k : K), RealmRef M k → Prop

/-- An executable resolver chooses one typed realm and has finite override support. -/
structure Resolver (M : RealmModel K V) [DecidableEq K] where
  resolve : (k : K) → RealmRef M k
  overrideKeys : Finset K
  finite_support :
    ∀ {k}, k ∉ overrideKeys →
      (resolve k).token = (defaultRef M k).token

/-- The type-preservation proposition exposed by every executable resolver. -/
def ResolverTypePreserving (ρ : Resolver M) : Prop :=
  ∀ k, M.keyOf (ρ.resolve k).token = k

/-- A selected executable resolver refines a semantic resolver specification. -/
def ResolverSatisfies (ρ : Resolver M) (spec : ResolverSpec M) : Prop :=
  ∀ k, spec k (ρ.resolve k)

theorem resolver_type_preserving (ρ : Resolver M) :
    ResolverTypePreserving ρ := by
  intro k
  exact (ρ.resolve k).key_eq

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

end TypedResolver

/-! ## 2. Abstract realm store and scoped operations -/

section RealmStore

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {Store : Type x}
variable [DecidableEq K]

/-- Proof-facing operations for a realm-indexed dependent store.

    ADR-02's finite dependent map may instantiate this interface later. -/
structure RealmStoreOps (M : RealmModel K V) (Store : Type x) where
  empty : Store
  lookup : Store → (r : M.realmType) → Option (V (M.keyOf r))
  insert : Store → (r : M.realmType) → V (M.keyOf r) → Store
  erase : Store → M.realmType → Store
  lookup_empty : ∀ r, lookup empty r = none
  lookup_insert_same :
    ∀ (s : Store) (r : M.realmType) (v : V (M.keyOf r)),
      lookup (insert s r v) r = some v
  lookup_insert_other :
    ∀ (s : Store) (r : M.realmType) (v : V (M.keyOf r)) (q : M.realmType),
      q ≠ r → lookup (insert s r v) q = lookup s q
  lookup_erase_same :
    ∀ (s : Store) (r : M.realmType),
      lookup (erase s r) r = none
  lookup_erase_other :
    ∀ (s : Store) (r q : M.realmType),
      q ≠ r → lookup (erase s r) q = lookup s q

/-- A scoped lookup resolves once and transports through the captured witness. -/
def scopedLookup (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) : Option (V k) :=
  let rr := ρ.resolve k
  (ops.lookup s rr.token).map (RealmRef.cast rr)

/-- A scoped insertion stores a logical value at the selected physical token. -/
def scopedInsert (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) (value : V k) : Store :=
  let rr := ρ.resolve k
  ops.insert s rr.token (RealmRef.castInv rr value)

/-- A scoped erase selects the physical token once at the call boundary. -/
def scopedErase (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) : Store :=
  let rr := ρ.resolve k
  ops.erase s rr.token

/-- Physical noninterference is a premise, not a consequence of key inequality. -/
def PhysicalDistinct (ρ : Resolver M) (k j : K) : Prop :=
  (ρ.resolve k).token ≠ (ρ.resolve j).token

end RealmStore

/-! ## 3. Metadata, interception, and persistent derived contexts -/

section Context

variable {K : Type u} {V : K → Type v} {Meta : K → Type y}
variable [DecidableEq K]
variable {M : RealmModel K V} {Store : Type x}

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

/-- A finite interception specification keeps presence separate from metadata. -/
structure InterceptionSpec (K : Type u) (Meta : K → Type y)
    [DecidableEq K] where
  at : (k : K) → Option (Meta k)
  support : Finset K
  support_sound :
    ∀ {k : K} {m : Meta k}, at k = some m → k ∈ support
  support_complete :
    ∀ {k : K}, k ∈ support → ∃ m : Meta k, at k = some m

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
        (match spec.at k with
        | some m => m
        | none => A.empty k) }

/-- Effective provider metadata: declared first, context second. -/
def effectiveMeta (A : MetaAlgebra K Meta)
    (declared inherited : (k : K) → Meta k) (k : K) : Meta k :=
  A.merge k (declared k) (inherited k)

theorem deriveIsolate_persistent (u : ResolverUpdate M)
    (c : ScopedContext M Meta Store) (k : K) (rr : RealmRef M k) :
    (deriveIsolate u c k rr).realms = c.realms ∧
      (deriveIsolate u c k rr).contextMeta = c.contextMeta := by
  exact ⟨rfl, rfl⟩

theorem deriveIntercept_persistent (A : MetaAlgebra K Meta)
    (c : ScopedContext M Meta Store)
    (spec : InterceptionSpec K Meta) :
    (deriveIntercept A c spec).resolver = c.resolver ∧
      (deriveIntercept A c spec).realms = c.realms := by
  exact ⟨rfl, rfl⟩

/-- Provider behavior is an explicit adapter, not implied by storage metadata. -/
structure ProviderAdapter (M : RealmModel K V) (Meta : K → Type y) where
  apply : (k : K) → Meta k → V k → V k

end Context

/-! ## 4. One-way flat embedding contract -/

section FlatEmbedding

variable {K : Type u} {V : K → Type v}
variable [DecidableEq K]

/-- A flat-to-scoped embedding with lookup, insert, and erase commuting laws. -/
structure FlatEmbedding (M : RealmModel K V)
    (FlatStore ScopedStore : Type x)
    (ops : RealmStoreOps M ScopedStore)
    (ρ : Resolver M) [DecidableEq K] where
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

end FlatEmbedding

/-! ## 5. Finite executable Toy -/

section Toy

abbrev ToyKey := Bool
abbrev ToyValue (_ : ToyKey) := Nat

def toyModel : RealmModel ToyKey ToyValue where
  realmType := Bool
  keyOf := fun r => r
  default := fun k => k
  default_key := by
    intro k
    rfl

def toyResolver : Resolver toyModel where
  resolve := fun k => defaultRef toyModel k
  overrideKeys := ∅
  finite_support := by
    intro k hk
    rfl

def toyIdentitySpec : ResolverSpec toyModel :=
  fun k rr => rr.token = k

example : ResolverSatisfies toyResolver toyIdentitySpec := by
  intro k
  rfl

theorem toy_resolver_type_preserving :
    ResolverTypePreserving toyResolver := by
  exact resolver_type_preserving toyResolver

abbrev ToyStore := ToyKey → Option Nat

def toyLookup (s : ToyStore) (r : ToyKey) : Option (ToyValue (toyModel.keyOf r)) :=
  s r

def toyInsert (s : ToyStore) (r : ToyKey) (v : ToyValue (toyModel.keyOf r)) : ToyStore :=
  fun q => if q = r then some v else s q

def toyErase (s : ToyStore) (r : ToyKey) : ToyStore :=
  fun q => if q = r then none else s q

def toyStoreOps : RealmStoreOps toyModel ToyStore where
  empty := fun _ => none
  lookup := toyLookup
  insert := toyInsert
  erase := toyErase
  lookup_empty := by
    intro r
    rfl
  lookup_insert_same := by
    intro s r v
    simp [toyLookup, toyInsert]
  lookup_insert_other := by
    intro s r v q h
    simp [toyLookup, toyInsert, h]
  lookup_erase_same := by
    intro s r
    simp [toyLookup, toyErase]
  lookup_erase_other := by
    intro s r q h
    simp [toyLookup, toyErase, h]

example (s : ToyStore) (k : ToyKey) (v : Nat) :
    toyLookup (toyInsert s k v) k = some v := by
  simp [toyLookup, toyInsert]

example (s : ToyStore) (k : ToyKey) :
    toyLookup (toyErase s k) k = none := by
  simp [toyLookup, toyErase]

abbrev ToyMeta (_ : ToyKey) := Option Nat

def toyMetaAlg : MetaAlgebra ToyKey ToyMeta where
  empty := fun _ => none
  merge := fun _ old new =>
    match new with
    | some n => some n
    | none => old
  left_id := by
    intro k x
    cases x <;> rfl
  right_id := by
    intro k x
    rfl
  assoc := by
    intro k x y z
    cases x <;> cases y <;> cases z <;> rfl

def toyMetaPrecedence : MetadataPrecedence toyMetaAlg where
  present := fun _ m => ∃ n, m = some n
  right_wins := by
    intro k old new h
    rcases h with ⟨n, rfl⟩
    rfl

example : toyMetaAlg.merge false (some 1) (some 2) = some 2 := by
  rfl

def toyEmpty : ToyStore := fun _ => none

def toyContext : ScopedContext toyModel ToyMeta ToyStore where
  resolver := toyResolver
  realms := toyEmpty
  contextMeta := fun _ => none

def emptyToyInterception : InterceptionSpec ToyKey ToyMeta where
  at := fun _ => none
  support := ∅
  support_sound := by
    intro k m h
    cases h
  support_complete := by
    intro k hk
    exact False.elim (by simpa using hk)

example :
    (deriveIntercept toyMetaAlg toyContext emptyToyInterception).resolver =
      toyContext.resolver := by
  rfl

example :
    (deriveIntercept toyMetaAlg toyContext emptyToyInterception).realms =
      toyContext.realms := by
  rfl

def toyFlatEmbedding :
    FlatEmbedding toyModel ToyStore ToyStore toyStoreOps toyResolver where
  embed := id
  flatLookup := toyLookup
  flatInsert := toyInsert
  flatErase := toyErase
  embed_lookup := by
    intro s k
    simp [scopedLookup, toyResolver, defaultRef, toyStoreOps,
      toyLookup, RealmRef.cast]
  embed_insert := by
    intro s k v
    simp [scopedInsert, toyResolver, defaultRef, toyStoreOps,
      toyInsert, RealmRef.castInv]
  embed_erase := by
    intro s k
    simp [scopedErase, toyResolver, defaultRef, toyStoreOps, toyErase]

example (s : ToyStore) (k : ToyKey) :
    scopedLookup toyStoreOps toyResolver
        (scopedErase toyStoreOps toyResolver s k) k = none := by
  simp [scopedLookup, scopedErase, toyResolver, defaultRef,
    toyStoreOps, toyErase, RealmRef.cast]

#eval toyLookup (toyInsert toyEmpty true 7) true
#eval toyLookup (toyErase (toyInsert toyEmpty true 7) true) true

end Toy

end STCADR10
