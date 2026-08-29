module

public import STC.Scoped

/-!
# Finite scoped-coeffect evidence

The P12-T06 finite deterministic evidence over the two-key toy model from
`STC.Scoped.Model`.  It exercises default realm resolution, a `depB` resolver
override with a miss at `cache`, two realms under one logical key remaining
physically distinct, scoped insert/lookup/erase and both frame cases over the
authoritative P5 `Finmap` store, right-biased metadata precedence under
interception, persistent `deriveIsolate`/`deriveIntercept` behavior, and the
one-way flat embedding under the ADR conditions (identity resolver, no
aliasing).

This module is evidence only: production modules never import it.

## Main declarations

* `depBResolver`: the finite override resolver;
* `toyOps`, `toyStore0`, `toyStore1`: the P5-backed scoped store fixture;
* `toyMeta`, `toyMetaAlg`, `toyMetaPrecedence`, `depInterception`,
  `toyContext`, `isolatedContext`: the metadata and context fixtures;
* `toyFlatModel`, `toyFlatOps`, `toyFlatEmbedding`: the identity flat model;
* `ScopedReport`, `scopedReport`, `expectedScopedReport`,
  `scopedReport_expected`: the pinned executable report.
-/

namespace STC.Examples.Scoped

open STC.Scoped

@[expose] public section

/-! ### Resolver evidence -/

section ResolverEvidence

/-- The override resolver: key `dep` resolves to the non-default `depB` realm. -/
def depBResolver : Resolver toyModel :=
  resolverUpdate defaultResolver .dep toyDepBRef

/-- The default reference of `dep`: the `depA` realm. -/
def depARef : RealmRef toyModel .dep :=
  RealmRef.defaultRef toyModel .dep

/-- The overridden reference of `dep`: the `depB` realm. -/
def depBRef : RealmRef toyModel .dep :=
  depBResolver.resolve .dep

/-- The overridden reference of `cache`: still its default realm. -/
def overriddenCacheRef : RealmRef toyModel .cache :=
  depBResolver.resolve .cache

/-- Default realm resolution: `dep` resolves to the default `depA` realm. -/
example : depARef.token = .depA := by
  rfl

/-- The update hits its key through the checked update law. -/
example :
    (resolverUpdate depBResolver .dep (depBResolver.resolve .dep)).resolve .dep =
      depBResolver.resolve .dep := by
  exact resolverUpdate_hit depBResolver .dep (depBResolver.resolve .dep)

/-- The overridden resolution selects the `depB` realm. -/
example : depBRef.token = .depB := by
  rfl

/-- The update misses other keys through the checked update law. -/
example :
    (resolverUpdate depBResolver .dep toyDepBRef).resolve .cache = depBResolver.resolve .cache := by
  exact resolverUpdate_miss depBResolver .dep toyDepBRef (by decide : ToyKey.cache ≠ ToyKey.dep)

/-- A miss still resolves `cache` to its default realm. -/
example : overriddenCacheRef.token = .cacheR := by
  rfl

/-- Finite support: the missed key resolves exactly to the model default reference. -/
theorem overriddenCacheRef_is_default :
    overriddenCacheRef = RealmRef.defaultRef toyModel .cache := by
  exact RealmRef.ext (depBResolver.finite_support (by decide : ToyKey.cache ∉ depBResolver.overrideKeys))

/-- The override support contains exactly the updated key. -/
example : .dep ∈ depBResolver.overrideKeys := by
  decide

/-- The override support excludes untouched keys. -/
example : .cache ∉ depBResolver.overrideKeys := by
  decide

/-- Two realms under one logical key remain distinct physical tokens. -/
example : toyDepARef.token ≠ toyDepBRef.token :=
  toy_same_key_realms_distinct

/-- The default and overridden resolutions of the same key are physically distinct. -/
example : depARef.token ≠ depBRef.token := by
  decide

/-- The updated resolver satisfies a specification admitting both the default references
and the installed override, through the checked satisfaction bridge. -/
theorem depBResolver_satisfies_defaultSpec :
    ResolverSatisfies depBResolver
      (fun k rr => rr.token = (RealmRef.defaultRef toyModel k).token ∨ k = .dep) := by
  exact resolverUpdate_satisfies (K := ToyKey) (M := toyModel) defaultResolver
    (fun k rr => rr.token = (RealmRef.defaultRef toyModel k).token ∨ k = .dep)
    toyDepBRef (resolverSatisfies_default (K := ToyKey) (M := toyModel) _
      (by intro k; left; rfl)) (by right; rfl)

end ResolverEvidence

/-! ### Scoped store evidence over the P5 store -/

section ScopedStoreEvidence

/-- The P5 `Finmap` adapter instance for the toy model. -/
def toyOps : RealmStoreOps toyModel (RealmStore toyModel) :=
  finmapRealmStoreOps

def toyStore0 : RealmStore toyModel := ∅

def toyStore1 : RealmStore toyModel :=
  scopedInsert toyOps depBResolver toyStore0 .dep 7

/-- Scoped insert followed by scoped lookup returns the inserted value. -/
example : scopedLookup toyOps depBResolver toyStore1 .dep = some 7 := by
  exact scopedLookup_insert_self toyOps depBResolver toyStore0 .dep 7

/-- Scoped insert followed by scoped erase leaves the binding absent. -/
example :
    scopedLookup toyOps depBResolver (scopedErase toyOps depBResolver toyStore1 .dep) .dep = none := by
  exact scopedLookup_erase_self toyOps depBResolver toyStore1 .dep

/-- Frame law for two distinct logical keys under one resolver. -/
example (s : RealmStore toyModel) :
    scopedLookup toyOps depBResolver (scopedInsert toyOps depBResolver s .dep 7) .cache =
      scopedLookup toyOps depBResolver s .cache := by
  exact scopedLookup_insert_frame toyOps depBResolver s .dep 7
    (physicalDistinct_of_ne depBResolver (by decide : ToyKey.dep ≠ ToyKey.cache))

/-- Frame law for two realms under one logical key: an insertion through the `depB`
realm does not disturb a lookup through the default `depA` realm. -/
example (s : RealmStore toyModel) :
    scopedLookup toyOps defaultResolver (scopedInsert toyOps depBResolver s .dep 7) .dep =
      scopedLookup toyOps defaultResolver s .dep := by
  exact scopedLookup_insert_frame_twoResolvers toyOps depBResolver defaultResolver s .dep 7
    (by decide)

/-- The captured insertion inverse erases exactly the selected token. -/
example (s : RealmStore toyModel) :
    (scopedInsertInverse toyOps depBResolver .dep).undo s =
      Coeffect.erase (depBResolver.resolve .dep).token s := by
  rfl

/-- Undoing an insertion over a previously absent realm restores the empty store. -/
example :
    (scopedInsertInverse toyOps depBResolver .dep).undo
        (scopedInsert toyOps depBResolver toyStore0 .dep 7) = toyStore0 := by
  exact finmap_scopedInsertInverse_restores depBResolver toyStore0 .dep 7 (by rfl)

/-- The erase inverse captures exactly the value visible at operation time. -/
example :
    (scopedEraseInverse toyOps depBResolver toyStore1 .dep).restored =
      scopedLookup toyOps depBResolver toyStore1 .dep := by
  rfl

/-- Undoing an erase over a present binding restores the store. -/
example :
    (scopedEraseInverse toyOps depBResolver toyStore1 .dep).undo
        (scopedErase toyOps depBResolver toyStore1 .dep) = toyStore1 := by
  exact finmap_scopedEraseInverse_restores depBResolver toyStore1 .dep
    (Coeffect.coeffect_lookup_insert .depB (RealmRef.castInv (depBResolver.resolve .dep) 7) toyStore0)

end ScopedStoreEvidence

/-! ### Metadata and context evidence -/

section ContextEvidence

/-- Dependent toy metadata: `Option Nat` for `dep`, `Option Bool` for `cache`. -/
abbrev toyMeta : ToyKey → Type
  | .dep => Option Nat
  | .cache => Option Bool

/-- The neutral inherited metadata: nothing present at any key. -/
def neutralToyMeta : (k : ToyKey) → toyMeta k :=
  fun k =>
    match k with
    | .dep => none
    | .cache => none

/-- The right-biased toy metadata algebra. -/
def toyMetaAlg : MetaAlgebra ToyKey toyMeta where
  empty := by
    intro k
    cases k <;> exact none
  merge := by
    intro k old new
    cases k <;> exact (match new with
      | some m => some m
      | none => old)
  left_id := by
    intro k x
    cases k <;> cases x <;> rfl
  right_id := by
    intro k x
    cases k <;> rfl
  assoc := by
    intro k x y z
    cases k <;> cases x <;> cases y <;> cases z <;> rfl

/-- Toy metadata presence: the payload is a `some`. -/
def toyMetaPresent (k : ToyKey) (m : toyMeta k) : Prop :=
  match k with
  | .dep => ∃ n : Nat, m = some n
  | .cache => ∃ b : Bool, m = some b

/-- The explicit right-priority law for the toy algebra. -/
def toyMetaPrecedence : MetadataPrecedence toyMetaAlg where
  present := toyMetaPresent
  right_wins := by
    intro k old new h
    cases k
    · rcases h with ⟨n, rfl⟩
      rfl
    · rcases h with ⟨n, rfl⟩
      rfl

/-- A finite interception installing metadata `some 5` at `dep` and nothing at `cache`. -/
def depInterception : InterceptionSpec ToyKey toyMeta where
  atKey := fun k =>
    match k with
    | .dep => some (some 5)
    | .cache => none
  support := {.dep}
  support_sound := by
    intro k m h
    cases k
    · simp
    · cases h
  support_complete := by
    intro k hk
    simp at hk
    subst k
    exact ⟨some 5, rfl⟩

/-- The finite scoped context: override resolver, empty realm store, neutral metadata. -/
def toyContext : ScopedContext toyModel toyMeta (RealmStore toyModel) where
  resolver := depBResolver
  realms := toyStore0
  contextMeta := neutralToyMeta

/-- The pinned update interface for the toy model. -/
def toyResolverUpdateOps : ResolverUpdate toyModel :=
  defaultResolverUpdate

/-- The derived isolation context: `cache` re-resolves to its default realm. -/
def isolatedContext : ScopedContext toyModel toyMeta (RealmStore toyModel) :=
  deriveIsolate toyResolverUpdateOps toyContext .cache (RealmRef.defaultRef toyModel .cache)

/-- Isolation hits the selected key. -/
example : (isolatedContext.resolver.resolve .cache).token = .cacheR := by
  rfl

/-- Isolation preserves the untouched resolver keys through the checked update law. -/
example : (isolatedContext.resolver.resolve .dep) = toyContext.resolver.resolve .dep := by
  exact deriveIsolate_resolver_miss toyResolverUpdateOps toyContext .cache
    (RealmRef.defaultRef toyModel .cache) (by decide : ToyKey.dep ≠ ToyKey.cache)

/-- Isolation leaves the realm store and metadata definitionally unchanged. -/
example :
    isolatedContext.realms = toyContext.realms ∧ isolatedContext.contextMeta = toyContext.contextMeta := by
  exact deriveIsolate_persistent toyResolverUpdateOps toyContext .cache (RealmRef.defaultRef toyModel .cache)

/-- A present interception payload wins over the inherited metadata by right precedence. -/
example :
    (deriveIntercept toyMetaAlg toyContext depInterception).contextMeta .dep = some 5 := by
  exact deriveIntercept_merge_present toyMetaAlg toyMetaPrecedence toyContext depInterception
    (by rfl) (by
      show ∃ n : Nat, (some 5 : toyMeta .dep) = some n
      exact ⟨5, rfl⟩)

/-- An absent interception payload leaves the inherited metadata unchanged. -/
example :
    (deriveIntercept toyMetaAlg toyContext depInterception).contextMeta .cache = none := by
  exact deriveIntercept_merge_absent toyMetaAlg toyContext depInterception (by rfl)

/-- Interception leaves the resolver and realm store definitionally unchanged. -/
example :
    (deriveIntercept toyMetaAlg toyContext depInterception).resolver = toyContext.resolver ∧
      (deriveIntercept toyMetaAlg toyContext depInterception).realms = toyContext.realms := by
  exact deriveIntercept_persistent toyMetaAlg toyContext depInterception

/-- The provider adapter: present metadata replaces the raw value. -/
def toyAdapter : ProviderAdapter toyModel toyMeta where
  apply := by
    intro k m v
    cases k <;> exact (match m with
      | some x => x
      | none => v)

/-- With neutral inherited metadata, provider application sees only the declared metadata. -/
example (v : ToyValue .dep) :
    provideWith toyMetaAlg toyAdapter neutralToyMeta neutralToyMeta .dep v = v := by
  exact provideWith_neutral_context toyMetaAlg toyAdapter neutralToyMeta .dep v

/-- Present inherited metadata takes precedence over declared metadata. -/
example (v : ToyValue .dep) :
    provideWith toyMetaAlg toyAdapter neutralToyMeta
        (fun k => match k with | .dep => some 9 | .cache => none) .dep v = 9 := by
  exact provideWith_context_precedence toyMetaAlg toyMetaPrecedence toyAdapter neutralToyMeta
    (fun k => match k with | .dep => some 9 | .cache => none) v (by
      show ∃ n : Nat, (some 9 : toyMeta .dep) = some n
      exact ⟨9, rfl⟩)

end ContextEvidence

/-! ### Flat embedding evidence -/

section FlatEvidence

/-- The identity flat model: one realm per logical key, no aliasing. -/
abbrev toyFlatModel : RealmModel ToyKey ToyValue where
  Realm := ToyKey
  keyOf := fun k => k
  default := fun k => k
  default_key := by
    intro k
    rfl

abbrev ToyFlatStore := RealmStore toyFlatModel

/-- The P5 `Finmap` adapter for the identity flat model. -/
def toyFlatOps : RealmStoreOps toyFlatModel ToyFlatStore :=
  finmapRealmStoreOps

/-- The one-way flat embedding under the identity resolver: embed is the identity. -/
def toyFlatEmbedding : FlatEmbedding toyFlatModel ToyFlatStore ToyFlatStore
    toyFlatOps defaultResolver where
  embed := id
  flatLookup := fun s k => Coeffect.lookup k s
  flatInsert := fun s k v => Coeffect.insert k v s
  flatErase := fun s k => Coeffect.erase k s
  embed_lookup := by
    intro s k
    unfold scopedLookup
    change (Coeffect.lookup k s).map (fun v => v) = Coeffect.lookup k s
    cases Coeffect.lookup k s <;> rfl
  embed_insert := by
    intro s k v
    unfold scopedInsert
    rfl
  embed_erase := by
    intro s k
    unfold scopedErase
    rfl

def flatStore0 : ToyFlatStore := ∅

def flatStore1 : ToyFlatStore :=
  Coeffect.insert .dep 7 flatStore0

/-- Lookup through the embedding agrees with the flat lookup. -/
example : scopedLookup toyFlatOps defaultResolver flatStore1 .dep = some 7 := by
  decide

/-- Insertion through the embedding then lookup returns the inserted value. -/
example :
    scopedLookup toyFlatOps defaultResolver (scopedInsert toyFlatOps defaultResolver flatStore0 .dep 7) .dep = some 7 := by
  decide

/-- Erasure through the embedding leaves the binding absent. -/
example :
    scopedLookup toyFlatOps defaultResolver (scopedErase toyFlatOps defaultResolver flatStore1 .dep) .dep = none := by
  decide

/-- The derived commuting-diagram law on the image. -/
example :
    scopedLookup toyFlatOps defaultResolver
        (toyFlatEmbedding.embed (Coeffect.insert .dep 7 flatStore0)) .dep = some 7 := by
  exact flatEmbedding_lookup_insert toyFlatEmbedding flatStore0 .dep 7

/-- The derived erase diagram on the image. -/
example :
    scopedLookup toyFlatOps defaultResolver
        (toyFlatEmbedding.embed (Coeffect.erase .dep flatStore1)) .dep = none := by
  exact flatEmbedding_lookup_erase toyFlatEmbedding flatStore1 .dep

/-- The flat store is inside the embedding's image. -/
example : FlatImage toyFlatEmbedding flatStore1 := by
  exact flatImage_self toyFlatEmbedding flatStore1

/-- Scoped updates on the image stay inside the image. -/
example : FlatImage toyFlatEmbedding (scopedInsert toyFlatOps defaultResolver flatStore1 .dep 8) := by
  exact flatImage_scopedInsert toyFlatEmbedding flatStore1 .dep 8

end FlatEvidence

/-! ### Pinned executable report -/

section ExecutableReport

/-- Compare two toy realms as plain `ToyRealm` values. -/
def toyTokenEq (a b : ToyRealm) : Bool :=
  decide (a = b)

/-- The finite report carrying every P12-T06 outcome. -/
structure ScopedReport where
  defaultDepToken : ToyRealm
  overrideDepToken : ToyRealm
  overrideMissToken : ToyRealm
  overrideSupportDep : Bool
  overrideSupportCache : Bool
  sameKeyRealmsDistinct : Bool
  depInsertLookup : Option Nat
  depInsertEraseLookup : Option Nat
  cacheFrameLookup : Option Bool
  sameKeyFrameLookup : Option Nat
  interceptDepMeta : Option Nat
  interceptCacheMeta : Option Bool
  providerNeutralValue : Nat
  providerPrecedenceValue : Nat
  flatDepLookup : Option Nat
  flatEraseLookup : Option Nat
  deriving DecidableEq, Repr

/-- Evaluate all P12-T06 outcomes. -/
def scopedReport : ScopedReport :=
  { defaultDepToken := depARef.token
    overrideDepToken := depBRef.token
    overrideMissToken := overriddenCacheRef.token
    overrideSupportDep := decide (.dep ∈ depBResolver.overrideKeys)
    overrideSupportCache := decide (.cache ∉ depBResolver.overrideKeys)
    sameKeyRealmsDistinct := !toyTokenEq depARef.token depBRef.token
    depInsertLookup := scopedLookup toyOps depBResolver toyStore1 .dep
    depInsertEraseLookup :=
      scopedLookup toyOps depBResolver (scopedErase toyOps depBResolver toyStore1 .dep) .dep
    cacheFrameLookup :=
      scopedLookup toyOps depBResolver (scopedInsert toyOps depBResolver toyStore0 .dep 7) .cache
    sameKeyFrameLookup :=
      scopedLookup toyOps defaultResolver (scopedInsert toyOps depBResolver toyStore0 .dep 7) .dep
    interceptDepMeta := (deriveIntercept toyMetaAlg toyContext depInterception).contextMeta .dep
    interceptCacheMeta := (deriveIntercept toyMetaAlg toyContext depInterception).contextMeta .cache
    providerNeutralValue := provideWith toyMetaAlg toyAdapter neutralToyMeta neutralToyMeta .dep 3
    providerPrecedenceValue :=
      provideWith toyMetaAlg toyAdapter neutralToyMeta
        (fun k => match k with | .dep => some 9 | .cache => none) .dep 3
    flatDepLookup := scopedLookup toyFlatOps defaultResolver flatStore1 .dep
    flatEraseLookup :=
      scopedLookup toyFlatOps defaultResolver (scopedErase toyFlatOps defaultResolver flatStore1 .dep) .dep }

/-- The exact expected output of `scopedReport`. -/
def expectedScopedReport : ScopedReport :=
  { defaultDepToken := .depA
    overrideDepToken := .depB
    overrideMissToken := .cacheR
    overrideSupportDep := true
    overrideSupportCache := true
    sameKeyRealmsDistinct := true
    depInsertLookup := some 7
    depInsertEraseLookup := none
    cacheFrameLookup := none
    sameKeyFrameLookup := none
    interceptDepMeta := some 5
    interceptCacheMeta := none
    providerNeutralValue := 3
    providerPrecedenceValue := 9
    flatDepLookup := some 7
    flatEraseLookup := none }

/-- The finite report matches all intended outcomes. -/
theorem scopedReport_expected : scopedReport = expectedScopedReport := by
  decide

end ExecutableReport

end

end STC.Examples.Scoped
