import STC.State.RegistryLike

/-!
# Executable list registry

This module instantiates `RegistryLike` with a persistent association list and
a proof that keys are unique. Insertions remove an old key before adding its
replacement, while semantic comparison remains order-insensitive.

## Main declarations

* `ToyRegistry`: a list of bindings with a `Nodup` key certificate.
* `toyRegistryLike`: the checked `RegistryLike` instance.
* `toyExampleChecks`: finite positive and negative evidence.
-/

universe u

namespace STC

/-- A persistent association-list registry with unique keys. -/
structure ToyRegistry (K V : Type u) where
  entries : List (K × V)
  key_nodup : (entries.map Prod.fst).Nodup

variable {K V : Type u} [DecidableEq K]

/-- Look up the first binding for a key. -/
def toyLookup : List (K × V) → K → Option V
  | [], _ => none
  | (key, value) :: rest, query =>
      if query = key then some value else toyLookup rest query

/-- Remove every binding for a key. -/
def toyErase : List (K × V) → K → List (K × V)
  | [], _ => []
  | (key, value) :: rest, query =>
      if query = key then toyErase rest query else (key, value) :: toyErase rest query

/-- Replace a binding by erasing its old entry and adding the new one at the front. -/
def toyInsert (entries : List (K × V)) (key : K) (value : V) : List (K × V) :=
  (key, value) :: toyErase entries key

theorem toyLookup_cons_eq (entries : List (K × V)) (key : K) (value : V) :
    toyLookup ((key, value) :: entries) key = some value := by
  simp [toyLookup]

theorem toyLookup_cons_ne (entries : List (K × V))
    {key query : K} (value : V) (h : query ≠ key) :
    toyLookup ((key, value) :: entries) query = toyLookup entries query := by
  simp [toyLookup, h]

theorem toyErase_keys_subset (entries : List (K × V)) (query : K)
    {x : K} :
    x ∈ (toyErase entries query).map Prod.fst → x ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [toyErase]
  | cons head rest ih =>
      rcases head with ⟨headKey, headValue⟩
      by_cases h : query = headKey
      · simp only [toyErase]
        rw [if_pos h]
        intro hx
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih hx)
      · simp only [toyErase]
        rw [if_neg h]
        simp only [List.map_cons, List.mem_cons]
        intro hx
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (ih hx)

theorem toyErase_nodup (entries : List (K × V))
    (hkeys : (entries.map Prod.fst).Nodup) (query : K) :
    (toyErase entries query |>.map Prod.fst).Nodup := by
  induction entries with
  | nil => simp [toyErase]
  | cons head rest ih =>
      rcases head with ⟨headKey, headValue⟩
      have hrest : (rest.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hkeys).2
      by_cases h : query = headKey
      · simp only [toyErase]
        rw [if_pos h]
        exact ih hrest
      · simp only [toyErase]
        rw [if_neg h]
        simp only [List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro hx
          exact (List.nodup_cons.mp hkeys).1
            (toyErase_keys_subset rest query (x := headKey) hx)
        · exact ih hrest

theorem toyErase_key_not_mem (entries : List (K × V))
    (hkeys : (entries.map Prod.fst).Nodup) (query : K) :
    query ∉ (toyErase entries query).map Prod.fst := by
  induction entries with
  | nil => simp [toyErase]
  | cons head rest ih =>
      rcases head with ⟨headKey, headValue⟩
      have hrest : (rest.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hkeys).2
      by_cases h : query = headKey
      · simp only [toyErase]
        rw [if_pos h]
        exact ih hrest
      · simp only [toyErase]
        rw [if_neg h]
        simp only [List.map_cons, List.mem_cons]
        intro hx
        rcases hx with hx | hx
        · exact h hx
        · exact ih hrest hx

theorem toyLookup_none_of_not_mem (entries : List (K × V))
    {query : K} (h : query ∉ entries.map Prod.fst) :
    toyLookup entries query = none := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨headKey, headValue⟩
      have hhead : query ≠ headKey := by
        intro heq
        exact h (by simp [heq])
      have hrest : query ∉ rest.map Prod.fst := by
        intro hx
        exact h (by simp [hx])
      simp [toyLookup, hhead, ih hrest]

theorem toyLookup_some_iff_mem (entries : List (K × V)) (query : K) :
    (toyLookup entries query).isSome ↔ query ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [toyLookup]
  | cons head rest ih =>
      rcases head with ⟨headKey, headValue⟩
      by_cases h : query = headKey
      · simp [toyLookup, h]
      · simp [toyLookup, h, ih]

theorem toyLookup_erase_eq (entries : List (K × V))
    (hkeys : (entries.map Prod.fst).Nodup) (key : K) :
    toyLookup (toyErase entries key) key = none := by
  exact toyLookup_none_of_not_mem _ (toyErase_key_not_mem entries hkeys key)

theorem toyLookup_erase_ne (entries : List (K × V))
    {key query : K} (h : query ≠ key) :
    toyLookup (toyErase entries key) query = toyLookup entries query := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨headKey, headValue⟩
      by_cases hhead : key = headKey
      · have hq : query ≠ headKey := by
          intro hq
          exact h (hq.trans hhead.symm)
        rw [hhead] at ih
        simp [toyErase, toyLookup, hhead, hq, ih]
      · by_cases hq : query = headKey
        · simp [toyErase, toyLookup, hhead, hq]
        · simp [toyErase, toyLookup, hhead, hq, ih]

theorem toyInsert_nodup (entries : List (K × V))
    (hkeys : (entries.map Prod.fst).Nodup) (key : K) (value : V) :
    (toyInsert entries key value |>.map Prod.fst).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · exact toyErase_key_not_mem entries hkeys key
  · exact toyErase_nodup entries hkeys key

theorem toyLookup_insert_eq (entries : List (K × V))
    (_hkeys : (entries.map Prod.fst).Nodup) (key : K) (value : V) :
    toyLookup (toyInsert entries key value) key = some value := by
  simp [toyInsert, toyLookup]

theorem toyLookup_insert_ne (entries : List (K × V))
    {key query : K} (value : V) (h : query ≠ key) :
    toyLookup (toyInsert entries key value) query = toyLookup entries query := by
  simp only [toyInsert]
  rw [toyLookup_cons_ne (toyErase entries key) value h]
  exact toyLookup_erase_ne entries h

/-- The list-and-`Nodup` implementation of the abstract registry laws. -/
def toyRegistryLike : RegistryLike K V (ToyRegistry K V) where
  empty := ⟨[], by simp⟩
  lookup := fun registry key => toyLookup registry.entries key
  insert := fun registry key value =>
    ⟨toyInsert registry.entries key value,
      toyInsert_nodup registry.entries registry.key_nodup key value⟩
  erase := fun registry key =>
    ⟨toyErase registry.entries key,
      toyErase_nodup registry.entries registry.key_nodup key⟩
  domain := fun registry => registry.entries.map Prod.fst
  domain_nodup := fun registry => registry.key_nodup
  lookup_empty := by
    intro key
    rfl
  lookup_insert_eq := by
    intro registry key value
    exact toyLookup_insert_eq registry.entries registry.key_nodup key value
  lookup_insert_ne := by
    intro registry key query value h
    exact toyLookup_insert_ne registry.entries value h
  lookup_erase_eq := by
    intro registry key
    exact toyLookup_erase_eq registry.entries registry.key_nodup key
  lookup_erase_ne := by
    intro registry key query h
    exact toyLookup_erase_ne registry.entries h
  mem_domain_iff := by
    intro registry key
    exact (toyLookup_some_iff_mem registry.entries key).symm

/-! A finite fixture with three distinct keys and two values. -/

inductive ToyKey : Type
  | alpha
  | beta
  | gamma
  deriving DecidableEq, Repr

inductive ToyValue : Type
  | first
  | second
  deriving DecidableEq, Repr

/-- A nondegenerate registry fixture leaving `gamma` available as a fresh key. -/
def toyExample : ToyRegistry ToyKey ToyValue :=
  { entries :=
      [(.alpha, .first), (.beta, .second)]
    key_nodup := by decide }

def toyExampleFresh : Option (ToyRegistry ToyKey ToyValue) :=
  insertFresh? toyRegistryLike toyExample .alpha .second

def toyExampleFreshKey : Option (ToyRegistry ToyKey ToyValue) :=
  insertFresh? toyRegistryLike toyExample .gamma .second

def toyExampleErase : Option (ToyValue × ToyRegistry ToyKey ToyValue) :=
  erasePresent? toyRegistryLike toyExample .beta

def toyExampleNew : Option (ToyRegistry ToyKey ToyValue) :=
  insertFresh? toyRegistryLike
    (toyRegistryLike.insert toyExample .alpha .first) .gamma .second

def toyExampleChecks : List Bool :=
  [toyExampleFresh = none,
   toyExampleFreshKey ≠ none,
   toyExampleErase ≠ none,
   toyExampleNew ≠ none]

#eval toyExampleChecks

/-- All finite Toy registry checks have the intended outcomes. -/
theorem toyExampleChecks_expected : toyExampleChecks = [true, true, true, true] := by
  decide

end STC
