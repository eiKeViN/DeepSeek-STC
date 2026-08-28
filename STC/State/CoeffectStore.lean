module

public import Mathlib.Data.Finmap
public import STC.Foundation.Relation

/-!
# The ADR-02 dependent coeffect store

`Store Value` is the authoritative dependent `Finmap` façade from ADR-02.  It
is intentionally separate from `STC.RegistryLike`: a registry stores uniform
fiber cells, while this store maps each key `k` to a value of the dependent
type `Value k`.  This module exposes only the proof-facing map operations and
their lookup laws; binding protocols, notification, and active-table
aggregation remain later work.

## Main declarations

* `Store`: the authoritative dependent `Finmap` façade.
* `lookup`, `keys`, `insert`, and `erase`: proof-facing map operations.
* `StoreObs`: pointwise dependent, tag-strict observation.
-/

universe u v

namespace STC.Coeffect

@[expose] public section

variable {K : Type u} {Value : K → Type v}

/-- The finite dependent coeffect store selected by ADR-02. -/
abbrev Store (Value : K → Type v) := Finmap Value

/-! The executable operations require only key decidable equality. -/

def lookup [DecidableEq K] (key : K) (store : Store Value) : Option (Value key) :=
  Finmap.lookup key store

def keys (store : Store Value) : Finset K :=
  Finmap.keys store

def insert [DecidableEq K] (key : K) (value : Value key) (store : Store Value) : Store Value :=
  Finmap.insert key value store

def erase [DecidableEq K] (key : K) (store : Store Value) : Store Value :=
  Finmap.erase key store

@[simp]
theorem coeffect_lookup_empty [DecidableEq K] (key : K) :
    lookup key (∅ : Store Value) = none := by
  rfl

theorem coeffect_mem_keys_iff [DecidableEq K] (store : Store Value) (key : K) :
    key ∈ keys store ↔ (lookup key store).isSome := by
  change key ∈ Finmap.keys store ↔ (Finmap.lookup key store).isSome = true
  rw [Finmap.mem_keys]
  exact (Finmap.lookup_isSome (s := store) (a := key)).symm

@[simp]
theorem coeffect_lookup_insert [DecidableEq K] (key : K) (value : Value key)
    (store : Store Value) :
    lookup key (insert key value store) = some value := by
  exact Finmap.lookup_insert store

theorem coeffect_lookup_insert_ne [DecidableEq K] {key key' : K} (h : key' ≠ key)
    (value : Value key) (store : Store Value) :
    lookup key' (insert key value store) = lookup key' store := by
  exact Finmap.lookup_insert_of_ne store h

@[simp]
theorem coeffect_lookup_erase [DecidableEq K] (key : K) (store : Store Value) :
    lookup key (erase key store) = none := by
  exact Finmap.lookup_erase key store

theorem coeffect_lookup_erase_ne [DecidableEq K] {key key' : K} (h : key ≠ key')
    (store : Store Value) :
    lookup key (erase key' store) = lookup key store := by
  exact Finmap.lookup_erase_ne h

/-! ### Pointwise dependent observation -/

/-- Store observation preserves definedness and relates values key by key. -/
def StoreObs [DecidableEq K] (keyObs : ∀ key, RelSpec (Value key))
    (left right : Store Value) : Prop :=
  ∀ key, OptionRel (keyObs key).rel (lookup key left) (lookup key right)

theorem storeObs_lookup [DecidableEq K]
    {keyObs : ∀ key, RelSpec (Value key)}
    {left right : Store Value} (h : StoreObs keyObs left right) (key : K) :
    OptionRel (keyObs key).rel (lookup key left) (lookup key right) :=
  h key

theorem coeffectStoreObs_same_keys [DecidableEq K]
    {keyObs : ∀ key, RelSpec (Value key)}
    {left right : Store Value} (h : StoreObs keyObs left right) :
    keys left = keys right := by
  apply Finset.ext
  intro key
  rw [coeffect_mem_keys_iff, coeffect_mem_keys_iff]
  exact optionRel_isSome_iff (h := h key)

/-- The pointwise dependent store relation is an explicit equivalence value. -/
def storeObsSpec [DecidableEq K] (keyObs : ∀ key, RelSpec (Value key)) :
    RelSpec (Store Value) where
  rel := StoreObs keyObs
  refl := by
    intro store key
    exact (optionRelSpec (keyObs key)).refl (lookup key store)
  symm := by
    intro left right h key
    exact (optionRelSpec (keyObs key)).symm (h key)
  trans := by
    intro left middle right h₁ h₂ key
    exact (optionRelSpec (keyObs key)).trans (h₁ key) (h₂ key)

end

end STC.Coeffect
