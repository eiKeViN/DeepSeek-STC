module

public import STC.Scoped.Resolver
public import STC.State.CoeffectStore

/-!
# Realm store adapter and scoped operations

The ADR-10 store layer.  `RealmStoreOps` is the proof-facing operation
interface over a realm-indexed dependent store; `RealmStore` and
`finmapRealmStoreOps` instantiate it over the authoritative P5 dependent
`Finmap` façade at the physical realm token type — no second authoritative
store is introduced.  `scopedLookup`/`scopedInsert`/`scopedErase` resolve a
logical key once, operate on the selected physical token, and transport values
through the captured `RealmRef` witness.

`PhysicalDistinct` is an explicit premise for the frame laws: logical-key
inequality implies it, but it is not defined as logical-key inequality, so two
keys that resolve to one realm (or two realms under one key) are handled at the
physical boundary.  `ScopedInsertInverse` and `ScopedEraseInverse` capture the
reference selected at application time; their rollback laws are proved at the
`Finmap` level and never re-resolve through a possibly changed resolver.

## Main declarations

* `RealmStoreOps`, `RealmStore`, `finmapRealmStoreOps`: the adapter boundary;
* `scopedLookup`, `scopedInsert`, `scopedErase`: the scoped operations;
* `scopedLookup_insert_self`, `scopedLookup_insert_frame`,
  `scopedLookup_erase_self`, `scopedLookup_erase_frame`, `scopedLookup_empty`;
* `PhysicalDistinct` with `physicalDistinct_of_ne` and `physicalDistinct_symm`;
* `ScopedInsertInverse`/`ScopedEraseInverse` with the captured-reference and
  `Finmap` restoration laws.
-/

universe u v w x

namespace STC.Scoped

@[expose] public section

/-! ### Abstract realm store operations -/

section RealmStoreOps

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {Store : Type x}

/-- Proof-facing operations for a realm-indexed dependent store.

ADR-02's dependent `Finmap` instantiates this interface in
`finmapRealmStoreOps`. -/
structure RealmStoreOps (M : RealmModel K V) (Store : Type x) where
  empty : Store
  lookup : Store → (r : M.Realm) → Option (V (M.keyOf r))
  insert : Store → (r : M.Realm) → V (M.keyOf r) → Store
  erase : Store → M.Realm → Store
  lookup_empty : ∀ r, lookup empty r = none
  lookup_insert_same :
    ∀ (s : Store) (r : M.Realm) (v : V (M.keyOf r)),
      lookup (insert s r v) r = some v
  lookup_insert_other :
    ∀ (s : Store) (r : M.Realm) (v : V (M.keyOf r)) (q : M.Realm),
      q ≠ r → lookup (insert s r v) q = lookup s q
  lookup_erase_same :
    ∀ (s : Store) (r : M.Realm),
      lookup (erase s r) r = none
  lookup_erase_other :
    ∀ (s : Store) (r q : M.Realm),
      q ≠ r → lookup (erase s r) q = lookup s q

end RealmStoreOps

/-! ### Scoped operations -/

section ScopedOps

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {Store : Type x}
variable [DecidableEq K]

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

/-- The empty store has no scoped binding. -/
theorem scopedLookup_empty (ops : RealmStoreOps M Store) (ρ : Resolver M) (k : K) :
    scopedLookup ops ρ ops.empty k = none := by
  simp [scopedLookup, ops.lookup_empty]

/-- Lookup after insertion at the same selected realm returns the inserted value. -/
theorem scopedLookup_insert_self (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) (v : V k) :
    scopedLookup ops ρ (scopedInsert ops ρ s k v) k = some v := by
  simp [scopedLookup, scopedInsert, ops.lookup_insert_same, RealmRef.cast_castInv]

/-- Lookup after erasure at the same selected realm returns none. -/
theorem scopedLookup_erase_self (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) :
    scopedLookup ops ρ (scopedErase ops ρ s k) k = none := by
  simp [scopedLookup, scopedErase, ops.lookup_erase_same]

end ScopedOps

/-! ### Physical distinctness -/

section PhysicalDistinct

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq K]

/-- Physical noninterference is an explicit premise, not a consequence of key inequality. -/
def PhysicalDistinct (ρ : Resolver M) (k j : K) : Prop :=
  (ρ.resolve k).token ≠ (ρ.resolve j).token

/-- `PhysicalDistinct` is exactly inequality of the selected physical tokens. -/
theorem physicalDistinct_iff (ρ : Resolver M) (k j : K) :
    PhysicalDistinct ρ k j ↔ (ρ.resolve k).token ≠ (ρ.resolve j).token :=
  Iff.rfl

/-- Physical distinctness is symmetric. -/
theorem physicalDistinct_symm {ρ : Resolver M} {k j : K} (h : PhysicalDistinct ρ k j) :
    PhysicalDistinct ρ j k :=
  h.symm

/-- Distinct logical keys resolve to distinct physical tokens.

The converse may fail when two keys resolve to one realm, so logical-key
inequality is not the definition of `PhysicalDistinct`. -/
theorem physicalDistinct_of_ne (ρ : Resolver M) {k j : K} (h : k ≠ j) :
    PhysicalDistinct ρ k j := by
  intro ht
  exact h (by
    calc
      k = M.keyOf (ρ.resolve k).token := (ρ.resolve k).key_eq.symm
      _ = M.keyOf (ρ.resolve j).token := congrArg M.keyOf ht
      _ = j := (ρ.resolve j).key_eq)

end PhysicalDistinct

/-! ### Scoped frame laws -/

section ScopedFrameLaws

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {Store : Type x}
variable [DecidableEq K]

/-- Inserting at `k` does not disturb a lookup at a physically distinct `j`. -/
theorem scopedLookup_insert_frame (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) (v : V k) {j : K} (h : PhysicalDistinct ρ k j) :
    scopedLookup ops ρ (scopedInsert ops ρ s k v) j = scopedLookup ops ρ s j := by
  simp only [PhysicalDistinct] at h
  simp [scopedLookup, scopedInsert, ops.lookup_insert_other, h.symm]

/-- Erasing at `k` does not disturb a lookup at a physically distinct `j`. -/
theorem scopedLookup_erase_frame (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) {j : K} (h : PhysicalDistinct ρ k j) :
    scopedLookup ops ρ (scopedErase ops ρ s k) j = scopedLookup ops ρ s j := by
  simp only [PhysicalDistinct] at h
  simp [scopedLookup, scopedErase, ops.lookup_erase_other, h.symm]

/-- Inserting then erasing at the same selected realm leaves the binding absent. -/
theorem scopedLookup_insert_erase_self (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) (v : V k) :
    scopedLookup ops ρ (scopedErase ops ρ (scopedInsert ops ρ s k v) k) k = none := by
  simp [scopedLookup, scopedErase, scopedInsert, ops.lookup_erase_same]

/-- A scoped insertion through one resolver does not disturb a lookup through another
resolver whose selected realm is physically distinct.

This is the same-key/different-realm frame case: two realms under one logical
key remain noninterfering, which logical-key inequality alone cannot express. -/
theorem scopedLookup_insert_frame_twoResolvers (ops : RealmStoreOps M Store)
    (ρ₁ ρ₂ : Resolver M) (s : Store) (k : K) (v : V k)
    (h : (ρ₁.resolve k).token ≠ (ρ₂.resolve k).token) :
    scopedLookup ops ρ₂ (scopedInsert ops ρ₁ s k v) k = scopedLookup ops ρ₂ s k := by
  dsimp [scopedLookup, scopedInsert]
  rw [ops.lookup_insert_other]
  exact h.symm

/-- A scoped erasure through one resolver does not disturb a lookup through another
resolver whose selected realm is physically distinct. -/
theorem scopedLookup_erase_frame_twoResolvers (ops : RealmStoreOps M Store)
    (ρ₁ ρ₂ : Resolver M) (s : Store) (k : K)
    (h : (ρ₁.resolve k).token ≠ (ρ₂.resolve k).token) :
    scopedLookup ops ρ₂ (scopedErase ops ρ₁ s k) k = scopedLookup ops ρ₂ s k := by
  dsimp [scopedLookup, scopedErase]
  rw [ops.lookup_erase_other]
  exact h.symm

end ScopedFrameLaws

/-! ### Physical adapter over the authoritative P5 store -/

section PhysicalAdapter

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}

/-- The physical realm store: the authoritative P5 dependent store at the realm token type. -/
abbrev RealmStore (M : RealmModel K V) :=
  Coeffect.Store (fun r : M.Realm => V (M.keyOf r))

end PhysicalAdapter

section FinmapAdapter

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq M.Realm]

/-- The ADR-02 dependent `Finmap` façade as the realm store operation instance. -/
def finmapRealmStoreOps : RealmStoreOps M (RealmStore M) where
  empty := ∅
  lookup := fun s r => Coeffect.lookup r s
  insert := fun s r v => Coeffect.insert r v s
  erase := fun s r => Coeffect.erase r s
  lookup_empty := by
    intro r
    rfl
  lookup_insert_same := by
    intro s r v
    exact Coeffect.coeffect_lookup_insert r v s
  lookup_insert_other := by
    intro s r v q h
    exact Coeffect.coeffect_lookup_insert_ne h v s
  lookup_erase_same := by
    intro s r
    exact Coeffect.coeffect_lookup_erase r s
  lookup_erase_other := by
    intro s r q h
    exact Coeffect.coeffect_lookup_erase_ne h s

end FinmapAdapter

/-! ### Captured-reference inverses and rollback -/

section Restoration

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V} {Store : Type x}
variable [DecidableEq K]

/-- The inverse data of one scoped insertion: the realm captured at application time. -/
structure ScopedInsertInverse (M : RealmModel K V) (k : K) (Store : Type x) where
  selected : RealmRef M k
  undo : Store → Store

/-- Build the undo of a scoped insertion from the reference selected at application time. -/
def scopedInsertInverse (ops : RealmStoreOps M Store) (ρ : Resolver M) (k : K) :
    ScopedInsertInverse M k Store :=
  { selected := ρ.resolve k
    undo := fun s => ops.erase s (ρ.resolve k).token }

/-- The captured inverse erases exactly the token selected at application time; it never
re-resolves through a possibly changed resolver. -/
theorem scopedInsertInverse_undo_eq (ops : RealmStoreOps M Store) (ρ : Resolver M) (k : K)
    (s : Store) :
    (scopedInsertInverse ops ρ k).undo s = ops.erase s (ρ.resolve k).token :=
  rfl

/-- The inverse data of one scoped erase: the selected reference and the erased value. -/
structure ScopedEraseInverse (M : RealmModel K V) (k : K) (Store : Type x) where
  selected : RealmRef M k
  restored : Option (V k)
  undo : Store → Store

/-- Build the undo of a scoped erase; the restore payload is captured before the erase. -/
def scopedEraseInverse (ops : RealmStoreOps M Store) (ρ : Resolver M) (s : Store) (k : K) :
    ScopedEraseInverse M k Store :=
  let rr := ρ.resolve k
  { selected := rr
    restored := (ops.lookup s rr.token).map (RealmRef.cast rr)
    undo := fun s' =>
      match ops.lookup s rr.token with
      | some v => ops.insert s' rr.token v
      | none => s' }

/-- The restore payload is exactly the value visible at operation time. -/
theorem scopedEraseInverse_restored_eq_lookup (ops : RealmStoreOps M Store) (ρ : Resolver M)
    (s : Store) (k : K) :
    (scopedEraseInverse ops ρ s k).restored = scopedLookup ops ρ s k :=
  rfl

end Restoration

/-! ### Rollback laws at the physical `Finmap` level -/

section FinmapRestoration

variable {K : Type u} {V : K → Type v}
variable {M : RealmModel K V}
variable [DecidableEq K] [DecidableEq M.Realm]

/-- Undoing an insertion restores every lookup when the selected realm was previously absent. -/
theorem finmap_scopedInsertInverse_restores_lookup (ρ : Resolver M) (s : RealmStore M)
    (k : K) (v : V k) (h : Coeffect.lookup (ρ.resolve k).token s = none) (q : M.Realm) :
    Coeffect.lookup q
        ((scopedInsertInverse finmapRealmStoreOps ρ k).undo
          (scopedInsert finmapRealmStoreOps ρ s k v)) = Coeffect.lookup q s := by
  unfold scopedInsertInverse scopedInsert finmapRealmStoreOps
  by_cases hq : q = (ρ.resolve k).token
  · subst q
    rw [Coeffect.coeffect_lookup_erase]
    exact h.symm
  · rw [Coeffect.coeffect_lookup_erase_ne hq, Coeffect.coeffect_lookup_insert_ne hq]

/-- Undoing an insertion restores the store when the selected realm was previously absent. -/
theorem finmap_scopedInsertInverse_restores (ρ : Resolver M) (s : RealmStore M) (k : K)
    (v : V k) (h : Coeffect.lookup (ρ.resolve k).token s = none) :
    (scopedInsertInverse finmapRealmStoreOps ρ k).undo
        (scopedInsert finmapRealmStoreOps ρ s k v) = s := by
  apply Finmap.ext_lookup
  intro q
  exact finmap_scopedInsertInverse_restores_lookup ρ s k v h q

/-- Undoing an erase restores every lookup when the erased binding was present. -/
theorem finmap_scopedEraseInverse_restores_lookup (ρ : Resolver M) (s : RealmStore M)
    (k : K) {v : V (M.keyOf (ρ.resolve k).token)}
    (h : Coeffect.lookup (ρ.resolve k).token s = some v) (q : M.Realm) :
    Coeffect.lookup q
        ((scopedEraseInverse finmapRealmStoreOps ρ s k).undo
          (scopedErase finmapRealmStoreOps ρ s k)) = Coeffect.lookup q s := by
  unfold scopedEraseInverse scopedErase finmapRealmStoreOps
  simp only [h]
  by_cases hq : q = (ρ.resolve k).token
  · subst q
    rw [Coeffect.coeffect_lookup_insert]
    exact h.symm
  · rw [Coeffect.coeffect_lookup_insert_ne hq, Coeffect.coeffect_lookup_erase_ne hq]

/-- Undoing an erase restores the store when the erased binding was present. -/
theorem finmap_scopedEraseInverse_restores (ρ : Resolver M) (s : RealmStore M) (k : K)
    {v : V (M.keyOf (ρ.resolve k).token)}
    (h : Coeffect.lookup (ρ.resolve k).token s = some v) :
    (scopedEraseInverse finmapRealmStoreOps ρ s k).undo
        (scopedErase finmapRealmStoreOps ρ s k) = s := by
  apply Finmap.ext_lookup
  intro q
  exact finmap_scopedEraseInverse_restores_lookup ρ s k h q

end FinmapRestoration

end

end STC.Scoped
