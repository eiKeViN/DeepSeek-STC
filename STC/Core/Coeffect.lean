module

public import STC.Core.Partial
public import STC.State.CoeffectStore

/-!
# Coeffect and satisfaction prerequisites

The semantic satisfaction relation is kept separate from its finite Boolean
checker.  All store transitions are witnessed at the authoritative dependent
`Finmap` carrier; no competing mutable store is introduced.
-/

universe u v w

namespace STC

@[expose] public section

namespace Coeffect

section StoreAlgebra

variable {K : Type u} {V : K → Type v} [DecidableEq K]

/-- Domain membership of a dependent store. -/
def Domain (store : Store V) : Finset K := store.keys

/-- Disjointness of two dependent-store domains. -/
def StoreDisjoint (left right : Store V) : Prop := Finmap.Disjoint left right

theorem domain_union (left right : Store V) :
    Domain (left ∪ right) = Domain left ∪ Domain right := by
  exact Finmap.keys_union

theorem lookup_union_left {left right : Store V} {k : K}
    (h : k ∈ left) : lookup k (left ∪ right) = lookup k left := by
  exact Finmap.lookup_union_left h

theorem lookup_union_right {left right : Store V} {k : K}
    (h : k ∉ left) : lookup k (left ∪ right) = lookup k right := by
  exact Finmap.lookup_union_right h

theorem union_comm_of_disjoint {left right : Store V}
    (h : StoreDisjoint left right) : left ∪ right = right ∪ left := by
  exact Finmap.union_comm_of_disjoint h

theorem insert_erase_restore (store : Store V) (k : K) (value : V k)
    (h : lookup k store = none) :
    erase k (insert k value store) = store := by
  apply Finmap.ext_lookup
  intro key
  by_cases hk : key = k
  · subst key
    simpa [erase, insert, lookup] using h.symm
  · simp [insert, erase, hk]

theorem erase_insert_restore (store : Store V) (k : K) (value : V k) :
    lookup k (insert k value (erase k store)) = some value := by
  simp [lookup, insert, erase]

/-- Inserting at a distinct key leaves other lookups untouched. -/
theorem insert_frame {k j : K} (h : j ≠ k) (value : V k) (store : Store V) :
    lookup j (insert k value store) = lookup j store :=
  coeffect_lookup_insert_ne h value store

/-- Erasing at a distinct key leaves other lookups untouched. -/
theorem erase_frame {k j : K} (h : j ≠ k) (store : Store V) :
    lookup j (erase k store) = lookup j store :=
  coeffect_lookup_erase_ne h store

/-- Inserting adds the key to the domain. -/
theorem domain_insert (store : Store V) (k : K) (value : V k) :
    Domain (insert k value store) = Insert.insert k (Domain store) := by
  apply Finset.ext
  intro j
  change j ∈ Finmap.insert k value store ↔ j ∈ Insert.insert k (Finmap.keys store)
  rw [Finmap.mem_insert, Finset.mem_insert, Finmap.mem_keys]

/-- Erasing removes the key from the domain. -/
theorem domain_erase (store : Store V) (k : K) :
    Domain (erase k store) = (Domain store).erase k :=
  Finmap.keys_erase k store

end StoreAlgebra

section WitnessedTransitions

variable {K : Type u} {V : K → Type v} [DecidableEq K]

/-- A witnessed read transition leaves the store unchanged. -/
def GetStep (k : K) (v : V k) (before after : Store V) : Prop :=
  before = after ∧ lookup k before = some v

/-- A witnessed provision/set transition inserts a previously absent binding. -/
def ProvideStep (k : K) (v : V k) (before after : Store V) : Prop :=
  lookup k before = none ∧ after = insert k v before

/-- A witnessed revoke transition records the removed value. -/
def RevokeStep (k : K) (v : V k) (before after : Store V) : Prop :=
  lookup k before = some v ∧ after = erase k before

theorem getStep_frame {k : K} {v : V k} {before after : Store V}
    (h : GetStep k v before after) : before = after := h.1

theorem provideStep_lookup {k : K} {v : V k} {before after : Store V}
    (h : ProvideStep k v before after) : lookup k after = some v := by
  rw [h.2]
  simp

theorem revokeStep_lookup {k : K} {v : V k} {before after : Store V}
    (h : RevokeStep k v before after) : lookup k after = none := by
  rw [h.2]
  simp

theorem provide_revoke_restore {k : K} {v : V k} {before after : Store V}
    (h : ProvideStep k v before after) : erase k after = before := by
  rw [h.2]
  exact insert_erase_restore before k v h.1

theorem revoke_provide_restore {k : K} {v : V k} {before after : Store V}
    (h : RevokeStep k v before after) : insert k v after = before := by
  rw [h.2]
  apply Finmap.ext_lookup
  intro key
  by_cases hk : key = k
  · subst key
    simpa [erase, insert, lookup] using h.1.symm
  · simp [insert, erase, hk]

/-- A provision at `k` leaves a distinct key's lookup untouched. -/
theorem provideStep_frame {k j : K} {v : V k} {before after : Store V}
    (hkj : j ≠ k) (h : ProvideStep k v before after) :
    lookup j after = lookup j before := by
  rw [h.2]
  exact insert_frame hkj v before

/-- A revoke at `k` leaves a distinct key's lookup untouched. -/
theorem revokeStep_frame {k j : K} {v : V k} {before after : Store V}
    (hkj : j ≠ k) (h : RevokeStep k v before after) :
    lookup j after = lookup j before := by
  rw [h.2]
  exact erase_frame hkj before

/-- A key-local coeffect interface with explicit relation-respect laws. -/
structure CoeffectOps (R : RelSpec (Store V)) where
  get : K → Store V → Option (Sigma V)
  get_spec : ∀ k store, get k store = (lookup k store).map (fun value => ⟨k, value⟩)
  respects : ∀ {left right}, R.rel left right →
    ∀ k, (get k left).isSome = (get k right).isSome

/-- The lifted read: a partial operation reading the value at `k`. -/
def liftGet (k : K) : PartialOp (Store V) (Sigma V) :=
  fun store =>
    (lookup k store).map fun value =>
      { state := store, undo := id, outcome := ⟨k, value⟩ }

/-- The lifted read result carries the state unchanged and the identity undo. -/
theorem liftGet_spec (k : K) (store : Store V) :
    liftGet k store =
      (lookup k store).map fun value =>
        { state := store, undo := (id : Store V → Store V), outcome := (⟨k, value⟩ : Sigma V) } :=
  rfl

/-- The lifted read has exactly the definedness of the raw lookup. -/
theorem liftGet_isSome (k : K) (store : Store V) :
    (liftGet k store).isSome = (lookup k store).isSome := by
  rw [liftGet_spec]
  simp

/-- The lifted read is relation-respecting in definedness. -/
theorem liftGet_definednessStable (R : RelSpec (Store V)) (ops : CoeffectOps R) (k : K) :
    DefinednessStable R (liftGet k) := by
  intro left right hlr
  constructor
  · intro h
    rcases h with ⟨r, hr⟩
    have hiso : (liftGet k left).isSome = (liftGet k right).isSome := by
      simpa [liftGet_isSome, ops.get_spec] using (ops.respects hlr k)
    exact Option.isSome_iff_exists.mp (by simpa [hr] using hiso.symm)
  · intro h
    rcases h with ⟨r, hr⟩
    have hiso : (liftGet k left).isSome = (liftGet k right).isSome := by
      simpa [liftGet_isSome, ops.get_spec] using (ops.respects hlr k)
    exact Option.isSome_iff_exists.mp (by simpa [hr] using hiso)

/-- The lifted provision inserts a previously absent binding; the undo erases it. -/
def liftProvide (k : K) (value : V k) : PartialOp (Store V) Unit :=
  fun store =>
    if _ : lookup k store = none then
      some { state := insert k value store, undo := erase k, outcome := () }
    else none

/-- A defined provision inserts exactly the supplied value. -/
theorem liftProvide_lookup (k : K) (value : V k) {store : Store V} {r : OpResult (Store V) Unit}
    (h : liftProvide k value store = some r) : lookup k r.state = some value := by
  unfold liftProvide at h
  split at h
  · have hr := Option.some.inj h
    subst r
    simp
  · cases h

/-- A defined provision restores the store through its undo. -/
theorem liftProvide_recovers (R : RelSpec (Store V)) (k : K) (value : V k) :
    OperationRecovers R (liftProvide k value) := by
  intro input r h
  unfold liftProvide at h
  by_cases hnone : lookup k input = none
  · simp [hnone] at h
    subst r
    change R.rel (erase k (insert k value input)) input
    rw [insert_erase_restore input k value hnone]
    exact R.refl input
  · simp [hnone] at h

/-- A provision at `k` leaves a distinct key's lookup untouched. -/
theorem liftProvide_frame (k : K) (value : V k) {j : K} {store : Store V}
    {r : OpResult (Store V) Unit} (hkj : j ≠ k) (h : liftProvide k value store = some r) :
    lookup j r.state = lookup j store := by
  unfold liftProvide at h
  split at h
  · have hr := Option.some.inj h
    subst r
    exact insert_frame hkj value store
  · cases h

/-- The lifted revoke erases a present binding; the undo restores the captured value. -/
def liftRevoke (k : K) : PartialOp (Store V) (Sigma V) :=
  fun store =>
    (lookup k store).map fun value =>
      { state := erase k store, undo := fun s => insert k value s, outcome := ⟨k, value⟩ }

/-- A defined revoke removes the binding at `k`. -/
theorem liftRevoke_lookup (k : K) {store : Store V} {r : OpResult (Store V) (Sigma V)}
    (h : liftRevoke k store = some r) : lookup k r.state = none := by
  unfold liftRevoke at h
  rcases hlook : lookup k store with _ | value <;> simp [hlook] at h
  subst r
  simp

/-- A defined revoke restores the store through its undo. -/
theorem liftRevoke_recovers (R : RelSpec (Store V)) (k : K) :
    OperationRecovers R (liftRevoke k) := by
  intro input r h
  unfold liftRevoke at h
  rcases hlook : lookup k input with _ | value <;> simp [hlook] at h
  subst r
  change R.rel (insert k value (erase k input)) input
  rw [revoke_provide_restore]
  · exact R.refl input
  · exact ⟨hlook, rfl⟩

/-- A revoke at `k` leaves a distinct key's lookup untouched. -/
theorem liftRevoke_frame (k : K) {j : K} {store : Store V}
    {r : OpResult (Store V) (Sigma V)} (hkj : j ≠ k) (h : liftRevoke k store = some r) :
    lookup j r.state = lookup j store := by
  unfold liftRevoke at h
  rcases hlook : lookup k store with _ | value <;> simp [hlook] at h
  subst r
  exact erase_frame hkj store

/-- Lift a key-local partial update to a store-level partial operation: the store-level
operation reads `k`, runs the local update, and reinstalls the result, capturing the
previous value as the undo. -/
def liftKeyLocal (k : K) (localOp : V k → Option (V k)) : PartialOp (Store V) Unit :=
  fun store =>
    match lookup k store with
    | none => none
    | some old =>
        (localOp old).map fun newVal =>
          { state := insert k newVal store, undo := fun s => insert k old s, outcome := () }

/-- A defined key-local lift preserves distinct keys' lookups. -/
theorem liftKeyLocal_frame (k : K) (localOp : V k → Option (V k)) {j : K} {store : Store V}
    {r : OpResult (Store V) Unit} (hkj : j ≠ k) (h : liftKeyLocal k localOp store = some r) :
    lookup j r.state = lookup j store := by
  rcases hlook : lookup k store with _ | old
  · simp [liftKeyLocal, hlook] at h
  · rcases hnew : localOp old with _ | newVal
    · simp [liftKeyLocal, hlook, hnew] at h
    · simp [liftKeyLocal, hlook, hnew] at h
      subst r
      exact insert_frame hkj newVal store

/-- A defined key-local lift restores the previous value at `k` through its undo. -/
theorem liftKeyLocal_restore (k : K) (localOp : V k → Option (V k)) {store : Store V}
    {r : OpResult (Store V) Unit} (h : liftKeyLocal k localOp store = some r) :
    lookup k (r.undo r.state) = lookup k store := by
  rcases hlook : lookup k store with _ | old
  · simp [liftKeyLocal, hlook] at h
  · rcases hnew : localOp old with _ | newVal
    · simp [liftKeyLocal, hlook, hnew] at h
    · simp [liftKeyLocal, hlook, hnew] at h
      subst r
      simp

end WitnessedTransitions

section Satisfaction

variable {K : Type u} {V : K → Type v} [DecidableEq K]

/-- Relational satisfaction of every binding in a finite dependent store. -/
def Satisfies (requirement : ∀ k, V k → Prop) (store : Store V) : Prop :=
  ∀ k value, lookup k store = some value → requirement k value

/-- The paper's satisfaction of a finite declaration set: every declared key is present. -/
abbrev declaredSatisfied (d : Finset K) (store : Store V) : Prop :=
  ∀ k, k ∈ d → k ∈ Domain store

/-- Constructive decidability of `Satisfies` from per-binding decidability: the finite
store bounds the universal quantification, so no classical oracle is supplied. -/
def decidableSatisfies (requirement : ∀ k, V k → Prop)
    (hdec : ∀ k value, Decidable (requirement k value)) (store : Store V) :
    Decidable (Satisfies requirement store) := by
  let perKey : ∀ k, Decidable (∀ value, lookup k store = some value → requirement k value) := by
    intro k
    rcases hlook : lookup k store with _ | presentVal
    · exact isTrue (by
        intro (v : V k) hv
        cases hv)
    · refine decidable_of_iff (requirement k presentVal) ?_
      constructor
      · intro hr v hv
        have hvv : presentVal = v := Option.some.inj hv
        subst v
        exact hr
      · intro hall
        apply hall
        rfl
  let onDomain : Decidable (∀ k, k ∈ Domain store →
      ∀ value, lookup k store = some value → requirement k value) := by
    infer_instance
  have hdom : (∀ k, k ∈ Domain store →
      ∀ value, lookup k store = some value → requirement k value) ↔
      Satisfies requirement store := by
    constructor
    · intro h k value hv
      exact h k (by exact Finmap.mem_iff.mpr ⟨value, hv⟩) value hv
    · intro h k hk value hv
      exact h k value hv
  exact decidable_of_iff
    (∀ k, k ∈ Domain store → ∀ value, lookup k store = some value → requirement k value)
    hdom

/-- The executable checker computes `Satisfies` from per-binding decidability. -/
def satCheck (spec : ∀ k, V k → Prop)
    (hdec : ∀ k value, Decidable (spec k value))
    (store : Store V) : Bool :=
  @decide (Satisfies spec store) (decidableSatisfies spec hdec store)

theorem satCheck_sound (spec : ∀ k, V k → Prop)
    (hdec : ∀ k value, Decidable (spec k value))
    (store : Store V) (h : satCheck spec hdec store = true) : Satisfies spec store := by
  unfold satCheck at h
  exact @of_decide_eq_true (Satisfies spec store) (decidableSatisfies spec hdec store) h

theorem satCheck_complete (spec : ∀ k, V k → Prop)
    (hdec : ∀ k value, Decidable (spec k value))
    (store : Store V) (h : Satisfies spec store) : satCheck spec hdec store = true := by
  unfold satCheck
  exact (@decide_eq_true_eq (Satisfies spec store) (decidableSatisfies spec hdec store)).mpr h

/-- The executable declared-set checker is decidable from the finite declaration set
alone; its soundness and completeness relate it to `declaredSatisfied`. -/
def declaredCheck (d : Finset K) (store : Store V) : Bool :=
  decide (declaredSatisfied d store)

theorem declaredCheck_sound (d : Finset K) (store : Store V)
    (h : declaredCheck d store = true) : declaredSatisfied d store := by
  unfold declaredCheck at h
  exact of_decide_eq_true h

theorem declaredCheck_complete (d : Finset K) (store : Store V)
    (h : declaredSatisfied d store) : declaredCheck d store = true := by
  unfold declaredCheck
  exact decide_eq_true_eq.mpr h

/-- A checked finite SAT profile packages soundness and completeness without
identifying the checker with the semantic relation. -/
structure SATProfile where
  requirement : ∀ k, V k → Prop
  checker : Store V → Bool
  sound : ∀ store, checker store = true → Satisfies requirement store
  complete : ∀ store, Satisfies requirement store → checker store = true

end Satisfaction

end Coeffect

end

end STC
