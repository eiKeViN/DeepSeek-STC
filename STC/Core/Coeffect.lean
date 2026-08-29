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

/-- A key-local coeffect interface with explicit relation-respect laws. -/
structure CoeffectOps (R : RelSpec (Store V)) where
  get : K → Store V → Option (Sigma V)
  get_spec : ∀ k store, get k store = (lookup k store).map (fun value => ⟨k, value⟩)
  respects : ∀ {left right}, R.rel left right →
    ∀ k, (get k left).isSome = (get k right).isSome

end WitnessedTransitions

section Satisfaction

variable {K : Type u} {V : K → Type v} [DecidableEq K]

/-- Relational satisfaction of every binding in a finite dependent store. -/
def Satisfies (requirement : ∀ k, V k → Prop) (store : Store V) : Prop :=
  ∀ k value, lookup k store = some value → requirement k value

/-- The executable checker is distinct from `Satisfies` but computes it by the
finite decidability supplied at the boundary. -/
def satCheck (spec : ∀ k, V k → Prop)
    (decideSat : ∀ store : Store V, Decidable (Satisfies spec store))
    (store : Store V) : Bool :=
  @decide (Satisfies spec store) (decideSat store)

theorem satCheck_sound (spec : ∀ k, V k → Prop)
    (decideSat : ∀ store : Store V, Decidable (Satisfies spec store))
    (store : Store V) (h : satCheck spec decideSat store = true) : Satisfies spec store := by
  exact of_decide_eq_true h

theorem satCheck_complete (spec : ∀ k, V k → Prop)
    (decideSat : ∀ store : Store V, Decidable (Satisfies spec store))
    (store : Store V) (h : Satisfies spec store) : satCheck spec decideSat store = true := by
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
