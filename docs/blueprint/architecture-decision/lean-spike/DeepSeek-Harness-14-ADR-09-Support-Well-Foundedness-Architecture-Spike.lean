import Mathlib.Tactic

set_option autoImplicit false

/-!
  ADR-09: support well-foundedness architecture.

  This is an isolated architecture spike.  It deliberately does not import
  production STC modules: the latter are owned by the P5 state-carrier work.
  The support relation has the paper's orientation

      a ⊲ b  :=  a ≺ b ∨ parent(b) = a.

  `SupportSet` is defined positively as the intersection of all prefixed sets;
  no recursive state/function field is introduced.  A `SupportOrder` is an
  explicit rank certificate, so well-foundedness is an assumption/certificate
  that later control and lifecycle proofs may require.
-/

universe u v

namespace STCADR09

section Snapshot

variable {N : Type u} {K : Type v}

structure Snapshot (N : Type u) (K : Type v)
    [DecidableEq N] [DecidableEq K] where
  dom : Finset N
  retired : N → Bool
  parent : N → Option N
  requires : N → Finset K
  provides : N → Finset K
  birth : N → Nat

variable [DecidableEq N] [DecidableEq K]

/- `Nonempty` of the provider/requirement intersection is the finite,
   decidable form of `p_a ∩ d_b ≠ ∅`. -/
def Precedes (s : Snapshot N K) (a b : N) : Prop :=
  (s.provides a ∩ s.requires b).Nonempty

def ParentEdge (s : Snapshot N K) (a b : N) : Prop :=
  s.parent b = some a

/- Paper orientation: the edge points from the provider/parent to its
   dependent/child.  This direction is used by every rank certificate below. -/
def SupportRel (s : Snapshot N K) (a b : N) : Prop :=
  Precedes s a b ∨ ParentEdge s a b

/- The recursion-facing dependency relation is the converse: a dependent b
   points to its support predecessor a.  Thus a provider→dependent rank increase
   becomes a strict rank decrease when induction follows `SupportDep`. -/
def SupportDep (s : Snapshot N K) (b a : N) : Prop :=
  SupportRel s a b

def ParentSupported (s : Snapshot N K) (A : Set N) (n : N) : Prop :=
  s.parent n = none ∨ ∃ p, s.parent n = some p ∧ p ∈ A

def ProvidersSupported (s : Snapshot N K) (A : Set N) (n : N) : Prop :=
  ∀ k, k ∈ s.requires n → ∃ m, m ∈ A ∧ k ∈ s.provides m

/- Positive support clause.  It refers only to a candidate set A, never to a
   recursively stored State → State function. -/
def SupportClause (s : Snapshot N K) (A : Set N) (n : N) : Prop :=
  n ∈ s.dom ∧ s.retired n = false ∧
    ParentSupported s A n ∧ ProvidersSupported s A n

def SupportOperator (s : Snapshot N K) (A : Set N) : Set N :=
  {n | SupportClause s A n}

def Prefixed (s : Snapshot N K) (A : Set N) : Prop :=
  SupportOperator s A ⊆ A

/- The least fixed point contract is the intersection of all prefixed sets.
   This is total even for a malformed/cyclic graph; a later theorem can add a
   SupportWF certificate when a non-empty/well-founded support is required. -/
def SupportSet (s : Snapshot N K) : Set N :=
  {n | ∀ A : Set N, Prefixed s A → n ∈ A}

theorem supportClause_mono (s : Snapshot N K) {A B : Set N}
    (hAB : A ⊆ B) {n : N} :
    SupportClause s A n → SupportClause s B n := by
  intro h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rcases h.2.2.1 with hroot | ⟨p, hp, hpa⟩
    · exact Or.inl hroot
    · exact Or.inr ⟨p, hp, hAB hpa⟩
  · intro k hk
    rcases h.2.2.2 k hk with ⟨m, hmA, hmk⟩
    exact ⟨m, hAB hmA, hmk⟩

theorem supportSet_least (s : Snapshot N K) {A : Set N}
    (hA : Prefixed s A) : SupportSet s ⊆ A := by
  intro n hn
  exact hn A hA

theorem supportSet_prefixed (s : Snapshot N K) :
    Prefixed s (SupportSet s) := by
  intro n hn
  intro A hA
  apply hA
  exact supportClause_mono s (supportSet_least s hA) hn

theorem supportOperator_prefixed (s : Snapshot N K) :
    Prefixed s (SupportOperator s (SupportSet s)) := by
  intro n hnn
  exact supportClause_mono s (supportSet_prefixed s) hnn

theorem supportSet_subset_operator (s : Snapshot N K) :
    SupportSet s ⊆ SupportOperator s (SupportSet s) :=
  supportSet_least s (supportOperator_prefixed s)

theorem supportSet_fixed (s : Snapshot N K) :
    SupportOperator s (SupportSet s) = SupportSet s := by
  apply Set.Subset.antisymm
  · exact supportSet_prefixed s
  · exact supportSet_subset_operator s

/- A rank certificate makes the orientation and the required WF obligation
   explicit.  The finite domain is part of Snapshot, so this certificate is
   enough to derive ordinary well-foundedness for the restricted relation. -/
structure SupportOrder (s : Snapshot N K) where
  rank : N → Nat
  edge_lt : ∀ {a b}, a ∈ s.dom → b ∈ s.dom →
    SupportRel s a b → rank a < rank b

theorem supportDep_rank_lt (s : Snapshot N K) (o : SupportOrder s)
    {b a : N} (hb : b ∈ s.dom) (ha : a ∈ s.dom)
    (hba : SupportDep s b a) : o.rank a < o.rank b := by
  exact o.edge_lt ha hb hba

abbrev RankCertificate (s : Snapshot N K) := SupportOrder s

def SupportWF (s : Snapshot N K) : Prop := Nonempty (SupportOrder s)

theorem supportWF_of_order (s : Snapshot N K) (o : SupportOrder s) :
    SupportWF s := ⟨o⟩

theorem no_support_two_cycle (s : Snapshot N K) (o : SupportOrder s)
    {a b : N} (ha : a ∈ s.dom) (hb : b ∈ s.dom)
    (hab : SupportRel s a b) (hba : SupportRel s b a) : False := by
  have h1 := o.edge_lt ha hb hab
  have h2 := o.edge_lt hb ha hba
  omega

/- Restricted profile: every support edge follows immutable allocation/birth
   order.  This is deliberately stronger than current-fresh O-Insert and is
   therefore an optional no-late-registration profile, not a rewrite of it. -/
structure NoLateRegistration (s : Snapshot N K) : Prop where
  birth_strict : ∀ {a b}, a ∈ s.dom → b ∈ s.dom →
    SupportRel s a b → s.birth a < s.birth b

def NoLateRegistration.toOrder {s : Snapshot N K}
    (h : NoLateRegistration s) : SupportOrder s :=
  { rank := s.birth
    edge_lt := h.birth_strict }

/- A committed snapshot freezes the finite domain and carries its rank proof.
   `committed_subset` and `domain_committed` together express equality with the
   snapshot domain without choosing a particular Finset equality lemma. -/
structure CommittedSnapshot (s : Snapshot N K) where
  committed : Finset N
  committed_subset : committed ⊆ s.dom
  domain_committed : ∀ {n}, n ∈ s.dom → n ∈ committed
  order : SupportOrder s

theorem committed_domain_exact (s : Snapshot N K)
    (c : CommittedSnapshot s) : c.committed = s.dom := by
  ext n
  constructor
  · intro hn
    exact c.committed_subset hn
  · intro hn
    exact c.domain_committed hn

end Snapshot

section FrozenShorthandAndCycle

/- The three edges in the frozen shorthand are r→n, r→c, c→n (with the
   orientation above).  They are not a cycle.  The concrete snapshots make
   the claim executable/decidable while keeping the generic support contract
   independent of this illustrative graph. -/

def shorthandSnapshot : Snapshot (Fin 3) (Fin 2) where
  dom := {0, 1, 2}
  retired := fun _ => false
  parent := fun n =>
    if n = 0 then none else if n = 1 then some 0 else some 1
  requires := fun n => if n = 2 then {0} else ∅
  provides := fun n => if n = 0 then {0} else ∅
  birth := fun n => n.val

theorem shorthand_rank_compatible :
    ∀ {a b : Fin 3}, SupportRel shorthandSnapshot a b →
      a.val < b.val := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
  simp [SupportRel, Precedes, ParentEdge, shorthandSnapshot] at h ⊢ <;>
    omega

theorem shorthand_not_cycle :
    ¬ ∃ (a b c : Fin 3),
      SupportRel shorthandSnapshot a b ∧
      SupportRel shorthandSnapshot b c ∧
      SupportRel shorthandSnapshot c a := by
  rintro ⟨a, b, c, hab, hbc, hca⟩
  have hab' := shorthand_rank_compatible hab
  have hbc' := shorthand_rank_compatible hbc
  have hca' := shorthand_rank_compatible hca
  omega

/- To obtain a genuine combined-support cycle while keeping the parent chain
   r→c→n, add the *additional* precedence edge n→r.  This is a graph
   witness only; no reachable lifecycle trace is claimed. -/
def correctedCycleSnapshot : Snapshot (Fin 3) (Fin 2) where
  dom := {0, 1, 2}
  retired := fun _ => false
  parent := fun n =>
    if n = 0 then none else if n = 1 then some 0 else some 1
  requires := fun n => if n = 0 then {0} else ∅
  provides := fun n => if n = 2 then {0} else ∅
  birth := fun n => n.val

theorem corrected_precedence_acyclic :
    ∀ {a b : Fin 3}, Precedes correctedCycleSnapshot a b →
      (2 - a.val) < (2 - b.val) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
  simp [Precedes, correctedCycleSnapshot] at h ⊢ <;>
    omega

theorem corrected_cycle_edges :
    SupportRel correctedCycleSnapshot (2 : Fin 3) 0 ∧
      SupportRel correctedCycleSnapshot 0 1 ∧
      SupportRel correctedCycleSnapshot 1 2 := by
  decide

theorem corrected_cycle_has_no_rank :
    ¬ ∃ rank : Fin 3 → Nat,
      (∀ {a b : Fin 3}, SupportRel correctedCycleSnapshot a b →
        rank a < rank b) := by
  rintro ⟨rank, h⟩
  have h20 := h (a := (2 : Fin 3)) (b := 0) (by decide)
  have h01 := h (a := (0 : Fin 3)) (b := 1) (by decide)
  have h12 := h (a := (1 : Fin 3)) (b := 2) (by decide)
  omega

/- Small executable checks used by CI/readers of the spike.  They intentionally
   check only the finite witness facts, not the deferred reachability claims. -/
def shorthandCheck : Bool :=
  decide (SupportRel shorthandSnapshot (0 : Fin 3) 2 ∧
    SupportRel shorthandSnapshot (0 : Fin 3) 1 ∧
    SupportRel shorthandSnapshot (1 : Fin 3) 2)

def correctedCycleCheck : Bool :=
  decide (SupportRel correctedCycleSnapshot (2 : Fin 3) 0 ∧
    SupportRel correctedCycleSnapshot (0 : Fin 3) 1 ∧
    SupportRel correctedCycleSnapshot (1 : Fin 3) 2)

#eval shorthandCheck
#eval correctedCycleCheck

end FrozenShorthandAndCycle

end STCADR09
