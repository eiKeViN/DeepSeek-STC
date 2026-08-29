module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.FixedPoints

/-!
# Support core

Committed support snapshots, positive support closure, and an explicit rank
certificate.  `SupportRel` points from provider/parent to dependent; `SupportDep`
is its converse for dependency-first induction.  Support rank is independent of
iterator rank and no mutable registry is consulted by the closure.
-/

universe u v

namespace STC

@[expose] public section

section Snapshot

variable {N : Type u} {K : Type v} [DecidableEq N] [DecidableEq K]

/-- Immutable finite data used by support proofs. -/
structure SupportSnapshot (N : Type u) (K : Type v)
    [DecidableEq N] [DecidableEq K] where
  dom : Finset N
  retired : N → Bool
  parent : N → Option N
  requires : N → Finset K
  provides : N → Finset K
  birth : N → Nat

/-- A provider of `a` satisfies one requirement of dependent `b`. -/
def Precedes (s : SupportSnapshot N K) (a b : N) : Prop :=
  (s.provides a ∩ s.requires b).Nonempty

/-- The parent edge points from parent `a` to child `b`. -/
def ParentEdge (s : SupportSnapshot N K) (a b : N) : Prop :=
  s.parent b = some a

/-- Forward support direction: provider/parent to dependent/child. -/
def SupportRel (s : SupportSnapshot N K) (a b : N) : Prop :=
  Precedes s a b ∨ ParentEdge s a b

instance (s : SupportSnapshot N K) (a b : N) : Decidable (SupportRel s a b) := by
  unfold SupportRel Precedes ParentEdge
  infer_instance

/-- Converse relation used when recursively descending from a dependent. -/
def SupportDep (s : SupportSnapshot N K) (b a : N) : Prop :=
  SupportRel s a b

def ParentSupported (s : SupportSnapshot N K) (A : Set N) (n : N) : Prop :=
  s.parent n = none ∨ ∃ p, s.parent n = some p ∧ p ∈ A

def ProvidersSupported (s : SupportSnapshot N K) (A : Set N) (n : N) : Prop :=
  ∀ k, k ∈ s.requires n → ∃ m, m ∈ A ∧ k ∈ s.provides m

/-- Positive support clause; the candidate set occurs only positively. -/
def SupportClause (s : SupportSnapshot N K) (A : Set N) (n : N) : Prop :=
  n ∈ s.dom ∧ s.retired n = false ∧
    ParentSupported s A n ∧ ProvidersSupported s A n

/-- The positive support operator. -/
def SupportOperator (s : SupportSnapshot N K) (A : Set N) : Set N :=
  {n | SupportClause s A n}

def Prefixed (s : SupportSnapshot N K) (A : Set N) : Prop :=
  SupportOperator s A ⊆ A

/-- Canonical support, defined as the intersection of all prefixed sets. -/
def SupportSet (s : SupportSnapshot N K) : Set N :=
  {n | ∀ A : Set N, Prefixed s A → n ∈ A}

theorem supportClause_mono (s : SupportSnapshot N K) {A B : Set N}
    (hAB : A ⊆ B) {n : N} :
    SupportClause s A n → SupportClause s B n := by
  intro h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rcases h.2.2.1 with hroot | ⟨p, hp, hpa⟩
    · exact Or.inl hroot
    · exact Or.inr ⟨p, hp, hAB hpa⟩
  · intro k hk
    rcases h.2.2.2 k hk with ⟨m, hm, hmk⟩
    exact ⟨m, hAB hm, hmk⟩

theorem supportSet_least (s : SupportSnapshot N K) {A : Set N}
    (hA : Prefixed s A) : SupportSet s ⊆ A := by
  intro n hn
  exact hn A hA

theorem supportSet_prefixed (s : SupportSnapshot N K) :
    Prefixed s (SupportSet s) := by
  intro n hn A hA
  apply hA
  exact supportClause_mono s (supportSet_least s hA) hn

theorem supportOperator_prefixed (s : SupportSnapshot N K) :
    Prefixed s (SupportOperator s (SupportSet s)) := by
  intro n hn
  exact supportClause_mono s (supportSet_prefixed s) hn

theorem supportSet_fixed (s : SupportSnapshot N K) :
    SupportOperator s (SupportSet s) = SupportSet s := by
  apply Set.Subset.antisymm
  · exact supportSet_prefixed s
  · intro n hn
    exact (supportSet_least (A := SupportOperator s (SupportSet s)) s
      (supportOperator_prefixed s)) hn

/-- A visible strict rank certificate for every support edge. -/
structure SupportOrder (s : SupportSnapshot N K) where
  rank : N → Nat
  edge_lt : ∀ {a b}, a ∈ s.dom → b ∈ s.dom →
    SupportRel s a b → rank a < rank b

abbrev RankCertificate (s : SupportSnapshot N K) := SupportOrder s

def SupportWF (s : SupportSnapshot N K) : Prop := Nonempty (SupportOrder s)

theorem supportDep_rank_lt (s : SupportSnapshot N K) (o : SupportOrder s)
    {b a : N} (hb : b ∈ s.dom) (ha : a ∈ s.dom)
    (h : SupportDep s b a) : o.rank a < o.rank b :=
  o.edge_lt ha hb h

/-- Well-foundedness of the converse relation on the committed domain. -/
theorem supportDep_wellFounded (s : SupportSnapshot N K) (o : SupportOrder s) :
    WellFounded (fun (x y : {n // n ∈ s.dom}) => SupportDep s y.1 x.1) := by
  let r : {n // n ∈ s.dom} → Nat := fun x => o.rank x.1
  have hw : WellFounded (fun x y => r x < r y) := wellFounded_lt.onFun
  apply hw.mono
  intro a b hab
  exact supportDep_rank_lt s o b.property a.property hab

structure NoLateRegistration (s : SupportSnapshot N K) : Prop where
  birth_strict : ∀ {a b}, a ∈ s.dom → b ∈ s.dom →
    SupportRel s a b → s.birth a < s.birth b

def NoLateRegistration.toOrder {s : SupportSnapshot N K}
    (h : NoLateRegistration s) : SupportOrder s :=
  { rank := s.birth, edge_lt := h.birth_strict }

/-- A committed snapshot records the frozen domain and its support certificate. -/
structure CommittedSnapshot (s : SupportSnapshot N K) where
  committed : Finset N
  committed_subset : committed ⊆ s.dom
  domain_committed : ∀ {n}, n ∈ s.dom → n ∈ committed
  order : SupportOrder s

theorem committed_domain_exact (s : SupportSnapshot N K)
    (c : CommittedSnapshot s) : c.committed = s.dom := by
  ext n
  constructor
  · intro h
    exact c.committed_subset h
  · intro h
    exact c.domain_committed h

end Snapshot

end

end STC
