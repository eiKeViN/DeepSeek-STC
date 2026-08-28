module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.List.Pairwise
public import Mathlib.Logic.Equiv.Defs
public import STC.Alpha.Core
public import STC.State.Observation

/-!
# The trace/reference freshness boundary

The P6-T03 orchestration/trace interface of the ADR-04 architecture: current versus
ever-issued freshness, the monotone name ledger, the explicit permutation transport of
finite name sets, `Option` parent/reference fields, and ledgers, the finite-support
trace shell with no-reuse, and the product boundary carrying the state together with
its trace metadata.  This file is the deliberate T03 boundary split; it is imported
only by `STC.Alpha.Transport`.

The default core observation on the boundary projects only the state component;
an explicitly name-aware observation may additionally compare the trace metadata.

## Main declarations

* `ParentRef`, `NameLedger`, `CurrentFresh`, `EverFresh`, `LedgerSound`;
* `renameFinset`, `renameParentRef`, `renameLedger` and their transport laws;
* `AllocationAllowed`, `allocate?`: the explicit success/undefined allocation helper;
* `NameTrace`, `TraceSupport`, `TraceNoReuse`, `renameNameTrace` and their transports;
* `AlphaBoundary`, `renameBoundary`, `coreBoundaryObs`, `nameAwareBoundaryObs`.
-/

universe u v

namespace STC

@[expose] public section

variable {N : Type u} [DecidableEq N] {S : Type v}

/-! ### Lifetime freshness primitives -/

section Freshness

/-- The parent/reference carrier: `none` is the synthetic root marker and never a
registry/provider entry. -/
abbrev ParentRef (N : Type u) := Option N

/-- The monotone ever-issued name ledger: names are only ever inserted. -/
structure NameLedger (N : Type u) [DecidableEq N] where
  everIssued : Finset N

/-- Current-registry freshness: the name is absent from the current registry domain. -/
def CurrentFresh (current : Finset N) (n : N) : Prop :=
  n ∉ current

/-- Ever-issued freshness: the name has never been issued on this ledger. -/
def EverFresh (ledger : NameLedger N) (n : N) : Prop :=
  n ∉ ledger.everIssued

/-- Ledger soundness: every current name has been issued. -/
def LedgerSound (current : Finset N) (ledger : NameLedger N) : Prop :=
  current ⊆ ledger.everIssued

/-! #### Permutation transport of finite name data -/

/-- Rename a finite name set by the permutation action. -/
def renameFinset (χ : Equiv.Perm N) (s : Finset N) : Finset N :=
  s.map χ.toEmbedding

omit [DecidableEq N] in
/-- The membership transport of `renameFinset` through the inverse permutation. -/
theorem renameFinset_mem (χ : Equiv.Perm N) (s : Finset N) (n : N) :
    n ∈ renameFinset χ s ↔ χ.symm n ∈ s := by
  simp [renameFinset, Finset.mem_map_equiv]

omit [DecidableEq N] in
/-- `renameFinset` by the identity permutation is the identity map. -/
theorem renameFinset_id :
    renameFinset (Equiv.refl N) = (id : Finset N → Finset N) := by
  funext s
  ext n
  simp only [renameFinset]
  rw [Finset.mem_map_equiv]
  change (Equiv.refl N).symm n ∈ s ↔ n ∈ s
  simp

omit [DecidableEq N] in
/-- `renameFinset` accumulates over permutation composition in the action order. -/
theorem renameFinset_comp (χ ψ : Equiv.Perm N) :
    renameFinset (χ * ψ) = renameFinset χ ∘ renameFinset ψ := by
  have hsymm : (χ * ψ).symm = ψ.symm * χ.symm := by
    show (χ * ψ)⁻¹ = ψ⁻¹ * χ⁻¹
    simp
  funext s
  ext n
  change n ∈ renameFinset (χ * ψ) s ↔ n ∈ renameFinset χ (renameFinset ψ s)
  simp only [renameFinset]
  rw [Finset.mem_map_equiv, Finset.mem_map_equiv]
  simp [hsymm]

/-- Rename an optional parent/reference field; `none` is fixed. -/
def renameParentRef (χ : Equiv.Perm N) (parent : ParentRef N) : ParentRef N :=
  parent.map (χ : N → N)

omit [DecidableEq N] in
/-- The synthetic root is fixed by every renaming. -/
theorem renameParentRef_none (χ : Equiv.Perm N) :
    renameParentRef χ none = none := rfl

omit [DecidableEq N] in
/-- `renameParentRef` by the identity permutation is the identity map. -/
theorem renameParentRef_id : renameParentRef (Equiv.refl N) = id := by
  funext parent
  cases parent <;> simp [renameParentRef]

omit [DecidableEq N] in
/-- `renameParentRef` accumulates over permutation composition in the action order. -/
theorem renameParentRef_comp (χ ψ : Equiv.Perm N) :
    renameParentRef (χ * ψ) = renameParentRef χ ∘ renameParentRef ψ := by
  funext parent
  cases parent <;> simp [renameParentRef]

/-- Rename the ever-issued ledger. -/
def renameLedger (χ : Equiv.Perm N) (ledger : NameLedger N) : NameLedger N :=
  { everIssued := renameFinset χ ledger.everIssued }

/-- The ledger projection of a renamed ledger. -/
theorem renameLedger_everIssued (χ : Equiv.Perm N) (ledger : NameLedger N) :
    (renameLedger χ ledger).everIssued = renameFinset χ ledger.everIssued := rfl

/-- `renameLedger` by the identity permutation is the identity map. -/
theorem renameLedger_id : renameLedger (Equiv.refl N) = (id : NameLedger N → NameLedger N) := by
  funext ledger
  cases ledger
  simp [renameLedger, renameFinset_id]

/-- `renameLedger` accumulates over permutation composition in the action order. -/
theorem renameLedger_comp (χ ψ : Equiv.Perm N) :
    renameLedger (χ * ψ) = renameLedger χ ∘ renameLedger ψ := by
  funext ledger
  cases ledger
  simp [renameLedger, renameFinset_comp]

/-! #### Freshness transport -/

omit [DecidableEq N] in
/-- Current freshness transports through the permutation action. -/
theorem currentFresh_rename (χ : Equiv.Perm N) {current : Finset N} {n : N} :
    CurrentFresh (renameFinset χ current) (χ n) ↔ CurrentFresh current n := by
  have hm : χ n ∈ renameFinset χ current ↔ n ∈ current := by
    simp [renameFinset]
  simpa [CurrentFresh] using (not_congr hm)

/-- Ever-issued freshness transports through the permutation action. -/
theorem everFresh_rename (χ : Equiv.Perm N) {ledger : NameLedger N} {n : N} :
    EverFresh (renameLedger χ ledger) (χ n) ↔ EverFresh ledger n := by
  have hm : χ n ∈ (renameLedger χ ledger).everIssued ↔ n ∈ ledger.everIssued := by
    simp [renameLedger, renameFinset]
  simpa [EverFresh] using (not_congr hm)

/-- Ledger soundness transports through the permutation action, in both directions. -/
theorem ledgerSound_rename (χ : Equiv.Perm N) {current : Finset N} {ledger : NameLedger N} :
    LedgerSound (renameFinset χ current) (renameLedger χ ledger) ↔
      LedgerSound current ledger := by
  constructor
  · intro h n hn
    have hn' : χ n ∈ renameFinset χ current := by
      simpa [renameFinset, Finset.mem_map_equiv] using hn
    have hled' := h hn'
    simpa [renameLedger, renameFinset, Finset.mem_map_equiv] using hled'
  · intro h n hn
    have hback : χ.symm n ∈ current := by
      simpa [renameFinset, Finset.mem_map_equiv] using hn
    have hled := h hback
    simpa [renameLedger, renameFinset, Finset.mem_map_equiv] using hled

/-! #### Allocation -/

/-- Allocation is allowed exactly when the candidate is currently fresh, ever fresh,
and the supplied parent-permission predicate holds.  Parent permission is an explicit
predicate over `ParentRef`; `none` is the synthetic root marker and does not require a
provider entry. -/
def AllocationAllowed (parentAllowed : Finset N → ParentRef N → Prop)
    (current : Finset N) (ledger : NameLedger N) (parent : ParentRef N) (n : N) : Prop :=
  CurrentFresh current n ∧ EverFresh ledger n ∧ parentAllowed current parent

/-- The explicit allocation helper: on success it inserts the candidate into both the
current set and the ever-issued ledger; on failure it returns `none`, which is plain
undefinedness and never an `ExecResult.failure` unless a caller supplies a diagnostic,
boundary, and prefix undo.  The guard is written out explicitly (`AllocationAllowed`
unfolded) so that the decidable instance search never has to reduce a compound
predicate definition. -/
def allocate? (parentAllowed : Finset N → ParentRef N → Prop)
    [hdec : ∀ current parent, Decidable (parentAllowed current parent)]
    (current : Finset N) (ledger : NameLedger N) (parent : ParentRef N) (n : N) :
    Option (Finset N × NameLedger N) :=
  if n ∉ current ∧ n ∉ ledger.everIssued ∧ parentAllowed current parent then
    some (insert n current, { everIssued := insert n ledger.everIssued })
  else none

/-- A successful allocation returns exactly the insert-updated pair and was allowed. -/
theorem allocate?_some (parentAllowed : Finset N → ParentRef N → Prop)
    [hdec : ∀ current parent, Decidable (parentAllowed current parent)]
    {current current' : Finset N} {ledger ledger' : NameLedger N}
    {parent : ParentRef N} {n : N}
    (h : allocate? parentAllowed current ledger parent n = some (current', ledger')) :
    current' = insert n current ∧
      ledger'.everIssued = insert n ledger.everIssued ∧
        AllocationAllowed parentAllowed current ledger parent n := by
  unfold allocate? at h
  by_cases hAllowed : n ∉ current ∧ n ∉ ledger.everIssued ∧ parentAllowed current parent
  · simp [hAllowed] at h
    rcases h with ⟨hcurrent, hledger⟩
    subst current'
    subst ledger'
    exact ⟨rfl, rfl, hAllowed⟩
  · simp [hAllowed] at h

/-- A disallowed allocation returns `none`. -/
theorem allocate?_none (parentAllowed : Finset N → ParentRef N → Prop)
    [hdec : ∀ current parent, Decidable (parentAllowed current parent)]
    {current : Finset N} {ledger : NameLedger N} {parent : ParentRef N} {n : N}
    (h : ¬ AllocationAllowed parentAllowed current ledger parent n) :
    allocate? parentAllowed current ledger parent n = none := by
  unfold allocate?
  change ¬ (n ∉ current ∧ n ∉ ledger.everIssued ∧ parentAllowed current parent) at h
  simp [h]

/-- A successful allocation updates the ever-issued ledger monotonically. -/
theorem allocate?_monotone (parentAllowed : Finset N → ParentRef N → Prop)
    [hdec : ∀ current parent, Decidable (parentAllowed current parent)]
    {current current' : Finset N} {ledger ledger' : NameLedger N}
    {parent : ParentRef N} {n : N}
    (h : allocate? parentAllowed current ledger parent n = some (current', ledger')) :
    ledger.everIssued ⊆ ledger'.everIssued := by
  have hs := allocate?_some parentAllowed h
  rw [hs.2.1]
  intro n hn
  exact Finset.mem_insert_of_mem hn

/-- Allocation allowedness transports through the permutation action when the parent
permission predicate transports: the freshness conjuncts always transport. -/
theorem allocationAllowed_rename (parentAllowed : Finset N → ParentRef N → Prop)
    (hparent : ∀ {χ : Equiv.Perm N} {current : Finset N} {parent : ParentRef N},
      parentAllowed current parent ↔
        parentAllowed (renameFinset χ current) (renameParentRef χ parent))
    (χ : Equiv.Perm N) {current : Finset N} {ledger : NameLedger N}
    {parent : ParentRef N} {n : N} :
    AllocationAllowed parentAllowed (renameFinset χ current) (renameLedger χ ledger)
        (renameParentRef χ parent) (χ n) ↔
      AllocationAllowed parentAllowed current ledger parent n := by
  constructor
  · intro h
    exact ⟨(currentFresh_rename χ).1 h.1, (everFresh_rename χ).1 h.2.1,
      (hparent (χ := χ)).2 h.2.2⟩
  · intro h
    exact ⟨(currentFresh_rename χ).2 h.1, (everFresh_rename χ).2 h.2.1,
      (hparent (χ := χ)).1 h.2.2⟩

end Freshness

/-! ### The finite-support trace shell -/

section TraceShell

/-- The minimal ADR-04 trace metadata record: the initial issued set, the listed
allocations, parent/reference labels, finite boundary snapshots, and the declared
finite support envelope. -/
structure NameTrace (N : Type u) [DecidableEq N] where
  initialIssued : Finset N
  allocations : List N
  parents : List (ParentRef N)
  references : List (ParentRef N)
  boundarySnapshots : List (Finset N)
  support : Finset N

/-- The declared support envelope covers the initial set, every listed allocation,
parent, reference, and boundary snapshot.  The envelope is not automatically the exact
minimal set of names occurring in the trace. -/
structure TraceSupport (trace : NameTrace N) : Prop where
  initial : trace.initialIssued ⊆ trace.support
  allocations : ∀ n, n ∈ trace.allocations → n ∈ trace.support
  parents : ∀ parent, parent ∈ trace.parents → ∀ n, parent = some n → n ∈ trace.support
  references : ∀ reference, reference ∈ trace.references → ∀ n, reference = some n →
    n ∈ trace.support
  snapshots : ∀ snapshot, snapshot ∈ trace.boundarySnapshots → snapshot ⊆ trace.support

/-- No-reuse of the finite shell: the listed allocations are pairwise distinct and
fresh relative to the initial issued set. -/
def TraceNoReuse (trace : NameTrace N) : Prop :=
  trace.allocations.Pairwise (· ≠ ·) ∧
    ∀ n, n ∈ trace.allocations → n ∉ trace.initialIssued

/-- Rename every name-bearing trace field by the permutation action. -/
def renameNameTrace (χ : Equiv.Perm N) (trace : NameTrace N) : NameTrace N :=
  { initialIssued := renameFinset χ trace.initialIssued
    allocations := trace.allocations.map (χ : N → N)
    parents := trace.parents.map (renameParentRef χ)
    references := trace.references.map (renameParentRef χ)
    boundarySnapshots := trace.boundarySnapshots.map (renameFinset χ)
    support := renameFinset χ trace.support }

/-- `renameNameTrace` by the identity permutation is the identity. -/
theorem renameNameTrace_id (trace : NameTrace N) :
    renameNameTrace (Equiv.refl N) trace = trace := by
  cases trace
  simp [renameNameTrace, renameFinset_id, renameParentRef_id]

/-- `renameNameTrace` accumulates over permutation composition in the action order. -/
theorem renameNameTrace_comp (χ ψ : Equiv.Perm N) (trace : NameTrace N) :
    renameNameTrace (χ * ψ) trace = renameNameTrace χ (renameNameTrace ψ trace) := by
  cases trace
  simp [renameNameTrace, renameFinset_comp, renameParentRef_comp]

/-- Declared trace support transports through the permutation action. -/
theorem traceSupport_rename (χ : Equiv.Perm N) {trace : NameTrace N}
    (h : TraceSupport trace) : TraceSupport (renameNameTrace χ trace) where
  initial := by
    intro n hn
    have hback : χ.symm n ∈ trace.initialIssued := by
      simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv] using hn
    have hsup := h.initial hback
    simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv] using hsup
  allocations := by
    intro n hn
    have hn' : n ∈ trace.allocations.map (χ : N → N) := by
      simpa [renameNameTrace] using hn
    rcases List.mem_map.mp hn' with ⟨a, ha, hχa⟩
    have ha' : a = χ.symm n := by
      exact (Equiv.apply_eq_iff_eq (χ : Equiv.Perm N)).mp (by simpa using hχa)
    subst ha'
    have hsup := h.allocations (χ.symm n) ha
    simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv] using hsup
  parents := by
    intro parent hp n hn
    have hp' : parent ∈ trace.parents.map (renameParentRef χ) := by
      simpa [renameNameTrace] using hp
    rcases List.mem_map.mp hp' with ⟨p0, hp0, hχp0⟩
    rw [← hχp0] at hn
    cases p0 with
    | none => simp [renameParentRef] at hn
    | some n0 =>
        have hχ : χ n0 = n := by
          simpa [renameParentRef] using Option.some.inj (by simpa [renameParentRef] using hn)
        have hsup := h.parents (some n0) hp0 n0 rfl
        simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv, ← hχ] using hsup
  references := by
    intro reference hr n hn
    have hr' : reference ∈ trace.references.map (renameParentRef χ) := by
      simpa [renameNameTrace] using hr
    rcases List.mem_map.mp hr' with ⟨r0, hr0, hχr0⟩
    rw [← hχr0] at hn
    cases r0 with
    | none => simp [renameParentRef] at hn
    | some n0 =>
        have hχ : χ n0 = n := by
          simpa [renameParentRef] using Option.some.inj (by simpa [renameParentRef] using hn)
        have hsup := h.references (some n0) hr0 n0 rfl
        simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv, ← hχ] using hsup
  snapshots := by
    intro b hb
    have hb' : b ∈ trace.boundarySnapshots.map (renameFinset χ) := by
      simpa [renameNameTrace] using hb
    rcases List.mem_map.mp hb' with ⟨b0, hb0, hχb0⟩
    intro n hn
    subst b
    have hback : χ.symm n ∈ b0 := by
      simpa [renameFinset, Finset.mem_map_equiv] using hn
    have hsup := (h.snapshots b0 hb0) hback
    simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv] using hsup

/-- No-reuse transports through the permutation action. -/
theorem traceNoReuse_rename (χ : Equiv.Perm N) {trace : NameTrace N}
    (h : TraceNoReuse trace) : TraceNoReuse (renameNameTrace χ trace) := by
  constructor
  · have hpair : (trace.allocations.map (χ : N → N)).Pairwise (· ≠ ·) := by
      rw [List.pairwise_map]
      rw [List.pairwise_iff_get]
      intro i j hij hχ
      have hne := (List.pairwise_iff_get.mp h.1) i j hij
      exact hne ((Equiv.injective χ) hχ)
    simpa [renameNameTrace] using hpair
  · intro n hn
    have hn' : n ∈ trace.allocations.map (χ : N → N) := by
      simpa [renameNameTrace] using hn
    rcases List.mem_map.mp hn' with ⟨a, ha, hχa⟩
    have ha' : a = χ.symm n := by
      exact (Equiv.apply_eq_iff_eq (χ : Equiv.Perm N)).mp (by simpa using hχa)
    subst ha'
    have hfresh := h.2 (χ.symm n) ha
    intro hmem
    apply hfresh
    simpa [renameNameTrace, renameFinset, Finset.mem_map_equiv] using hmem

end TraceShell

/-! ### The product boundary -/

section BoundaryProduct

/-- The product boundary: the state together with its trace metadata.  This is the
carrier on which a freshness-sensitive transition may be considered Markovian; the
default core observation still projects only the state component. -/
structure AlphaBoundary (N : Type u) (S : Type v) [DecidableEq N] where
  state : S
  trace : NameTrace N

/-- Rename the product boundary: the state by the action, every name-bearing trace
field by the permutation. -/
def renameBoundary (A : AlphaAction N S) (χ : Equiv.Perm N)
    (boundary : AlphaBoundary N S) : AlphaBoundary N S :=
  { state := A.act χ boundary.state, trace := renameNameTrace χ boundary.trace }

/-- `renameBoundary` by the identity permutation is the identity. -/
theorem renameBoundary_id (A : AlphaAction N S) (boundary : AlphaBoundary N S) :
    renameBoundary A (Equiv.refl N) boundary = boundary := by
  cases boundary
  simp [renameBoundary, A.act_id, renameNameTrace_id]

/-- `renameBoundary` accumulates over permutation composition in the action order. -/
theorem renameBoundary_comp (A : AlphaAction N S) (χ ψ : Equiv.Perm N)
    (boundary : AlphaBoundary N S) :
    renameBoundary A (χ * ψ) boundary = renameBoundary A χ (renameBoundary A ψ boundary) := by
  cases boundary
  simp [renameBoundary, A.act_comp, renameNameTrace_comp]

/-- The default core observation on the boundary: only the state component, exactly as
the P5 default `CoreStateObs` projects. -/
def coreBoundaryObs (R : RelSpec S) : RelSpec (AlphaBoundary N S) :=
  pullbackRelSpec (fun boundary => boundary.state) R

/-- The core observation ignores the trace metadata: states related in the core make
the boundaries related whatever their ledgers and traces are. -/
theorem coreBoundaryObs_ignores_trace (R : RelSpec S)
    {boundary boundary' : AlphaBoundary N S} (hstate : R.rel boundary.state boundary'.state) :
    (coreBoundaryObs R).rel boundary boundary' :=
  hstate

/-- The explicit name-aware boundary observation: the core observation plus exact
equality of the trace metadata.  This is not called alpha equivalence. -/
def nameAwareBoundaryObs (R : RelSpec S) : RelSpec (AlphaBoundary N S) :=
  RelSpec.conj (coreBoundaryObs R)
    (pullbackRelSpec (fun boundary => boundary.trace) (equality (NameTrace N)))

/-- The name-aware observation distinguishes boundaries that agree on the core state
but differ in trace metadata, while the core observation relates them. -/
theorem nameAwareBoundaryObs_distinguishes (R : RelSpec S)
    {boundary boundary' : AlphaBoundary N S}
    (_hstate : R.rel boundary.state boundary'.state)
    (htrace : boundary.trace ≠ boundary'.trace) :
    ¬ (nameAwareBoundaryObs R).rel boundary boundary' := by
  intro h
  change (RelSpec.conj (coreBoundaryObs R)
    (pullbackRelSpec (fun boundary => boundary.trace) (equality (NameTrace N)))).rel
      boundary boundary' at h
  change (coreBoundaryObs R).rel boundary boundary' ∧
    boundary.trace = boundary'.trace at h
  exact htrace h.2

end BoundaryProduct

end

end STC
