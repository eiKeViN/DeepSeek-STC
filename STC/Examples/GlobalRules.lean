module

public import STC.Control.Rules
public import STC.Examples.GlobalModel

/-!
# Global rule witnesses

The finite fixture inhabits every concrete constructor of the authoritative
rules: a linear trace over two acting fibers with a nonempty requirement and
provision, nested registration, async diversion (both branches admissible
under the A.async policy), and a real raise/cleanup path; plus the ADR-09
three-edge cycle-trace candidate (r = 0, c = 1, n = 2; former provider p = 3)
ending in the corrected cyclic support projection with an acyclic precedence
fragment and a well-formed endpoint.
-/

namespace STC.Examples.GlobalRules

open STC STC.State STC.Control

@[expose] public section

abbrev Cell := FiberCell Nat Nat Nat Unit Nat (List Nat) Unit Nat
abbrev State := GlobalState Nat Nat Nat Unit Nat (List Nat) Unit Nat Nat
abbrev Sem := ComponentSemantics Nat State Nat Unit Nat (List Nat) Unit Nat
abbrev OLabel := GlobalOrchestrationLabel Nat Cell
abbrev LLabel := GlobalLifecycleLabel Nat Nat Nat Unit (FailureEvidence State Nat (List Nat))

/-! ### Fixture cells -/

abbrev coeffects0 : Finmap (fun _ : Nat => Nat) :=
  Finmap.insert 10 (0 : Nat) (Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)))

abbrev s0 : State :=
  { ambient := 10, registry := ∅, coeffects := coeffects0,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

abbrev cell1 : Cell :=
  { incarnation := 1, parent := none, birth := 0,
    component := { key := 1, requires := ∅, provides := {10}, actionCode := (), iteratorCode := 1, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cell2 : Cell :=
  { incarnation := 2, parent := some 1, birth := 1,
    component := { key := 2, requires := {10}, provides := {20}, actionCode := (), iteratorCode := 3, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 3, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cell3 : Cell :=
  { incarnation := 3, parent := none, birth := 2,
    component := { key := 3, requires := {10}, provides := ∅, actionCode := (), iteratorCode := 1, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cell4 : Cell :=
  { incarnation := 4, parent := none, birth := 3,
    component := { key := 4, requires := {10}, provides := ∅, actionCode := (), iteratorCode := 0, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 0, accumulatorCode := [], flightCode := none, failureData := none } }

abbrev cell5 : Cell :=
  { incarnation := 5, parent := none, birth := 4,
    component := { key := 5, requires := {10}, provides := ∅, actionCode := (), iteratorCode := 99, accumulatorCode := [], flightCode := (), failureCode := 0 },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 99, accumulatorCode := [], flightCode := none, failureData := none } }

/-! ### The external semantics -/

/-- The fixture's ranked iterator: rank is the code itself. Code 99 raises the
real error 7; positive codes yield the continuation `code - 1` with the
registration retirement inverse `[2]` when the iterator code is 1 (the parent
harvests the outstanding child-retirement inverse) and `[]` otherwise; code 0
halts. The stage body never changes the state. -/
def fixtureStage (code : Nat) (before : State) : Option (State.StageResult State Nat (List Nat) Nat) :=
  if _hfail : code = 99 then
    some (.raise 7)
  else if _hpos : 0 < code then
    if _hone : code = 1 then
      some (.yield before [2] (code - 1))
    else
      some (.yield before [] (code - 1))
  else
    some (.halt before [])

/-- A real landing: the landed state records the arrival in the ambient
counter; the landing inverse is the empty list. -/
def fixtureLanding (_token : Unit) (before : State) : Option (LandingOutcome State (List Nat) Nat) :=
  some (.landed { before with ambient := before.ambient + 1 } [])

/-- The nested-registration action: registers cell 2 when it is fresh and
returns the canonical retirement inverse `[2]`. -/
def fixtureAction (_code : Unit) (before : State) : Option (ActionResult State (List Nat)) :=
  match Finmap.lookup 2 before.registry with
  | none =>
      if _hfresh : 2 ∉ before.ledger.everIssued then
        some { state := allocate before 2 cell2, inverse? := some [2] }
      else none
  | some _ => none

/-- The registration undo: erase cell 2 and roll the ledger and history back. -/
def fixtureUndo (state : State) : Option State :=
  match Finmap.lookup 2 state.registry with
  | some _ =>
      some { ambient := state.ambient
             registry := Finmap.erase 2 state.registry
             coeffects := state.coeffects
             ledger := { everIssued := state.ledger.everIssued.erase 2 }
             allocationHistory := state.allocationHistory.dropLast }
  | none => none

/-- The accumulator executes the recorded retirement inverses in LIFO order:
each name in the list flips that fiber's retired flag (idempotent on an
already-retired cell). -/
def foldRetire (code : List Nat) (state : State) : State :=
  code.foldl (fun s n => (retire? s n).getD s) state

def fixtureAccumulator (code : List Nat) (state : State) : Option State :=
  some (foldRetire code state)

theorem cell_retire_idempotent {cell : Cell} (h : cell.retired = true) :
    { cell with retired := true } = cell := by
  cases cell
  subst h
  rfl

theorem finmap_insert_eq_of_lookup {n : Nat} {cell : Cell} {s : Finmap (fun _ : Nat => Cell)}
    (h : Finmap.lookup n s = some cell) : Finmap.insert n cell s = s := by
  apply Finmap.ext_lookup
  intro m
  by_cases hm : m = n
  · subst m
    rw [Finmap.lookup_insert, h]
  · rw [Finmap.lookup_insert_of_ne (a := n) (a' := m) s (by intro h; exact hm h)]

theorem finmap_erase_insert_eq {cell : Cell} {s : Finmap (fun _ : Nat => Cell)}
    (h : Finmap.lookup 2 s = none) : Finmap.erase 2 (Finmap.insert 2 cell s) = s := by
  apply Finmap.ext_lookup
  intro m
  by_cases hm : m = 2
  · subst m
    rw [Finmap.lookup_erase, h]
  · rw [Finmap.lookup_erase_ne (a := m) (a' := 2) hm]
    exact Finmap.lookup_insert_of_ne (a := 2) (a' := m) s (by intro h2; exact hm h2)

/-- One retire-step either leaves a name unchanged or flips its retired flag. -/
theorem retireStep_lookup (state : State) (n name : Nat) :
    Finmap.lookup name ((retire? state n).getD state).registry = Finmap.lookup name state.registry ∨
      (name = n ∧ ∃ cell, Finmap.lookup name state.registry = some cell ∧ cell.retired = false ∧
        Finmap.lookup name ((retire? state n).getD state).registry = some { cell with retired := true }) := by
  cases hlook : Finmap.lookup n state.registry with
  | none =>
      left
      unfold retire?
      rw [hlook]
      rfl
  | some cell =>
      by_cases hname : name = n
      · subst name
        cases hret : cell.retired with
        | true =>
            left
            unfold retire?
            rw [hlook]
            simp only [Option.map_some, Option.getD_some]
            have hcell : { cell with retired := true } = cell := cell_retire_idempotent hret
            rw [hcell]
            unfold updateFiber
            rw [finmap_insert_eq_of_lookup hlook]
            exact hlook
        | false =>
            right
            refine ⟨rfl, cell, ?_, hret, ?_⟩
            · exact hlook
            · unfold retire?
              rw [hlook]
              simp only [Option.map_some, Option.getD_some]
              exact updateFiber_lookup_eq state n { cell with retired := true }
      · left
        unfold retire?
        rw [hlook]
        simp only [Option.map_some, Option.getD_some]
        exact updateFiber_lookup_ne state (by intro h; exact hname h) { cell with retired := true }

/-- The fold's registry effect: every name is unchanged or flipped exactly at
a code member whose before-cell was unretired. -/
theorem foldRetire_lookup (code : List Nat) (state : State) (name : Nat) :
    Finmap.lookup name (foldRetire code state).registry = Finmap.lookup name state.registry ∨
      (name ∈ code ∧ ∃ cell, Finmap.lookup name state.registry = some cell ∧ cell.retired = false ∧
        Finmap.lookup name (foldRetire code state).registry = some { cell with retired := true }) := by
  induction code generalizing state with
  | nil => left; rfl
  | cons n code ih =>
      change Finmap.lookup name (foldRetire code ((retire? state n).getD state)).registry =
          Finmap.lookup name state.registry ∨
        (name ∈ n :: code ∧ ∃ cell, Finmap.lookup name state.registry = some cell ∧ cell.retired = false ∧
          Finmap.lookup name (foldRetire code ((retire? state n).getD state)).registry = some { cell with retired := true })
      have hstep := retireStep_lookup state n name
      have hih := ih ((retire? state n).getD state)
      rcases hih with hih | hih
      · rcases hstep with hstep | hstep
        · left
          exact hih.trans hstep
        · rcases hstep with ⟨hn, cell, hl, hret, ha⟩
          right
          refine ⟨by simp [hn], cell, hl, hret, ?_⟩
          rw [hih, ha]
      · rcases hih with ⟨hmem, cell, hl₁, hret₁, ha₁⟩
        right
        refine ⟨by simp [hmem], cell, ?_, hret₁, ?_⟩
        · rcases hstep with hstep | hstep
          · rw [hstep] at hl₁
            exact hl₁
          · rcases hstep with ⟨_hn, cell0, _hl0, _hret0, ha0⟩
            rw [ha0] at hl₁
            have hcell : cell = { cell0 with retired := true } := (Option.some.inj hl₁).symm
            rw [hcell] at hret₁
            cases hret₁
        · exact ha₁

theorem foldRetire_coeffects (code : List Nat) (state : State) :
    (foldRetire code state).coeffects = state.coeffects := by
  induction code generalizing state with
  | nil => rfl
  | cons n code ih =>
      change (foldRetire code ((retire? state n).getD state)).coeffects = state.coeffects
      have hstep : ((retire? state n).getD state).coeffects = state.coeffects := by
        unfold retire?
        cases Finmap.lookup n state.registry with
        | none => rfl
        | some _ => rfl
      rw [← hstep]
      exact ih ((retire? state n).getD state)

theorem foldRetire_ledger (code : List Nat) (state : State) :
    (foldRetire code state).ledger = state.ledger := by
  induction code generalizing state with
  | nil => rfl
  | cons n code ih =>
      change (foldRetire code ((retire? state n).getD state)).ledger = state.ledger
      have hstep : ((retire? state n).getD state).ledger = state.ledger := by
        unfold retire?
        cases Finmap.lookup n state.registry with
        | none => rfl
        | some _ => rfl
      rw [← hstep]
      exact ih ((retire? state n).getD state)

theorem foldRetire_history (code : List Nat) (state : State) :
    (foldRetire code state).allocationHistory = state.allocationHistory := by
  induction code generalizing state with
  | nil => rfl
  | cons n code ih =>
      change (foldRetire code ((retire? state n).getD state)).allocationHistory = state.allocationHistory
      have hstep : ((retire? state n).getD state).allocationHistory = state.allocationHistory := by
        unfold retire?
        cases Finmap.lookup n state.registry with
        | none => rfl
        | some _ => rfl
      rw [← hstep]
      exact ih ((retire? state n).getD state)

theorem foldRetire_keys (code : List Nat) (state : State) :
    (foldRetire code state).registry.keys = state.registry.keys := by
  induction code generalizing state with
  | nil => rfl
  | cons n code ih =>
      change (foldRetire code ((retire? state n).getD state)).registry.keys = state.registry.keys
      have hstep : ((retire? state n).getD state).registry.keys = state.registry.keys := by
        unfold retire?
        cases hlook : Finmap.lookup n state.registry with
        | none => rfl
        | some cell =>
            change (updateFiber state n { cell with retired := true }).registry.keys = state.registry.keys
            rw [updateFiber_keys]
            exact Finset.insert_eq_self.mpr (by rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hlook]; rfl)
      rw [← hstep]
      exact ih ((retire? state n).getD state)

/-! ### The semantic relations -/

def semObserves (left right : State) : Prop := left.coeffects = right.coeffects

def semWritesWithin (env : Finset Nat) (left right : State) : Prop :=
  ∀ key, key ∉ env → Coeffect.lookup key left.coeffects = Coeffect.lookup key right.coeffects

def semRegistryFrame (left right : State) : Prop := left.registry = right.registry
def semDomainFrame (left right : State) : Prop := left.registry.keys = right.registry.keys
def semAllocationFrame (left right : State) : Prop := left.ledger = right.ledger ∧ left.allocationHistory = right.allocationHistory
def semContinuationStable (left right : State) : Prop := left.registry = right.registry

def semAccumulatorFrame (code : List Nat) (left right : State) : Prop :=
  left.ledger = right.ledger ∧ left.allocationHistory = right.allocationHistory ∧ left.coeffects = right.coeffects ∧
    ∀ name, Finmap.lookup name left.registry = Finmap.lookup name right.registry ∨
      (∃ cell, name ∈ code ∧ Finmap.lookup name left.registry = some cell ∧ cell.retired = false ∧
        Finmap.lookup name right.registry = some { cell with retired := true })

/-! ### The semantic laws -/

/-- The stage's semantic result shape: a success reaches exactly the source
state; the only raise is the code-99 error. -/
theorem fixtureStage_state_eq {code : Nat} {before : State}
    {result : State.StageResult State Nat (List Nat) Nat}
    (h : fixtureStage code before = some result) :
    result.state? = some before ∨ result = .raise 7 := by
  unfold fixtureStage at h
  by_cases hfail : code = 99
  · rw [dif_pos hfail] at h
    right
    exact (Option.some.inj h).symm
  · rw [dif_neg hfail] at h
    by_cases hpos : 0 < code
    · rw [dif_pos hpos] at h
      by_cases hone : code = 1
      · rw [dif_pos hone] at h
        left
        have hres : result = .yield before [2] (code - 1) := (Option.some.inj h).symm
        rw [hres]
        rfl
      · rw [dif_neg hone] at h
        left
        have hres : result = .yield before [] (code - 1) := (Option.some.inj h).symm
        rw [hres]
        rfl
    · rw [dif_neg hpos] at h
      left
      have hres : result = .halt before [] := (Option.some.inj h).symm
      rw [hres]
      rfl

theorem sem_action_writesWithinProvision :
    ∀ {code before result}, fixtureAction code before = some result →
      semWritesWithin ∅ before result.state := by
  intro code before result hacc
  change ∀ key, key ∉ (∅ : Finset Nat) →
    Coeffect.lookup key before.coeffects = Coeffect.lookup key result.state.coeffects
  intro key _hkey
  unfold fixtureAction at hacc
  cases hlook : Finmap.lookup 2 before.registry with
  | none =>
      simp only [hlook] at hacc
      by_cases hg : 2 ∉ before.ledger.everIssued
      · rw [dif_pos hg] at hacc
        have hres : result = { state := allocate before 2 cell2, inverse? := some [2] } := (Option.some.inj hacc).symm
        rw [hres]
        change Coeffect.lookup key before.coeffects = Coeffect.lookup key (allocate before 2 cell2).coeffects
        rw [allocate_coeffects]
      · rw [dif_neg hg] at hacc
        cases hacc
  | some _ =>
      simp only [hlook] at hacc
      cases hacc

theorem sem_action_frame :
    ∀ {code before result}, fixtureAction code before = some result →
      semObserves before result.state := by
  intro code before result hacc
  change before.coeffects = result.state.coeffects
  unfold fixtureAction at hacc
  cases hlook : Finmap.lookup 2 before.registry with
  | none =>
      simp only [hlook] at hacc
      by_cases hg : 2 ∉ before.ledger.everIssued
      · rw [dif_pos hg] at hacc
        have hres : result = { state := allocate before 2 cell2, inverse? := some [2] } := (Option.some.inj hacc).symm
        rw [hres]
        change before.coeffects = (allocate before 2 cell2).coeffects
        rw [allocate_coeffects]
      · rw [dif_neg hg] at hacc
        cases hacc
  | some _ =>
      simp only [hlook] at hacc
      cases hacc

theorem sem_inverse_law :
    ∀ {code before result}, fixtureAction code before = some result →
      fixtureUndo result.state = some before := by
  intro code before result hacc
  unfold fixtureAction at hacc
  cases hlook : Finmap.lookup 2 before.registry with
  | none =>
      simp only [hlook] at hacc
      by_cases hg : 2 ∉ before.ledger.everIssued
      · rw [dif_pos hg] at hacc
        have hres : result = { state := allocate before 2 cell2, inverse? := some [2] } := (Option.some.inj hacc).symm
        rw [hres]
        unfold fixtureUndo
        have hlook2 : Finmap.lookup 2 (allocate before 2 cell2).registry = some cell2 :=
          allocate_lookup_fresh before 2 cell2
        rw [hlook2]
        change some { ambient := (allocate before 2 cell2).ambient, registry := Finmap.erase 2 (allocate before 2 cell2).registry, coeffects := (allocate before 2 cell2).coeffects, ledger := { everIssued := (allocate before 2 cell2).ledger.everIssued.erase 2 }, allocationHistory := (allocate before 2 cell2).allocationHistory.dropLast } = some before
        refine congrArg some ?_
        cases before
        simp [allocate, finmap_erase_insert_eq, hlook, hg]
      · rw [dif_neg hg] at hacc
        cases hacc
  | some _ =>
      simp only [hlook] at hacc
      cases hacc

theorem sem_stage_frame :
    ∀ {code before result after}, fixtureStage code before = some result →
      result.state? = some after → semObserves before after := by
  intro code before result after hstage hstate
  change before.coeffects = after.coeffects
  rcases fixtureStage_state_eq hstage with hstate' | hraise
  · rw [hstate'] at hstate
    have hafter : before = after := Option.some.inj hstate
    rw [hafter]
  · rw [hraise] at hstate
    simp [State.StageResult.state?] at hstate

theorem sem_stage_writesWithinProvision :
    ∀ {code before result after}, fixtureStage code before = some result →
      result.state? = some after → semWritesWithin ∅ before after := by
  intro code before result after hstage hstate
  change ∀ key, key ∉ (∅ : Finset Nat) → Coeffect.lookup key before.coeffects = Coeffect.lookup key after.coeffects
  intro key _hkey
  rcases fixtureStage_state_eq hstage with hstate' | hraise
  · rw [hstate'] at hstate
    have hafter : before = after := Option.some.inj hstate
    rw [hafter]
  · rw [hraise] at hstate
    simp [State.StageResult.state?] at hstate

theorem sem_stage_registryFrame :
    ∀ {code before result after}, fixtureStage code before = some result →
      result.state? = some after → semRegistryFrame before after := by
  intro code before result after hstage hstate
  change before.registry = after.registry
  rcases fixtureStage_state_eq hstage with hstate' | hraise
  · rw [hstate'] at hstate
    have hafter : before = after := Option.some.inj hstate
    rw [hafter]
  · rw [hraise] at hstate
    simp [State.StageResult.state?] at hstate

theorem sem_stage_allocationFrame :
    ∀ {code before result after}, fixtureStage code before = some result →
      result.state? = some after → semAllocationFrame before after := by
  intro code before result after hstage hstate
  change before.ledger = after.ledger ∧ before.allocationHistory = after.allocationHistory
  rcases fixtureStage_state_eq hstage with hstate' | hraise
  · rw [hstate'] at hstate
    have hafter : before = after := Option.some.inj hstate
    rw [hafter]
    exact ⟨rfl, rfl⟩
  · rw [hraise] at hstate
    simp [State.StageResult.state?] at hstate

theorem sem_relation_respect :
    ∀ {code left right left' right'}, semObserves left right →
      fixtureAction code left = some left' → fixtureAction code right = some right' →
        semObserves left'.state right'.state := by
  intro code left right left' right' hlr hl hr
  change left'.state.coeffects = right'.state.coeffects
  change left.coeffects = right.coeffects at hlr
  unfold fixtureAction at hl hr
  cases hl0 : Finmap.lookup 2 left.registry with
  | none =>
      simp only [hl0] at hl
      by_cases hgl : 2 ∉ left.ledger.everIssued
      · rw [dif_pos hgl] at hl
        have hl' : left' = { state := allocate left 2 cell2, inverse? := some [2] } := (Option.some.inj hl).symm
        rw [hl']
        cases hr0 : Finmap.lookup 2 right.registry with
        | none =>
            simp only [hr0] at hr
            by_cases hgr : 2 ∉ right.ledger.everIssued
            · rw [dif_pos hgr] at hr
              have hr' : right' = { state := allocate right 2 cell2, inverse? := some [2] } := (Option.some.inj hr).symm
              rw [hr']
              change (allocate left 2 cell2).coeffects = (allocate right 2 cell2).coeffects
              rw [allocate_coeffects, allocate_coeffects]
              exact hlr
            · rw [dif_neg hgr] at hr
              cases hr
        | some _ =>
            simp only [hr0] at hr
            cases hr
      · rw [dif_neg hgl] at hl
        cases hl
  | some _ =>
      simp only [hl0] at hl
      cases hl

theorem sem_rank_law :
    ∀ {code before result next inverse after}, fixtureStage code before = some result →
      result = .yield after inverse next → next < code := by
  intro code before result next inverse after hstage hyield
  unfold fixtureStage at hstage
  by_cases hfail : code = 99
  · rw [dif_pos hfail] at hstage
    have hres : result = .raise 7 := (Option.some.inj hstage).symm
    rw [hres] at hyield
    cases hyield
  · rw [dif_neg hfail] at hstage
    by_cases hpos : 0 < code
    · rw [dif_pos hpos] at hstage
      by_cases hone : code = 1
      · rw [dif_pos hone] at hstage
        have hres : result = .yield before [2] (code - 1) := (Option.some.inj hstage).symm
        rw [hres] at hyield
        have hnext : next = code - 1 := by
          injection hyield with _hbefore _hinverse hnext
          exact hnext.symm
        rw [hnext]
        change (code - 1) < code
        omega
      · rw [dif_neg hone] at hstage
        have hres : result = .yield before [] (code - 1) := (Option.some.inj hstage).symm
        rw [hres] at hyield
        have hnext : next = code - 1 := by
          injection hyield with _hbefore _hinverse hnext
          exact hnext.symm
        rw [hnext]
        change (code - 1) < code
        omega
    · rw [dif_neg hpos] at hstage
      have hres : result = .halt before [] := (Option.some.inj hstage).symm
      rw [hres] at hyield
      cases hyield

theorem sem_landing_stable :
    ∀ {token before state inverse}, fixtureLanding token before = some (.landed state inverse) →
      semContinuationStable before state := by
  intro token before state inverse hland
  change before.registry = state.registry
  unfold fixtureLanding at hland
  have hres : (.landed { before with ambient := before.ambient + 1 } [] : LandingOutcome State (List Nat) Nat) = .landed state inverse := Option.some.inj hland
  have hstate : state = { before with ambient := before.ambient + 1 } := by
    injection hres with hstate _hinverse
    exact hstate.symm
  rw [hstate]

theorem sem_landing_frame :
    ∀ {token before outcome after}, fixtureLanding token before = some outcome →
      outcome.state? = some after → semObserves before after := by
  intro token before outcome after hland hstate
  change before.coeffects = after.coeffects
  unfold fixtureLanding at hland
  have hres : (.landed { before with ambient := before.ambient + 1 } [] : LandingOutcome State (List Nat) Nat) = outcome := Option.some.inj hland
  rw [← hres] at hstate
  simp [LandingOutcome.state?] at hstate
  rw [← hstate]

theorem sem_landing_writesWithinProvision :
    ∀ {token before outcome after}, fixtureLanding token before = some outcome →
      outcome.state? = some after → semWritesWithin ∅ before after := by
  intro token before outcome after hland hstate
  change ∀ key, key ∉ (∅ : Finset Nat) → Coeffect.lookup key before.coeffects = Coeffect.lookup key after.coeffects
  intro key _hkey
  unfold fixtureLanding at hland
  have hres : (.landed { before with ambient := before.ambient + 1 } [] : LandingOutcome State (List Nat) Nat) = outcome := Option.some.inj hland
  rw [← hres] at hstate
  simp [LandingOutcome.state?] at hstate
  rw [← hstate]

theorem sem_landing_registryFrame :
    ∀ {token before outcome after}, fixtureLanding token before = some outcome →
      outcome.state? = some after → semRegistryFrame before after := by
  intro token before outcome after hland hstate
  change before.registry = after.registry
  unfold fixtureLanding at hland
  have hres : (.landed { before with ambient := before.ambient + 1 } [] : LandingOutcome State (List Nat) Nat) = outcome := Option.some.inj hland
  rw [← hres] at hstate
  simp [LandingOutcome.state?] at hstate
  rw [← hstate]

theorem sem_landing_allocationFrame :
    ∀ {token before outcome after}, fixtureLanding token before = some outcome →
      outcome.state? = some after → semAllocationFrame before after := by
  intro token before outcome after hland hstate
  change before.ledger = after.ledger ∧ before.allocationHistory = after.allocationHistory
  unfold fixtureLanding at hland
  have hres : (.landed { before with ambient := before.ambient + 1 } [] : LandingOutcome State (List Nat) Nat) = outcome := Option.some.inj hland
  rw [← hres] at hstate
  simp [LandingOutcome.state?] at hstate
  rw [← hstate]; simp

theorem sem_composeInverse_law :
    ∀ {a b before mid after}, fixtureAccumulator b before = some mid →
      fixtureAccumulator a mid = some after → fixtureAccumulator (b ++ a) before = some after := by
  intro a b before mid after hb ha
  unfold fixtureAccumulator at hb ha
  have hmid : mid = foldRetire b before := (Option.some.inj hb).symm
  have hafter : after = foldRetire a mid := (Option.some.inj ha).symm
  unfold fixtureAccumulator
  change some (foldRetire (b ++ a) before) = some after
  rw [hafter, hmid]
  unfold foldRetire
  rw [List.foldl_append]

theorem sem_identityAccumulator_law :
    ∀ state, fixtureAccumulator [] state = some state := by
  intro state
  unfold fixtureAccumulator
  rfl

theorem sem_accumulator_frame :
    ∀ {code before after}, fixtureAccumulator code before = some after →
      semAccumulatorFrame code before after := by
  intro code before after hacc
  unfold semAccumulatorFrame
  unfold fixtureAccumulator at hacc
  have hafter : after = foldRetire code before := (Option.some.inj hacc).symm
  rw [hafter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (foldRetire_ledger code before).symm
  · exact (foldRetire_history code before).symm
  · exact (foldRetire_coeffects code before).symm
  · intro name
    rcases foldRetire_lookup code before name with h | h
    · left
      exact h.symm
    · rcases h with ⟨hmem, cell, hl, hret, ha⟩
      right
      exact ⟨cell, hmem, hl, hret, ha⟩

theorem sem_accumulator_writesWithinProvision :
    ∀ {code before after}, fixtureAccumulator code before = some after →
      semWritesWithin ∅ before after := by
  intro code before after hacc
  change ∀ key, key ∉ (∅ : Finset Nat) → Coeffect.lookup key before.coeffects = Coeffect.lookup key after.coeffects
  intro key _hkey
  unfold fixtureAccumulator at hacc
  have hafter : after = foldRetire code before := (Option.some.inj hacc).symm
  rw [hafter]
  rw [foldRetire_coeffects code before]

theorem sem_accumulator_domainFrame :
    ∀ {code before after}, fixtureAccumulator code before = some after →
      semDomainFrame before after := by
  intro code before after hacc
  change before.registry.keys = after.registry.keys
  unfold fixtureAccumulator at hacc
  have hafter : after = foldRetire code before := (Option.some.inj hacc).symm
  rw [hafter]
  rw [foldRetire_keys code before]

theorem sem_accumulator_allocationFrame :
    ∀ {code before after}, fixtureAccumulator code before = some after →
      semAllocationFrame before after := by
  intro code before after hacc
  change before.ledger = after.ledger ∧ before.allocationHistory = after.allocationHistory
  unfold fixtureAccumulator at hacc
  have hafter : after = foldRetire code before := (Option.some.inj hacc).symm
  rw [hafter]
  rw [foldRetire_ledger code before, foldRetire_history code before]
  exact ⟨rfl, rfl⟩

theorem sem_accumulator_observes :
    ∀ {code before after}, fixtureAccumulator code before = some after →
      semObserves before after := by
  intro code before after hacc
  change before.coeffects = after.coeffects
  unfold fixtureAccumulator at hacc
  have hafter : after = foldRetire code before := (Option.some.inj hacc).symm
  rw [hafter]
  rw [foldRetire_coeffects code before]

/-- The concrete external semantics instantiation: every law is the hoisted
theorem above, so the same non-degenerate semantics discharges every axiom. -/
def rulesSem : Sem :=
  { action := fixtureAction
    stage := fixtureStage
    composeInverse := fun a b => b ++ a
    identityAccumulator := []
    accumulator := fixtureAccumulator
    launch := fun (_ : State) => some ()
    landing := fixtureLanding
    undo := fixtureUndo
    observes := semObserves
    writesWithinProvision := semWritesWithin
    continuationStable := semContinuationStable
    registryFrame := semRegistryFrame
    domainFrame := semDomainFrame
    allocationFrame := semAllocationFrame
    rank := fun (code : Nat) => code
    accumulatorFrame := semAccumulatorFrame
    stageEnvelope := fun (_ : Nat) => ∅
    landingEnvelope := fun (_ : Unit) => ∅
    accumulatorEnvelope := fun (_ : List Nat) => ∅
    actionEnvelope := fun (_ : Unit) => ∅
    action_writesWithinProvision := sem_action_writesWithinProvision
    action_frame := sem_action_frame
    inverse_law := sem_inverse_law
    stage_frame := sem_stage_frame
    stage_writesWithinProvision := sem_stage_writesWithinProvision
    stage_registryFrame := sem_stage_registryFrame
    stage_allocationFrame := sem_stage_allocationFrame
    relation_respect := sem_relation_respect
    rank_law := sem_rank_law
    landing_stable := sem_landing_stable
    landing_frame := sem_landing_frame
    landing_writesWithinProvision := sem_landing_writesWithinProvision
    landing_registryFrame := sem_landing_registryFrame
    landing_allocationFrame := sem_landing_allocationFrame
    composeInverse_law := sem_composeInverse_law
    identityAccumulator_law := sem_identityAccumulator_law
    accumulator_frame := sem_accumulator_frame
    accumulator_writesWithinProvision := sem_accumulator_writesWithinProvision
    accumulator_domainFrame := sem_accumulator_domainFrame
    accumulator_allocationFrame := sem_accumulator_allocationFrame
    accumulator_observes := sem_accumulator_observes }

/-- The body-frame adequacy instance: every abstract frame relation means its
concrete `GState` interpretation; the cleanup interpretation is conditional
on the step's foreign edits being recorded-child retirements of the acting
owner (the strengthened `CleanupFrame` branch). -/
theorem bodyFrameAdequacy : BodyFrameAdequacy rulesSem :=
  { registry_total := by
      intro before after h
      exact h
    allocation_noAllocation := by
      intro before after h
      exact ⟨h.1.symm, h.2.symm⟩
    provision_coeffectFrame := by
      intro before after provides h key hkey
      exact h key hkey
    observes_readRespect := by
      intro before after hobs owner key _hcell
      rw [hobs]
    accumulator_domain_total := by
      intro before after h
      exact h
    accumulator_cleanupFrame := by
      intro owner cell before after hlook hacc hchildren hframe
      unfold CleanupFrame
      rcases hframe with ⟨hled, hhist, hcoef, hforeign⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro name hne
        have hf := hforeign name
        rcases hf with hf | hf
        · left
          exact hf
        · rcases hf with ⟨cellN, _hmem, hl, hret, ha⟩
          right
          have hne' : Finmap.lookup name before.registry ≠ Finmap.lookup name after.registry := by
            intro heq
            have hcellN : cellN = { cellN with retired := true } :=
              Option.some.inj (hl.symm.trans (heq.trans ha))
            have hbad : cellN.retired = true := by
              rw [hcellN]
            simp [hret] at hbad
          refine ⟨cellN, hl, hret, hchildren name cellN hl hne hne', ha⟩
      · exact hled
      · exact hhist
      · exact hcoef }

abbrev model := globalControlModel rulesSem

/-! ### Main fixture: state chain -/

abbrev view101 : Finmap (fun _ : Nat => Nat) := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))

abbrev s1 : State := allocate s0 1 cell1
abbrev s2 : State := beginState rulesSem s1 1 ∅ ()
abbrev s3 : State := allocate s2 2 cell2
abbrev s4 : State := iterState rulesSem s3 1 [2] 0
abbrev s5 : State := finishState rulesSem s4 1 []
abbrev s6 : State := beginState rulesSem s5 2 view101 ()
abbrev s7 : State := iterState rulesSem s6 2 [] 2
abbrev s8 : State := allocate s7 3 cell3
abbrev s9 : State := beginState rulesSem s8 3 view101 ()
abbrev s10 : State := allocate s9 4 cell4
abbrev s11 : State := beginState rulesSem s10 4 view101 ()
abbrev s12 : State := finishState rulesSem s11 4 []
abbrev s13 : State := allocate s12 5 cell5
abbrev s14 : State := beginState rulesSem s13 5 view101 ()
abbrev s15 : State := raiseState s14 5 7
abbrev s16 : State := unloadState s15 5
abbrev s17 : State := retireState s16 1
abbrev s18 : State := leaveState s17 1
abbrev s19 : State := divertAbortState s18 3
abbrev s20 : State := unloadState s19 3
abbrev s21 : State := retireState s20 3
abbrev s22 : State := removeState s21 3
abbrev s23 : State := divertLandState rulesSem { s22 with ambient := s22.ambient + 1 } 2 []
abbrev s24 : State := leaveState s23 4
abbrev s25 : State := unloadState s24 4
abbrev s26 : State := unloadState s25 2
abbrev s27 : State := unloadState (foldRetire [2] s26) 1

/-! ### Per-state cell facts -/

abbrev cell1begun : Cell := { cell1 with phase := .reloading, committedView := ∅, payload := { cell1.payload with iteratorCode := 1, accumulatorCode := [], flightCode := some () } }
abbrev cell1itered : Cell := { cell1begun with payload := { cell1begun.payload with iteratorCode := 0, accumulatorCode := [2] } }
abbrev cell1active : Cell := { cell1itered with phase := .active, committed := { entries := commitProjection s4 ({10} : Finset Nat) }, payload := { cell1itered.payload with accumulatorCode := [2], flightCode := none, failureData := none } }
abbrev cell1retired : Cell := { cell1active with retired := true }
abbrev cell1unloading : Cell := { cell1retired with phase := .unloading }
abbrev cell1inactive : Cell := { cell1unloading with phase := .inactive, committedView := ∅, payload := { cell1unloading.payload with flightCode := none } }

abbrev cell2begun : Cell := { cell2 with phase := .reloading, committedView := view101, payload := { cell2.payload with iteratorCode := 3, accumulatorCode := [], flightCode := some () } }
abbrev cell2itered : Cell := { cell2begun with payload := { cell2begun.payload with iteratorCode := 2, accumulatorCode := [] } }
abbrev cell2unloading : Cell := { cell2itered with phase := .unloading, payload := { cell2itered.payload with accumulatorCode := [], flightCode := none } }
abbrev cell2inactive : Cell := { cell2unloading with phase := .inactive, committedView := ∅, payload := { cell2unloading.payload with flightCode := none } }
abbrev cell2retiredInactive : Cell := { cell2inactive with retired := true }

abbrev cell3begun : Cell := { cell3 with phase := .reloading, committedView := view101, payload := { cell3.payload with iteratorCode := 1, accumulatorCode := [], flightCode := some () } }
abbrev cell3unloading : Cell := { cell3begun with phase := .unloading }
abbrev cell3inactive : Cell := { cell3 with phase := .inactive, committedView := ∅, payload := { cell3.payload with flightCode := none } }
abbrev cell3retired : Cell := { cell3inactive with retired := true }

abbrev cell4begun : Cell := { cell4 with phase := .reloading, committedView := view101, payload := { cell4.payload with iteratorCode := 0, accumulatorCode := [], flightCode := some () } }
abbrev cell4active : Cell := { cell4begun with phase := .active, committed := { entries := commitProjection s11 (∅ : Finset Nat) }, payload := { cell4begun.payload with accumulatorCode := [], flightCode := none, failureData := none } }
abbrev cell4unloading : Cell := { cell4active with phase := .unloading }
abbrev cell4inactive : Cell := { cell4unloading with phase := .inactive, committedView := ∅, payload := { cell4unloading.payload with flightCode := none } }

abbrev cell5begun : Cell := { cell5 with phase := .reloading, committedView := view101, payload := { cell5.payload with iteratorCode := 99, accumulatorCode := [], flightCode := some () } }
abbrev cell5unloading : Cell := { cell5begun with phase := .unloading, payload := { cell5begun.payload with failureData := some 7 } }
abbrev cell5failed : Cell := { cell5unloading with phase := .failed, committedView := ∅, payload := { cell5unloading.payload with flightCode := none } }

theorem lookup_s1_1 : Finmap.lookup 1 s1.registry = some cell1 := by
  congr

theorem lookup_s2_1 : Finmap.lookup 1 s2.registry = some cell1begun := by
  congr

theorem lookup_s3_1 : Finmap.lookup 1 s3.registry = some cell1begun := by
  congr

theorem lookup_s4_1 : Finmap.lookup 1 s4.registry = some cell1itered := by
  congr

theorem lookup_s5_1 : Finmap.lookup 1 s5.registry = some cell1active := by
  congr

theorem lookup_s5_2 : Finmap.lookup 2 s5.registry = some cell2 := by
  congr

theorem lookup_s6_1 : Finmap.lookup 1 s6.registry = some cell1active := by
  congr

theorem lookup_s6_2 : Finmap.lookup 2 s6.registry = some cell2begun := by
  congr

theorem lookup_s7_2 : Finmap.lookup 2 s7.registry = some cell2itered := by
  congr

theorem lookup_s8_3 : Finmap.lookup 3 s8.registry = some cell3 := by
  congr

theorem lookup_s9_3 : Finmap.lookup 3 s9.registry = some cell3begun := by
  congr

theorem lookup_s10_4 : Finmap.lookup 4 s10.registry = some cell4 := by
  congr

theorem lookup_s11_4 : Finmap.lookup 4 s11.registry = some cell4begun := by
  congr

theorem lookup_s12_4 : Finmap.lookup 4 s12.registry = some cell4active := by
  congr

theorem lookup_s13_5 : Finmap.lookup 5 s13.registry = some cell5 := by
  congr

theorem lookup_s14_5 : Finmap.lookup 5 s14.registry = some cell5begun := by
  congr

theorem lookup_s15_5 : Finmap.lookup 5 s15.registry = some cell5unloading := by
  congr

theorem lookup_s16_5 : Finmap.lookup 5 s16.registry = some cell5failed := by
  congr

theorem lookup_s17_1 : Finmap.lookup 1 s17.registry = some cell1retired := by
  congr

theorem lookup_s18_1 : Finmap.lookup 1 s18.registry = some cell1unloading := by
  congr

theorem lookup_s18_3 : Finmap.lookup 3 s18.registry = some cell3begun := by
  congr

theorem lookup_s19_3 : Finmap.lookup 3 s19.registry = some cell3unloading := by
  congr

theorem lookup_s20_3 : Finmap.lookup 3 s20.registry = some cell3inactive := by
  congr

theorem lookup_s21_3 : Finmap.lookup 3 s21.registry = some cell3retired := by
  congr

theorem lookup_s22_2 : Finmap.lookup 2 s22.registry = some cell2itered := by
  congr

theorem lookup_s23_2 : Finmap.lookup 2 s23.registry = some cell2unloading := by
  congr

theorem lookup_s23_4 : Finmap.lookup 4 s23.registry = some cell4active := by
  congr

theorem lookup_s24_4 : Finmap.lookup 4 s24.registry = some cell4unloading := by
  congr

theorem lookup_s25_4 : Finmap.lookup 4 s25.registry = some cell4inactive := by
  congr

theorem lookup_s25_2 : Finmap.lookup 2 s25.registry = some cell2unloading := by
  congr

theorem lookup_s26_2 : Finmap.lookup 2 s26.registry = some cell2inactive := by
  congr

theorem lookup_s26_1 : Finmap.lookup 1 s26.registry = some cell1unloading := by
  congr

theorem lookup_s27_1 : Finmap.lookup 1 s27.registry = some cell1inactive := by
  congr

theorem lookup_s27_2 : Finmap.lookup 2 s27.registry = some cell2retiredInactive := by
  congr

/-! ### Provider and target views -/

theorem commitProjection_mem_keys_iff (state : State) (provides : Finset Nat) (key : Nat) :
    key ∈ (commitProjection state provides).keys ↔ key ∈ provides ∧ key ∈ state.coeffects.keys := by
  constructor
  · intro h
    exact ⟨commitProjection_keys_subset state provides h, by
      rw [Finmap.mem_keys] at h
      rw [Finmap.mem_def] at h
      change key ∈ Multiset.map Sigma.fst (Multiset.filter (fun entry => entry.1 ∈ provides) state.coeffects.entries) at h
      rw [Multiset.mem_map] at h
      rcases h with ⟨entry, hmem, hfst⟩
      rw [Multiset.mem_filter] at hmem
      rw [Finmap.mem_keys, Finmap.mem_def]
      change key ∈ Multiset.map Sigma.fst state.coeffects.entries
      rw [Multiset.mem_map]
      exact ⟨entry, hmem.1, hfst⟩⟩
  · intro h
    rw [Finmap.mem_keys, Finmap.mem_def]
    change key ∈ Multiset.map Sigma.fst (Multiset.filter (fun entry => entry.1 ∈ provides) state.coeffects.entries)
    rw [Multiset.mem_map]
    rcases h with ⟨hprov, hkeys⟩
    rw [Finmap.mem_keys, Finmap.mem_def] at hkeys
    change key ∈ Multiset.map Sigma.fst state.coeffects.entries at hkeys
    rw [Multiset.mem_map] at hkeys
    rcases hkeys with ⟨entry, hmem, hfst⟩
    exact ⟨entry, by rw [Multiset.mem_filter]; exact ⟨hmem, by rwa [hfst]⟩, hfst⟩

theorem providesNow_s5 : ProvidesNow s5 1 10 :=
  ⟨_, lookup_s5_1, by
    change 10 ∈ (commitProjection s4 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem providesNow_s6 : ProvidesNow s6 1 10 :=
  ⟨_, lookup_s6_1, by
    change 10 ∈ (commitProjection s6 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem targetViewAt_s5_2 : TargetViewAt s5 2 view101 := by
  refine ⟨_, lookup_s5_2, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s5
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s6_2 : TargetViewAt s6 2 view101 := by
  refine ⟨_, lookup_s6_2, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s5
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s8_3 : TargetViewAt s8 3 view101 := by
  refine ⟨_, lookup_s8_3, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s6
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s10_4 : TargetViewAt s10 4 view101 := by
  refine ⟨_, lookup_s10_4, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s6
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem targetViewAt_s13_5 : TargetViewAt s13 5 view101 := by
  refine ⟨_, lookup_s13_5, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s6
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv


theorem lookup_s11_1 : Finmap.lookup 1 s11.registry = some cell1active := by
  congr

theorem lookup_s18_2 : Finmap.lookup 2 s18.registry = some cell2itered := by
  congr

theorem lookup_s18_4 : Finmap.lookup 4 s18.registry = some cell4active := by
  congr

theorem lookup_s18_5 : Finmap.lookup 5 s18.registry = some cell5failed := by
  congr

theorem lookup_s21_1 : Finmap.lookup 1 s21.registry = some cell1unloading := by
  congr

theorem lookup_s21_2 : Finmap.lookup 2 s21.registry = some cell2itered := by
  congr

theorem lookup_s21_4 : Finmap.lookup 4 s21.registry = some cell4active := by
  congr

theorem lookup_s21_5 : Finmap.lookup 5 s21.registry = some cell5failed := by
  congr

theorem lookup_s23_1 : Finmap.lookup 1 s23.registry = some cell1unloading := by
  congr

theorem lookup_s15_1 : Finmap.lookup 1 s15.registry = some cell1active := by
  congr

theorem lookup_s15_2 : Finmap.lookup 2 s15.registry = some cell2itered := by
  congr

theorem lookup_s15_3 : Finmap.lookup 3 s15.registry = some cell3begun := by
  congr

theorem lookup_s15_4 : Finmap.lookup 4 s15.registry = some cell4active := by
  congr

theorem lookup_s19_5 : Finmap.lookup 5 s19.registry = some cell5failed := by
  congr

theorem lookup_s16_1 : Finmap.lookup 1 s16.registry = some cell1active := by
  congr

theorem lookup_s16_2 : Finmap.lookup 2 s16.registry = some cell2itered := by
  congr

theorem lookup_s16_3 : Finmap.lookup 3 s16.registry = some cell3begun := by
  congr

theorem lookup_s16_4 : Finmap.lookup 4 s16.registry = some cell4active := by
  congr

theorem lookup_s19_1 : Finmap.lookup 1 s19.registry = some cell1unloading := by
  congr

theorem lookup_s19_2 : Finmap.lookup 2 s19.registry = some cell2itered := by
  congr

theorem lookup_s19_4 : Finmap.lookup 4 s19.registry = some cell4active := by
  congr

theorem lookup_s22_1 : Finmap.lookup 1 s22.registry = some cell1unloading := by
  congr

theorem lookup_s22_4 : Finmap.lookup 4 s22.registry = some cell4active := by
  congr

theorem lookup_s24_1 : Finmap.lookup 1 s24.registry = some cell1unloading := by
  congr

theorem lookup_s24_2 : Finmap.lookup 2 s24.registry = some cell2unloading := by
  congr

theorem lookup_s24_5 : Finmap.lookup 5 s24.registry = some cell5failed := by
  congr

theorem lookup_s25_1 : Finmap.lookup 1 s25.registry = some cell1unloading := by
  congr

theorem lookup_s25_5 : Finmap.lookup 5 s25.registry = some cell5failed := by
  congr

theorem lookup_s26_4 : Finmap.lookup 4 s26.registry = some cell4inactive := by
  congr

theorem lookup_s26_5 : Finmap.lookup 5 s26.registry = some cell5failed := by
  congr

theorem providesNow_s11 : ProvidesNow s11 1 10 :=
  ⟨_, lookup_s11_1, by
    change 10 ∈ (commitProjection s11 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem targetViewAt_s11_4 : TargetViewAt s11 4 view101 := by
  refine ⟨_, lookup_s11_4, ?_, ?_, ?_⟩
  · rfl
  · change view101.keys = {10}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
    by_cases hkey : key = 10 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 10
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      exact providesNow_s11
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem noProvides10_s18 : ∀ p, ¬ ProvidesNow s18 p 10 := by
  intro p h
  rcases h with ⟨cell, hlook, htable, hphase⟩
  by_cases hp1 : p = 1
  · subst p
    rw [lookup_s18_1] at hlook
    cases hlook with | refl
    simp at hphase
  · by_cases hp2 : p = 2
    · subst p
      rw [lookup_s18_2] at hlook
      cases hlook with | refl
      change 10 ∈ cell2itered.committed.entries.keys at htable
      simp at htable
    · by_cases hp3 : p = 3
      · subst p
        rw [lookup_s18_3] at hlook
        cases hlook with | refl
        change 10 ∈ cell3begun.committed.entries.keys at htable
        simp at htable
      · by_cases hp4 : p = 4
        · subst p
          rw [lookup_s18_4] at hlook
          cases hlook with | refl
          change 10 ∈ (commitProjection s11 (∅ : Finset Nat)).keys at htable
          rw [commitProjection_mem_keys_iff] at htable
          simp at htable
        · by_cases hp5 : p = 5
          · subst p
            rw [lookup_s18_5] at hlook
            cases hlook with | refl
            simp at hphase
          · have hnone : Finmap.lookup p s18.registry = none := by
              simp [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
                leaveState, retireState, unloadState, raiseState, beginState, finishState, iterState,
                editCell, allocate, beginPayload, iterPayload, rulesSem,
                Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty,
                hp1, hp2, hp3, hp4, hp5]
            simp [hnone] at hlook

theorem targetAbsent_s18_3 : TargetAbsent s18 3 := by
  intro ω h
  rcases h with ⟨cell, hlook, _hret, hkeys, hall⟩
  rw [lookup_s18_3] at hlook
  cases hlook with | refl
  have hmem : 10 ∈ ω.keys := by
    rw [hkeys]
    change 10 ∈ cell3.component.requires
    rw [cell3]
    simp
  have hisome : (Finmap.lookup 10 ω).isSome := by
    rw [Finmap.lookup_isSome, ← Finmap.mem_keys]
    exact hmem
  cases hlook10 : Finmap.lookup 10 ω with
  | none => simp [hlook10] at hisome
  | some provider =>
      have hprov : ProvidesNow s18 provider 10 := hall 10 provider hlook10
      exact noProvides10_s18 provider hprov

theorem targetNot_s22_2 : ¬ TargetViewAt s22 2 view101 := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow s22 1 10 := hall 10 1 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_s22_1] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem targetNot_s23_4 : ¬ TargetViewAt s23 4 view101 := by
  intro h
  rcases h with ⟨cell, hlook, _hret, _hkeys, hall⟩
  have hprov : ProvidesNow s23 1 10 := hall 10 1 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_s23_1] at hlook'
  cases hlook' with | refl
  simp at hphase

/-- The pure control edit never touches a foreign cell. -/
theorem editCell_lookup_ne (state : State) (owner : Nat) (edit : Cell → Cell) {name : Nat}
    (h : name ≠ owner) :
    Finmap.lookup name (editCell state owner edit).registry = Finmap.lookup name state.registry := by
  unfold editCell
  cases hlook : Finmap.lookup owner state.registry with
  | none => rfl
  | some _ => exact Finmap.lookup_insert_of_ne (a := owner) (a' := name) (s := state.registry) h

/-- A name outside {1..5} is absent from the s22 registry (cell 3 was removed;
the whole chain reduces through the successor equations). -/
theorem lookup_s22_none_of_ne {name : Nat} (h1 : name ≠ 1) (h2 : name ≠ 2) (h3 : name ≠ 3)
    (h4 : name ≠ 4) (h5 : name ≠ 5) :
    Finmap.lookup name s22.registry = none := by
  change Finmap.lookup name (Finmap.erase 3 s21.registry) = none
  rw [Finmap.lookup_erase_ne h3]
  change Finmap.lookup name (editCell s20 3 (fun cell => { cell with retired := true })).registry = none
  rw [editCell_lookup_ne s20 3 _ h3]
  change Finmap.lookup name (editCell s19 3 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s19 3 _ h3]
  change Finmap.lookup name (editCell s18 3 (fun cell => { cell with phase := .unloading })).registry = none
  rw [editCell_lookup_ne s18 3 _ h3]
  change Finmap.lookup name (editCell s17 1 (fun cell => { cell with phase := .unloading })).registry = none
  rw [editCell_lookup_ne s17 1 _ h1]
  change Finmap.lookup name (editCell s16 1 (fun cell => { cell with retired := true })).registry = none
  rw [editCell_lookup_ne s16 1 _ h1]
  change Finmap.lookup name (editCell s15 5 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s15 5 _ h5]
  change Finmap.lookup name (editCell s14 5 (fun cell => { cell with phase := .unloading, payload := { cell.payload with failureData := some 7 } })).registry = none
  rw [editCell_lookup_ne s14 5 _ h5]
  change Finmap.lookup name (editCell s13 5 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s13 5 _ h5]
  change Finmap.lookup name (Finmap.insert 5 cell5 s12.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 5) (a' := name) (s := s12.registry) h5]
  change Finmap.lookup name (editCell s11 4 (fun cell => { cell with phase := .active, committed := { entries := commitProjection s11 cell.component.provides }, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none, failureData := none } })).registry = none
  rw [editCell_lookup_ne s11 4 _ h4]
  change Finmap.lookup name (editCell s10 4 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s10 4 _ h4]
  change Finmap.lookup name (Finmap.insert 4 cell4 s9.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 4) (a' := name) (s := s9.registry) h4]
  change Finmap.lookup name (editCell s8 3 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s8 3 _ h3]
  change Finmap.lookup name (Finmap.insert 3 cell3 s7.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 3) (a' := name) (s := s7.registry) h3]
  change Finmap.lookup name (editCell s6 2 (fun cell => { cell with payload := iterPayload rulesSem cell [] 2 })).registry = none
  rw [editCell_lookup_ne s6 2 _ h2]
  change Finmap.lookup name (editCell s5 2 (fun cell => { cell with phase := .reloading, committedView := view101, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s5 2 _ h2]
  change Finmap.lookup name (editCell s4 1 (fun cell => { cell with phase := .active, committed := { entries := commitProjection s4 cell.component.provides }, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none, failureData := none } })).registry = none
  rw [editCell_lookup_ne s4 1 _ h1]
  change Finmap.lookup name (editCell s3 1 (fun cell => { cell with payload := iterPayload rulesSem cell [2] 0 })).registry = none
  rw [editCell_lookup_ne s3 1 _ h1]
  change Finmap.lookup name (Finmap.insert 2 cell2 s2.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 2) (a' := name) (s := s2.registry) h2]
  change Finmap.lookup name (editCell s1 1 (fun cell => { cell with phase := .reloading, committedView := ∅, payload := beginPayload rulesSem cell () })).registry = none
  rw [editCell_lookup_ne s1 1 _ h1]
  change Finmap.lookup name (Finmap.insert 1 cell1 s0.registry) = none
  rw [Finmap.lookup_insert_of_ne (a := 1) (a' := name) (s := s0.registry) h1]
  change Finmap.lookup name (∅ : Finmap (fun _ : Nat => Cell)) = none
  rw [Finmap.lookup_empty]

/-! ### The main trace witnesses -/

/-- A name outside {1..5} is absent from the s24 registry (same chain as the
s22 lemma plus the leave/divertLand control edits). -/
theorem lookup_s24_none_of_ne {name : Nat} (h1 : name ≠ 1) (h2 : name ≠ 2) (h3 : name ≠ 3)
    (h4 : name ≠ 4) (h5 : name ≠ 5) :
    Finmap.lookup name s24.registry = none := by
  change Finmap.lookup name (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
  rw [editCell_lookup_ne s23 4 _ h4]
  change Finmap.lookup name (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none } })).registry = none
  rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ h2]
  change Finmap.lookup name { s22 with ambient := s22.ambient + 1 }.registry = none
  change Finmap.lookup name s22.registry = none
  exact lookup_s22_none_of_ne h1 h2 h3 h4 h5

/-- A name outside {1..5} is absent from the s26 registry (unload of 2, unload
of 4, then the s24 chain). -/
theorem lookup_s26_none_of_ne {name : Nat} (h1 : name ≠ 1) (h2 : name ≠ 2) (h3 : name ≠ 3)
    (h4 : name ≠ 4) (h5 : name ≠ 5) :
    Finmap.lookup name s26.registry = none := by
  change Finmap.lookup name (editCell s25 2 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s25 2 _ h2]
  change Finmap.lookup name (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
  rw [editCell_lookup_ne s24 4 _ h4]
  exact lookup_s24_none_of_ne h1 h2 h3 h4 h5

theorem step_insert1 : OrchestrationRule (.insert none 1 cell1) s0 s1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 1) (child := cell1)
    (by simp []) (by decide)
    (by simp [CanonicalInitialCell, nextBirth])
    (by intro name cell' h; simp at h)

theorem step_begin1 : LifecycleRule rulesSem (.begin 1 ∅) s1 s2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell1)
    (hlook := lookup_s1_1) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := ⟨cell1, lookup_s1_1, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

theorem step_insert2 : OrchestrationRule (.insert (some 1) 2 cell2) s2 s3 := by
  exact OrchestrationRule.insert (registrar := some 1) (fresh := 2) (child := cell2)
    (by simp [s2, s1, beginState, editCell, allocate, Finmap.lookup_insert])
    (by simp [s2, s1, beginState, editCell, allocate, ])
    (by
      simp [CanonicalInitialCell, Registered, s2, s1, nextBirth, beginState, editCell,
        allocate, beginPayload, rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        by_cases hname : name = 1
        · subst name
          rw [lookup_s2_1] at h
          cases h with | refl
          change key ∈ cell2.component.provides at hkey
          simp at hkey
          subst key
          simp []
        · simp [s2, s1, beginState, editCell, allocate, beginPayload, rulesSem,
            Finmap.lookup_insert, hname] at h)

theorem step_iter1 : LifecycleRule rulesSem (.iter 1 0) s3 s4 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cell1begun)
    (hlook := lookup_s3_1) (hphase := rfl)
    (htarget := ⟨cell1begun, lookup_s3_1, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 1 s3 = some (.yield s3 [2] 0)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

theorem step_finish1 : LifecycleRule rulesSem (.finish 1) s4 s5 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell1itered)
    (hlook := lookup_s4_1) (hphase := rfl)
    (htarget := ⟨cell1itered, lookup_s4_1, rfl, by
      change (∅ : Finmap (fun _ : Nat => Nat)).keys = (∅ : Finset Nat)
      simp, by
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := by
      change fixtureStage 0 s4 = some (.halt s4 [])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

theorem step_begin2 : LifecycleRule rulesSem (.begin 2 view101) s5 s6 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell2)
    (hlook := lookup_s5_2) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s5_2)
    (hlaunch := rfl)

theorem step_iter2 : LifecycleRule rulesSem (.iter 2 2) s6 s7 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cell2begun)
    (hlook := lookup_s6_2) (hphase := rfl)
    (htarget := targetViewAt_s6_2)
    (hstage := by
      change fixtureStage 3 s6 = some (.yield s6 [] 2)
      rfl)
    (hrank := by decide)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({20} : Finset Nat)
      simp)

theorem step_insert3 : OrchestrationRule (.insert none 3 cell3) s7 s8 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 3) (child := cell3)
    (by simp [s7, s6, s5, s4, s3, s2, s1, iterState, beginState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne])
    (by simp [s7, s6, s5, s4, s3, s2, s1, iterState, beginState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s7, s6, s5, s4, s3, s2, s1, nextBirth, iterState, beginState,
        finishState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin3 : LifecycleRule rulesSem (.begin 3 view101) s8 s9 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell3)
    (hlook := lookup_s8_3) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s8_3)
    (hlaunch := rfl)

theorem step_insert4 : OrchestrationRule (.insert none 4 cell4) s9 s10 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 4) (child := cell4)
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, beginState, iterState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert,
        Finmap.lookup_insert_of_ne])
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, beginState, iterState, finishState, editCell,
        allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s9, s8, s7, s6, s5, s4, s3, s2, s1, nextBirth, beginState,
        iterState, finishState, editCell, allocate, beginPayload, iterPayload, rulesSem,
        Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin4 : LifecycleRule rulesSem (.begin 4 view101) s10 s11 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell4)
    (hlook := lookup_s10_4) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s10_4)
    (hlaunch := rfl)

theorem step_finish4 : LifecycleRule rulesSem (.finish 4) s11 s12 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cell4begun)
    (hlook := lookup_s11_4) (hphase := rfl)
    (htarget := targetViewAt_s11_4)
    (hstage := by
      change fixtureStage 0 s11 = some (.halt s11 [])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_insert5 : OrchestrationRule (.insert none 5 cell5) s12 s13 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 5) (child := cell5)
    (by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, finishState, beginState, iterState,
        editCell, allocate, beginPayload, iterPayload, rulesSem, Finmap.lookup_insert,
        Finmap.lookup_insert_of_ne])
    (by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, finishState, beginState, iterState,
        editCell, allocate, beginPayload, iterPayload, rulesSem, ])
    (by
      simp [CanonicalInitialCell, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, nextBirth,
        finishState, beginState, iterState, editCell, allocate, beginPayload, iterPayload,
        rulesSem, Finmap.lookup_insert])
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem step_begin5 : LifecycleRule rulesSem (.begin 5 view101) s13 s14 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cell5)
    (hlook := lookup_s13_5) (hphase := rfl) (hretired := rfl) (hnoFailure := rfl) (hnoFlight := rfl)
    (htarget := targetViewAt_s13_5)
    (hlaunch := rfl)

abbrev failureEvidence5 : FailureEvidence State Nat (List Nat) :=
  { error := 7, boundary := s14, prefixUndo := [] }

theorem step_raise5 : LifecycleRule rulesSem (.raise 5 failureEvidence5) s14 s15 := by
  exact LifecycleRule.raise (sem := rulesSem) (cell := cell5begun)
    (hlook := lookup_s14_5) (hphase := rfl)
    (hstage := by
      change fixtureStage 99 s14 = some (.raise 7)
      rfl)
    (hbridge := by unfold FailureFromStage; rfl)

theorem step_unload5 : LifecycleRule rulesSem (.unload 5) s15 s16 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell5unloading)
    (hlook := lookup_s15_5) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s15_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s15_2] at hlook
          cases hlook with | refl
          by_cases hk : key = 10
          · subst key
            rw [Finmap.lookup_insert] at hkv
            have h15 : (1 : Nat) = 5 := Option.some.inj hkv
            omega
          · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
            cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            rw [lookup_s15_3] at hlook
            cases hlook with | refl
            by_cases hk : key = 10
            · subst key
              rw [Finmap.lookup_insert] at hkv
              have h15 : (1 : Nat) = 5 := Option.some.inj hkv
              omega
            · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
              cases hkv
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s15_4] at hlook
              cases hlook with | refl
              by_cases hk : key = 10
              · subst key
                rw [Finmap.lookup_insert] at hkv
                have h15 : (1 : Nat) = 5 := Option.some.inj hkv
                omega
              · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
                cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                exact (hne rfl).elim
              · have hnone : Finmap.lookup dependent s15.registry = none := by
                  simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
                    raiseState, beginState, finishState, iterState, editCell, allocate,
                    beginPayload, iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
                    Finmap.lookup_empty, hd1, hd2, hd3, hd4, hd5]
                rw [hnone] at hlook
                cases hlook)
    (haccumulator := by
      change fixtureAccumulator [] s15 = some s15
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_retire1 : OrchestrationRule (.retire 1) s16 s17 := by
  exact OrchestrationRule.retire lookup_s16_1

theorem step_leave1 : LifecycleRule rulesSem (.leave 1) s17 s18 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cell1retired)
    (hlook := lookup_s17_1) (hphase := rfl)
    (hchanged := by
      intro h
      rcases h with ⟨cell, hlook, hret, _hkeys, _hall⟩
      rw [lookup_s17_1] at hlook
      cases hlook with | refl
      cases hret)

theorem step_divertAbort3 : LifecycleRule rulesSem (.divertAbort 3 .absent) s18 s19 := by
  exact LifecycleRule.divertAbort (sem := rulesSem) (cell := cell3begun)
    (hlook := lookup_s18_3) (hphase := rfl) (hboundary := targetAbsent_s18_3)

theorem step_unload3 : LifecycleRule rulesSem (.unload 3) s19 s20 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell3unloading)
    (hlook := lookup_s19_3) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s19_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s19_2] at hlook
          cases hlook with | refl
          by_cases hk : key = 10
          · subst key
            rw [Finmap.lookup_insert] at hkv
            have h13 : (1 : Nat) = 3 := Option.some.inj hkv
            omega
          · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
            cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            exact (hne rfl).elim
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s19_4] at hlook
              cases hlook with | refl
              by_cases hk : key = 10
              · subst key
                rw [Finmap.lookup_insert] at hkv
                have h13 : (1 : Nat) = 3 := Option.some.inj hkv
                omega
              · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
                cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s19_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s19.registry = none := by
                  simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3,
                    s2, s1, divertAbortState, leaveState, retireState, unloadState, raiseState,
                    beginState, finishState, iterState, editCell, allocate, beginPayload,
                    iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
                    Finmap.lookup_empty, hd1, hd2, hd3, hd4, hd5]
                rw [hnone] at hlook
                cases hlook)
    (haccumulator := by
      change fixtureAccumulator [] s19 = some s19
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_retire3 : OrchestrationRule (.retire 3) s20 s21 := by
  exact OrchestrationRule.retire lookup_s20_3

theorem step_remove3 : OrchestrationRule (.remove 3) s21 s22 := by
  exact OrchestrationRule.remove (cell := cell3retired) (hlook := lookup_s21_3)
    (hretired := rfl) (hphase := by left; rfl) (hnoChild := by
      intro name cell' h hparent
      by_cases hn1 : name = 1
      · subst name
        rw [lookup_s21_1] at h
        cases h with | refl
        cases hparent
      · by_cases hn2 : name = 2
        · subst name
          rw [lookup_s21_2] at h
          cases h with | refl
          cases hparent
        · by_cases hn3 : name = 3
          · subst name
            rw [lookup_s21_3] at h
            cases h with | refl
            simp at hparent
          · by_cases hn4 : name = 4
            · subst name
              rw [lookup_s21_4] at h
              cases h with | refl
              cases hparent
            · by_cases hn5 : name = 5
              · subst name
                rw [lookup_s21_5] at h
                cases h with | refl
                cases hparent
              · have hnone : Finmap.lookup name s21.registry = none := by
                  simp [s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5,
                    s4, s3, s2, s1, retireState, unloadState, divertAbortState, leaveState, raiseState,
                    beginState, finishState, iterState, editCell, allocate, beginPayload,
                    iterPayload, rulesSem, Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
                    Finmap.lookup_empty, hn1, hn2, hn3, hn4, hn5]
                rw [hnone] at h
                cases h)

theorem step_divertLand2 : LifecycleRule rulesSem (.divertLand 2 ()) s22 s23 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cell2itered)
    (hlook := lookup_s22_2) (hphase := rfl) (htoken := rfl)
    (hchanged := targetNot_s22_2)
    (hland := by
      change fixtureLanding () s22 = some (.landed { s22 with ambient := s22.ambient + 1 } [])
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({20} : Finset Nat)
      simp)

theorem step_leave4 : LifecycleRule rulesSem (.leave 4) s23 s24 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cell4active)
    (hlook := lookup_s23_4) (hphase := rfl)
    (hchanged := targetNot_s23_4)

theorem step_unload4 : LifecycleRule rulesSem (.unload 4) s24 s25 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell4unloading)
    (hlook := lookup_s24_4) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s24_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s24_2] at hlook
          cases hlook with | refl
          by_cases hk : key = 10
          · subst key
            rw [Finmap.lookup_insert] at hkv
            have h14 : (1 : Nat) = 4 := Option.some.inj hkv
            omega
          · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
            cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s24.registry = none := by
              unfold s24 s23 s22
              unfold leaveState
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 s22.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hlook
          · by_cases hd4 : dependent = 4
            · subst dependent
              exact (hne rfl).elim
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s24_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s24.registry = none := by
                  change Finmap.lookup dependent (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
                  rw [editCell_lookup_ne s23 4 _ (by intro h; exact hd4 h)]
                  change Finmap.lookup dependent (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none } })).registry = none
                  rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by intro h; exact hd2 h)]
                  change Finmap.lookup dependent { s22 with ambient := s22.ambient + 1 }.registry = none
                  change Finmap.lookup dependent s22.registry = none
                  exact lookup_s22_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hlook)
    (haccumulator := by
      change fixtureAccumulator [] s24 = some s24
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ (∅ : Finset Nat)
      simp)

theorem step_unload2 : LifecycleRule rulesSem (.unload 2) s25 s26 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell2unloading)
    (hlook := lookup_s25_2) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        rw [lookup_s25_1] at hlook
        cases hlook with | refl
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · by_cases hd2 : dependent = 2
        · subst dependent
          exact (hne rfl).elim
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s25.registry = none := by
              change Finmap.lookup 3 (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s24 4 _ (by decide)]
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hlook
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s25_4] at hlook
              cases hlook with | refl
              rw [Finmap.lookup_empty] at hkv
              cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s25_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s25.registry = none := by
                  change Finmap.lookup dependent (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome = true then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
                  rw [editCell_lookup_ne s24 4 _ (by intro h; exact hd4 h)]
                  exact lookup_s24_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hlook)
    (haccumulator := by
      change fixtureAccumulator [] s25 = some s25
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({20} : Finset Nat)
      simp)

theorem step_unload1 : LifecycleRule rulesSem (.unload 1) s26 s27 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cell1unloading)
    (hlook := lookup_s26_1) (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s26_2] at hlook
          cases hlook with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s26.registry = none := by
              change Finmap.lookup 3 (editCell s25 2 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s25 2 _ (by decide)]
              change Finmap.lookup 3 (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s24 4 _ (by decide)]
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hlook
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s26_4] at hlook
              cases hlook with | refl
              rw [Finmap.lookup_empty] at hkv
              cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s26_5] at hlook
                cases hlook with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s26.registry = none :=
                  lookup_s26_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hlook)
    (haccumulator := by
      change fixtureAccumulator [2] s26 = some (foldRetire [2] s26)
      rfl)
    (henvelope := by
      change (∅ : Finset Nat) ⊆ ({10} : Finset Nat)
      simp)

/-! ### Full-step D48 discharges -/

theorem iter1_writeFrame : WriteFrame s3 1 s4 :=
  iter_full_writeFrame rulesSem bodyFrameAdequacy lookup_s3_1
    (by change fixtureStage 1 s3 = some (.yield s3 [2] 0); rfl)
    (by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)
    rfl

theorem iter1_readNoninterference : ReadNoninterference s3 1 s4 :=
  iter_full_readNoninterference rulesSem bodyFrameAdequacy lookup_s3_1
    (by change fixtureStage 1 s3 = some (.yield s3 [2] 0); rfl)
    rfl

theorem finish1_writeFrame : WriteFrame s4 1 s5 :=
  finish_full_writeFrame rulesSem bodyFrameAdequacy lookup_s4_1
    (by change fixtureStage 0 s4 = some (.halt s4 []); rfl)
    (by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)
    rfl

theorem finish1_readNoninterference : ReadNoninterference s4 1 s5 :=
  finish_full_readNoninterference rulesSem bodyFrameAdequacy lookup_s4_1
    (by change fixtureStage 0 s4 = some (.halt s4 []); rfl)
    rfl

theorem lookup_s4_2 : Finmap.lookup 2 s4.registry = some cell2 := by
  congr

theorem finish1_tableConfined : TableConfined s5 :=
  finish_tableConfined rulesSem s4 1 [] (by
    intro name cell hl
    have hmem : name ∈ s4.registry.keys := by
      rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
      rfl
    simp [s4, s3, s2, s1, iterState, beginState, editCell, allocate, beginPayload,
      iterPayload, rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
    rcases hmem with h1 | h2 | htail
    · subst name
      rw [lookup_s4_1] at hl
      cases hl with | refl
      intro key hkey
      change key ∈ cell1itered.committed.entries.keys at hkey
      rw [cell1itered, cell1begun, cell1] at hkey
      simp at hkey
    · subst name
      rw [lookup_s4_2] at hl
      cases hl with | refl
      intro key hkey
      change key ∈ cell2.committed.entries.keys at hkey
      rw [cell2] at hkey
      simp at hkey
    · rcases htail with h1' | hempty
      · subst name
        rw [lookup_s4_1] at hl
        cases hl with | refl
        intro key hkey
        change key ∈ cell1itered.committed.entries.keys at hkey
        rw [cell1itered, cell1begun, cell1] at hkey
        simp at hkey
      · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
        simp at hempty)

theorem divertLand2_writeFrame : WriteFrame s22 2 s23 :=
  divertLand_full_writeFrame (landing := ()) rulesSem bodyFrameAdequacy lookup_s22_2
    (by change fixtureLanding () s22 = some (.landed { s22 with ambient := s22.ambient + 1 } []); rfl)
    (by change (∅ : Finset Nat) ⊆ ({20} : Finset Nat); simp)
    rfl

theorem divertLand2_readNoninterference : ReadNoninterference s22 2 s23 :=
  divertLand_full_readNoninterference (landing := ()) rulesSem bodyFrameAdequacy lookup_s22_2
    (by change fixtureLanding () s22 = some (.landed { s22 with ambient := s22.ambient + 1 } []); rfl)
    rfl

/-- Every foreign edit of the unload1 body is a recorded-child retirement of
owner 1 (the only changed cell is 2, retired from inactive). -/
theorem unload1_hchildren : ∀ n cellN, Finmap.lookup n s26.registry = some cellN → n ≠ 1 →
    Finmap.lookup n s26.registry ≠ Finmap.lookup n s27.registry →
      cellN.parent = some 1 := by
  intro n cellN hl hn hne
  have hbody : Finmap.lookup n s26.registry ≠ Finmap.lookup n (foldRetire [2] s26).registry := by
    intro h'
    exact hne (by
      rw [h']
      change Finmap.lookup n (foldRetire [2] s26).registry = Finmap.lookup n (unloadState (foldRetire [2] s26) 1).registry
      exact (editCell_lookup_ne (foldRetire [2] s26) 1 _ hn).symm)
  rcases foldRetire_lookup [2] s26 n with h | h
  · exfalso
    exact hbody h.symm
  · rcases h with ⟨hmem, cell, hl', hret, ha⟩
    rw [List.mem_singleton] at hmem
    subst n
    rw [hl'] at hl
    have hcellN : cellN = cell := (Option.some.inj hl).symm
    rw [hcellN]
    rw [lookup_s26_2] at hl'
    have hcell2 : cell = cell2inactive := (Option.some.inj hl').symm
    rw [hcell2]

theorem unload1_cleanupFrame : CleanupFrame s26 1 s27 :=
  unload_full_cleanupFrame rulesSem bodyFrameAdequacy lookup_s26_1 unload1_hchildren
    (by change fixtureAccumulator [2] s26 = some (foldRetire [2] s26); rfl)
    rfl

theorem unload1_readNoninterference : ReadNoninterference s26 1 s27 :=
  unload_full_readNoninterference rulesSem bodyFrameAdequacy lookup_s26_1
    (by change fixtureAccumulator [2] s26 = some (foldRetire [2] s26); rfl)
    rfl

theorem unload1_noAllocation :
    s27.registry.keys = s26.registry.keys ∧ s27.ledger = s26.ledger ∧
      s27.allocationHistory = s26.allocationHistory :=
  unload_noAllocation rulesSem bodyFrameAdequacy lookup_s26_1 rfl
    (by
      intro h
      rcases h with ⟨dependent, hne, _hinst, cell, key, hl, _hkey, hkv⟩
      by_cases hd1 : dependent = 1
      · subst dependent
        exact (hne rfl).elim
      · by_cases hd2 : dependent = 2
        · subst dependent
          rw [lookup_s26_2] at hl
          cases hl with | refl
          rw [Finmap.lookup_empty] at hkv
          cases hkv
        · by_cases hd3 : dependent = 3
          · subst dependent
            have hnone : Finmap.lookup 3 s26.registry = none := by
              change Finmap.lookup 3 (editCell s25 2 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s25 2 _ (by decide)]
              change Finmap.lookup 3 (editCell s24 4 (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })).registry = none
              rw [editCell_lookup_ne s24 4 _ (by decide)]
              change Finmap.lookup 3 (editCell s23 4 (fun cell => { cell with phase := .unloading })).registry = none
              rw [editCell_lookup_ne s23 4 _ (by decide)]
              change Finmap.lookup 3 (editCell { s22 with ambient := s22.ambient + 1 } 2 (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := rulesSem.composeInverse cell.payload.accumulatorCode [], flightCode := none } })).registry = none
              rw [editCell_lookup_ne { s22 with ambient := s22.ambient + 1 } 2 _ (by decide)]
              change Finmap.lookup 3 { s22 with ambient := s22.ambient + 1 }.registry = none
              change Finmap.lookup 3 (Finmap.erase 3 s21.registry) = none
              rw [Finmap.lookup_erase]
            simp [hnone] at hl
          · by_cases hd4 : dependent = 4
            · subst dependent
              rw [lookup_s26_4] at hl
              cases hl with | refl
              rw [Finmap.lookup_empty] at hkv
              cases hkv
            · by_cases hd5 : dependent = 5
              · subst dependent
                rw [lookup_s26_5] at hl
                cases hl with | refl
                rw [Finmap.lookup_empty] at hkv
                cases hkv
              · have hnone : Finmap.lookup dependent s26.registry = none :=
                  lookup_s26_none_of_ne (by intro h; exact hd1 h) (by intro h; exact hd2 h)
                    (by intro h; exact hd3 h) (by intro h; exact hd4 h) (by intro h; exact hd5 h)
                simp [hnone] at hl)
    (by change fixtureAccumulator [2] s26 = some (foldRetire [2] s26); rfl)
    (by change (∅ : Finset Nat) ⊆ ({10} : Finset Nat); simp)

/-! ### The nested-registration witness -/

def registrationWitness : NestedRegistrationWitness rulesSem :=
  { actionCode := ()
    parent := 1
    fresh := 2
    child := cell2
    parentBefore := s2
    parentAfter := s3
    result := { state := s3, inverse? := some [2] }
    inverse := [2]
    parentCell := cell1begun
    parent_lookup := lookup_s2_1
    action_run := by
      change fixtureAction () s2 = some { state := s3, inverse? := some [2] }
      unfold fixtureAction
      rw [show Finmap.lookup 2 s2.registry = none from by
        change Finmap.lookup 2 (editCell s1 1 (fun cell => { cell with phase := .reloading, committedView := ∅, payload := beginPayload rulesSem cell () })).registry = none
        rw [editCell_lookup_ne s1 1 _ (by decide)]
        change Finmap.lookup 2 (Finmap.insert 1 cell1 s0.registry) = none
        rw [Finmap.lookup_insert_of_ne (a := 1) (a' := 2) (s := s0.registry) (by decide)]
        change Finmap.lookup 2 (∅ : Finmap (fun _ : Nat => Cell)) = none
        rw [Finmap.lookup_empty]]
      simp [s2, s1, beginState, editCell, allocate, beginPayload, rulesSem,
        ]
    insert_step := step_insert2
    endpoint_link := rfl
    returns_inverse := rfl
    retire_adequate := by
      intro state cell hl
      change some (List.foldl (fun s n => (retire? s n).getD s) state [2]) = some (editCell state 2 (fun cell => { cell with retired := true }))
      rw [show List.foldl (fun s n => (retire? s n).getD s) state [2] = (retire? state 2).getD state from rfl]
      unfold retire?
      rw [hl]
      change some (updateFiber state 2 { cell with retired := true }) = some (editCell state 2 (fun cell => { cell with retired := true }))
      congr 1
      unfold editCell
      rw [hl]
      rfl }

theorem registrationWitness_folds :
    ∃ cell, Finmap.lookup 1 (foldInverseState rulesSem s3 1 [2]).registry = some cell ∧
      cell.payload.accumulatorCode = rulesSem.composeInverse cell1begun.payload.accumulatorCode [2] :=
  nestedRegistration_foldInverse rulesSem registrationWitness

/-! ### The §3.1 negatives -/

theorem retiredOwner_noTarget : ¬ TargetViewAt s17 1 ∅ := by
  intro h
  rcases h with ⟨cell, hl, hret, _hkeys, _hall⟩
  rw [lookup_s17_1] at hl
  cases hl with | refl
  cases hret

theorem retiredActive_provides : ProvidesNow s17 1 10 :=
  ⟨_, lookup_s17_1, by
    change 10 ∈ (commitProjection s17 ({10} : Finset Nat)).keys
    rw [commitProjection_mem_keys_iff]
    refine ⟨by simp, ?_⟩
    change 10 ∈ coeffects0.keys
    rw [coeffects0, Finmap.mem_keys, Finmap.mem_insert]
    simp, rfl⟩

theorem inactiveNonretired_notQuiescent : ¬ Quiescent s8 := by
  intro h
  have hq := h 3 cell3 (by congr)
  rcases hq with ⟨_h1, _h2, _h3, _h4, h5⟩
  have hbad := h5 rfl
  rcases hbad with hret | habsent
  · cases hret
  · exact habsent view101 targetViewAt_s8_3

theorem reloading_not_stagingStable : ¬ StagingStable s2 := by
  intro h
  have hf := h 1 cell1begun lookup_s2_1
  rcases hf with ha | ha
  · cases ha
  · rcases ha with hi | hf'
    · cases hi
    · cases hf'

/-! ### The R.base macro witnesses -/

abbrev cell4t : Cell := { cell4 with birth := 2 }
abbrev cell4u : Cell := { cell4 with component := { cell4.component with requires := ∅ }, birth := 2 }

abbrev t0 : State := allocate s5 4 cell4t
abbrev t1 : State := beginState rulesSem t0 4 view101 ()
abbrev t2 : State := finishState rulesSem t1 4 []

abbrev u0 : State := allocate s5 4 cell4u
abbrev u1 : State := beginState rulesSem u0 4 ∅ ()
abbrev u2 : State := finishState rulesSem u1 4 []
abbrev u3 : State := retireState u2 4
abbrev u4 : State := leaveState u3 4
abbrev u5 : State := unloadState u4 4

theorem stagingStable_t0 : StagingStable t0 := by
  intro name fiber hl
  have hmem : name ∈ t0.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
    rfl
  simp [t0, s5, s4, s3, s2, s1, finishState, iterState, beginState, editCell,
    allocate, beginPayload, iterPayload, rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
  rcases hmem with h4 | h1 | h2 | htail
  · subst name
    rw [show Finmap.lookup 4 t0.registry = some cell4t from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · subst name
    rw [show Finmap.lookup 1 t0.registry = some cell1active from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 2 t0.registry = some cell2 from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · rcases htail with h | hempty
    · subst name
      rw [show Finmap.lookup 1 t0.registry = some cell1active from by congr] at hl
      cases hl with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

theorem stagingStable_t2 : StagingStable t2 := by
  intro name fiber hl
  have hmem : name ∈ t2.registry.keys := by
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hl]
    rfl
  simp [t2, t1, t0, s5, s4, s3, s2, s1, finishState, beginState, iterState, editCell,
    allocate, beginPayload, iterPayload, rulesSem, Finmap.mem_keys, Finmap.mem_insert] at hmem
  rcases hmem with h4 | h1 | h2 | htail
  · subst name
    rw [show Finmap.lookup 4 t2.registry = some { cell4t with phase := .active, committed := { entries := commitProjection t1 (∅ : Finset Nat) }, committedView := view101, payload := { cell4t.payload with iteratorCode := 0, accumulatorCode := [], flightCode := none, failureData := none } } from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 1 t2.registry = some cell1active from by congr] at hl
    cases hl with | refl
    left; rfl
  · subst name
    rw [show Finmap.lookup 2 t2.registry = some cell2 from by congr] at hl
    cases hl with | refl
    right; left; rfl
  · rcases htail with h | hempty
    · subst name
      rw [show Finmap.lookup 1 t2.registry = some cell1active from by congr] at hl
      cases hl with | refl
      left; rfl
    · rw [← Finmap.lookup_isSome, Finmap.lookup_empty] at hempty
      simp at hempty

/-
/-! ### A.async: admissible divert evidence -/

def rulesPolicy : AsyncPolicy Unit State :=
  { atBoundary := fun (_ : Unit) (state : State) => providersOf state 10 = ∅
    landingWitness := fun (_ : Unit) (_ : State) => True
    allowed := fun (_ : Unit) (state : State) (choice : LandingChoice) =>
      match choice with
      | .land => True
      | .abort => providersOf state 10 = ∅
    mustLand := by intro flight state; trivial
    landSound := by intro flight state h; trivial
    abortGuard := by intro flight state h; exact h }

theorem divertAbort_admissible : divertAdmissible rulesSem rulesPolicy
    (.inr (.divertAbort 3 .absent)) s15 := by
  change ∃ cell flight, Finmap.lookup 3 s15.registry = some cell ∧
    cell.payload.flightCode = some flight ∧ cell.phase = .reloading ∧
      rulesPolicy.allowed flight s15 .abort
  refine ⟨cell3reloading, (), lookup_s15_3, rfl, rfl, ?_⟩
  change providersOf s15 10 = ∅
  decide

theorem divertLand_admissible : divertAdmissible rulesSem rulesPolicy
    (.inr (.divertLand 2 () 1 s19)) s19 := by
  change ∃ cell, Finmap.lookup 2 s19.registry = some cell ∧
    cell.payload.flightCode = some () ∧ cell.phase = .reloading ∧
      rulesPolicy.allowed () s19 .land
  refine ⟨cell2retired, lookup_s19_2, rfl, rfl, ?_⟩
  trivial

/-! ### ADR-09 cycle trace candidate (r = 0, c = 1, n = 2, former provider p = 3) -/

abbrev rc0 : State :=
  { ambient := 10, registry := ∅, coeffects := coeffects0,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

abbrev cellP : Cell :=
  { incarnation := 3, parent := none, birth := 0,
    component := { key := 3, requires := ∅, provides := {20}, actionCode := (), iteratorCode := 0, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cellR : Cell :=
  { incarnation := 0, parent := none, birth := 1,
    component := { key := 0, requires := {20}, provides := {10}, actionCode := (), iteratorCode := 0, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cellC : Cell :=
  { incarnation := 1, parent := some 0, birth := 2,
    component := { key := 1, requires := {20}, provides := ∅, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev cellN : Cell :=
  { incarnation := 2, parent := some 1, birth := 3,
    component := { key := 2, requires := {10}, provides := {20}, actionCode := (), iteratorCode := 1, accumulatorCode := 0, flightCode := (), failureCode := () },
    committed := { entries := Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload := { iteratorCode := 1, accumulatorCode := 0, flightCode := none, failureData := none } }

abbrev view20p : Finmap (fun _ : Nat => Nat) := Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))

abbrev c1 : State := allocate rc0 3 cellP
abbrev c2 : State := beginState rulesSem c1 3 ∅ ()
abbrev c3 : State := finishState { c2 with ambient := 9 } 3
abbrev c4 : State := allocate c3 0 cellR
abbrev c5 : State := beginState rulesSem c4 0 view20p ()
abbrev c6 : State := finishState { c5 with ambient := 8 } 0
abbrev c7 : State := allocate c6 1 cellC
abbrev c8 : State := beginState rulesSem c7 1 view20p ()
abbrev c9 : State := iterState rulesSem { c8 with ambient := 7 } 1 1 0
abbrev c10 : State := retireState c9 1
abbrev c11 : State := retireState c10 3
abbrev c12 : State := raiseState c11 3 ()
abbrev c13 : State := divertLandState rulesSem c12 1 1
abbrev c14 : State := unloadState { c13 with ambient := c13.ambient + 2 } 1
abbrev c15 : State := leaveState c14 0
abbrev c16 : State := unloadState c15 0
abbrev c17 : State := unloadState c16 3
abbrev c18 : State := removeState c17 3
abbrev c19 : State := allocate c18 2 cellN

theorem cycleStep_insertP : OrchestrationRule (.insert none 3 cellP) rc0 c1 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 3) (child := cellP)
    (by decide) (by decide)
    (by simp [CanonicalInitialCell, nextBirth])
    (by intro name cell' h; simp at h)

theorem cycleStep_beginP : LifecycleRule rulesSem (.begin 3 ∅ ()) c1 c2 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellP)
    (hlook := by simp [c1, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl)
    (htarget := ⟨cellP, by simp [c1, allocate, Finmap.lookup_insert], rfl, by
      intro key provider hkv
      change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hlaunch := rfl)

abbrev cellPbegun : Cell := { cellP with phase := .reloading, committedView := ∅, payload := { cellP.payload with iteratorCode := 0, accumulatorCode := 0, flightCode := some () } }
abbrev cellPactive : Cell := { cellPbegun with phase := .active }

theorem cycleStep_finishP : LifecycleRule rulesSem (.finish 3 { c2 with ambient := 9 }) c2 c3 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellPbegun) (hlook := by congr)
    (hphase := rfl)
    (htarget := ⟨cellPbegun, by congr, rfl, by
      intro key provider hkv
      change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩)
    (hstage := rfl)

theorem provides20_c3 : ProvidesNow c3 3 20 := by
  refine ⟨cellPactive, by congr, ?_, rfl⟩
  change 20 ∈ (Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys
  rw [Finmap.mem_keys, Finmap.mem_insert]
  simp

theorem cycleStep_insertR : OrchestrationRule (.insert none 0 cellR) c3 c4 := by
  exact OrchestrationRule.insert (registrar := none) (fresh := 0) (child := cellR)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, c3, c2, c1, finishState, beginState, editCell,
        updateFiber, allocate, beginPayload, rulesSem, cellP, Finmap.lookup_insert]
      decide)
    (by intro name cell' h
        by_cases hname : name = 3
        · subst name
          simp [c3, c2, c1, finishState, beginState, editCell, updateFiber, allocate,
            beginPayload, rulesSem, cellP, Finmap.lookup_insert] at h
          have hcell' : cell' = cellPactive := h.symm
          subst cell'
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
          subst key
          simp
        · simp [c3, c2, c1, finishState, beginState, editCell, updateFiber, allocate,
            beginPayload, rulesSem, cellP, Finmap.lookup_insert, hname] at h)

theorem cycleTargetViewAt_c4_0 : TargetViewAt c4 0 view20p := by
  refine ⟨cellR, by simp [c4, c3, allocate, Finmap.lookup_insert], ?_, ?_⟩
  · change view20p.keys = {20}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
    by_cases hkey : key = 20 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 20
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 3 := (Option.some.inj hkv).symm
      subst provider
      exact provides20_c3
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

theorem cycleStep_beginR : LifecycleRule rulesSem (.begin 0 view20p ()) c4 c5 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellR)
    (hlook := by simp [c4, c3, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl) (htarget := cycleTargetViewAt_c4_0) (hlaunch := rfl)

abbrev cellRbegun : Cell := { cellR with phase := .reloading, committedView := view20p, payload := { cellR.payload with iteratorCode := 0, accumulatorCode := 0, flightCode := some () } }

theorem cycleStep_finishR : LifecycleRule rulesSem (.finish 0 { c5 with ambient := 8 }) c5 c6 := by
  exact LifecycleRule.finish (sem := rulesSem) (cell := cellRbegun) (hlook := by congr)
    (hphase := rfl)
    (htarget := ⟨cellRbegun, by congr, by
      change view20p.keys = {20}
      apply Finset.ext
      intro key
      rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
      change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
      by_cases hkey : key = 20 <;> simp [hkey], by
      intro key provider hkv
      change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
      by_cases hkey : key = 20
      · subst key
        rw [Finmap.lookup_insert] at hkv
        have hp : provider = 3 := (Option.some.inj hkv).symm
        subst provider
        exact provides20_c3
      · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
          Finmap.lookup_empty] at hkv
        cases hkv⟩)
    (hstage := rfl)

theorem cycleStep_insertC : OrchestrationRule (.insert (some 0) 1 cellC) c6 c7 := by
  exact OrchestrationRule.insert (registrar := some 0) (fresh := 1) (child := cellC)
    (by
      simp [c6, c5, c4, c3, c2, c1, finishState, beginState, editCell, updateFiber,
        allocate, beginPayload, rulesSem, cellP, cellR, Finmap.lookup_insert,
        Finmap.lookup_insert_of_ne, Finmap.lookup_empty])
    (by
      simp [c6, c5, c4, c3, c2, c1, finishState, beginState, editCell, updateFiber,
        allocate, beginPayload, rulesSem, cellP, cellR, Finmap.lookup_insert])
    (by
      simp [CanonicalInitialCell, Registered, c6, c5, c4, c3, c2, c1, finishState,
        beginState, editCell, updateFiber, allocate, beginPayload, rulesSem, cellP,
        cellR, Finmap.lookup_insert]
      decide)
    (by intro name cell' h
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey)

theorem cycleTargetViewAt_c7_1 : TargetViewAt c7 1 view20p := by
  refine ⟨cellC, by simp [c7, c6, allocate, Finmap.lookup_insert], ?_, ?_⟩
  · change view20p.keys = {20}
    apply Finset.ext
    intro key
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
    change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
    by_cases hkey : key = 20 <;> simp [hkey]
  · intro key provider hkv
    change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
    by_cases hkey : key = 20
    · subst key
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 3 := (Option.some.inj hkv).symm
      subst provider
      exact provides20_c3
    · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey, Finmap.lookup_empty] at hkv
      cases hkv

abbrev cellCbegun : Cell := { cellC with phase := .reloading, committedView := view20p, payload := { cellC.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }

theorem cycleStep_beginC : LifecycleRule rulesSem (.begin 1 view20p ()) c7 c8 := by
  exact LifecycleRule.begin (sem := rulesSem) (cell := cellC)
    (hlook := by simp [c7, c6, allocate, Finmap.lookup_insert])
    (hphase := rfl) (hretired := rfl) (htarget := cycleTargetViewAt_c7_1) (hlaunch := rfl)

theorem cycleStep_iterC : LifecycleRule rulesSem (.iter 1 0 1 { c8 with ambient := 7 }) c8 c9 := by
  exact LifecycleRule.iter (sem := rulesSem) (cell := cellCbegun) (hlook := by congr)
    (hphase := rfl)
    (htarget := by
      refine ⟨cellCbegun, by congr, ?_, ?_⟩
      · change view20p.keys = {20}
        apply Finset.ext
        intro key
        rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
        change (key = 20 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 20
        by_cases hkey : key = 20 <;> simp [hkey]
      · intro key provider hkv
        change Finmap.lookup key (Finmap.insert 20 3 (∅ : Finmap (fun _ : Nat => Nat))) = some provider at hkv
        by_cases hkey : key = 20
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have hp : provider = 3 := (Option.some.inj hkv).symm
          subst provider
          exact provides20_c3
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
            Finmap.lookup_empty] at hkv
          cases hkv)
    (hstage := rfl)
    (hrank := by decide)

abbrev cellCitered : Cell := { cellCbegun with payload := { cellCbegun.payload with iteratorCode := 0, accumulatorCode := 1 } }
abbrev cellCretired : Cell := { cellCitered with retired := true }
abbrev cellPretired : Cell := { cellPactive with retired := true }
abbrev cellPunloading : Cell := { cellPretired with phase := .unloading, payload := { cellPretired.payload with failureData := some () } }

theorem cycleStep_retireC : OrchestrationRule (.retire 1 cellCitered) c9 c10 := by
  exact OrchestrationRule.retire (by congr)

theorem cycleStep_retireP : OrchestrationRule (.retire 3 cellPactive) c10 c11 := by
  exact OrchestrationRule.retire (by congr)

theorem cycleStep_raiseP : LifecycleRule rulesSem (.raise 3 ()) c11 c12 := by
  exact LifecycleRule.raise (sem := rulesSem) (cell := cellPretired) (hlook := by congr)
    (hphase := by right; rfl) (hreal := rfl)

abbrev cellCunloading : Cell := { cellCretired with phase := .unloading, payload := { cellCretired.payload with accumulatorCode := 2 } }
abbrev cellCinactive : Cell := { cellCunloading with phase := .inactive, committedView := ∅, payload := { cellCunloading.payload with flightCode := none } }
abbrev cellRactive : Cell := { cellRbegun with phase := .active }
abbrev cellRleft : Cell := { cellRactive with phase := .unloading }
abbrev cellRinactive : Cell := { cellRleft with phase := .inactive, committedView := ∅, payload := { cellRleft.payload with flightCode := none } }
abbrev cellPfailed : Cell := { cellPunloading with phase := .failed, committedView := ∅, payload := { cellPunloading.payload with flightCode := none } }

theorem lookup_c12_3 : Finmap.lookup 3 c12.registry = some cellPunloading := by
  congr

theorem cycleTargetNot_c12_1 : ¬ TargetViewAt c12 1 view20p := by
  intro h
  rcases h with ⟨cell, hlook, _hkeys, hall⟩
  have hprov : ProvidesNow c12 3 20 := hall 20 3 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_c12_3] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem cycleStep_divertLandC : LifecycleRule rulesSem (.divertLand 1 () 1 c12) c12 c13 := by
  exact LifecycleRule.divertLand (sem := rulesSem) (cell := cellCretired) (hlook := by congr)
    (hphase := rfl) (hchanged := cycleTargetNot_c12_1) (hland := rfl)

theorem lookup_c13_0 : Finmap.lookup 0 c13.registry = some cellRactive := by
  congr

theorem lookup_c13_1 : Finmap.lookup 1 c13.registry = some cellCunloading := by
  congr

theorem lookup_c13_3 : Finmap.lookup 3 c13.registry = some cellPunloading := by
  congr

theorem c13_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent c13.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = view20p := by
  intro hlook
  by_cases hd3 : dependent = 3
  · subst dependent
    rw [lookup_c13_3] at hlook
    cases hlook with | refl
    left; rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_c13_1] at hlook
      cases hlook with | refl
      right; rfl
    · by_cases hd0 : dependent = 0
      · subst dependent
        rw [lookup_c13_0] at hlook
        cases hlook with | refl
        right; rfl
      · have hnone : Finmap.lookup dependent c13.registry = none := by
          simp [c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1,
            divertLandState, raiseState, retireState, iterState, finishState, beginState,
            editCell, updateFiber, allocate, iterPayload, beginPayload, rulesSem,
            Finmap.lookup_insert, Finmap.lookup_insert_of_ne, Finmap.lookup_empty,
            hd3, hd1, hd0]
        rw [hnone] at hlook
        cases hlook

theorem cycleStep_unloadC : LifecycleRule rulesSem (.unload 1 { c13 with ambient := c13.ambient + 2 }) c13 c14 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellCunloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases c13_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 20
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h31 : (3 : Nat) = 1 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_c14_0 : Finmap.lookup 0 c14.registry = some cellRactive := by
  congr

theorem lookup_c14_3 : Finmap.lookup 3 c14.registry = some cellPunloading := by
  congr

theorem cycleTargetNot_c14_0 : ¬ TargetViewAt c14 0 view20p := by
  intro h
  rcases h with ⟨cell, hlook, _hkeys, hall⟩
  have hprov : ProvidesNow c14 3 20 := hall 20 3 (Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat)))
  rcases hprov with ⟨cell', hlook', _htable, hphase⟩
  rw [lookup_c14_3] at hlook'
  cases hlook' with | refl
  simp at hphase

theorem cycleStep_leaveR : LifecycleRule rulesSem (.leave 0) c14 c15 := by
  exact LifecycleRule.leave (sem := rulesSem) (cell := cellRactive) (hlook := by congr)
    (hphase := rfl) (hchanged := cycleTargetNot_c14_0)

theorem lookup_c15_0 : Finmap.lookup 0 c15.registry = some cellRleft := by
  congr

theorem lookup_c15_1 : Finmap.lookup 1 c15.registry = some cellCinactive := by
  congr

theorem lookup_c15_3 : Finmap.lookup 3 c15.registry = some cellPunloading := by
  congr

theorem c15_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent c15.registry = some cell →
      cell.committedView = ∅ ∨ cell.committedView = view20p := by
  intro hlook
  by_cases hd3 : dependent = 3
  · subst dependent
    rw [lookup_c15_3] at hlook
    cases hlook with | refl
    left; rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_c15_1] at hlook
      cases hlook with | refl
      left; rfl
    · by_cases hd0 : dependent = 0
      · subst dependent
        rw [lookup_c15_0] at hlook
        cases hlook with | refl
        right; rfl
      · have hnone : Finmap.lookup dependent c15.registry = none := by
          simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1,
            leaveState, unloadState, divertLandState, raiseState, retireState,
            iterState, finishState, beginState, editCell, updateFiber, allocate,
            iterPayload, beginPayload, rulesSem, Finmap.lookup_insert,
            Finmap.lookup_insert_of_ne, Finmap.lookup_empty, hd3, hd1, hd0]
        rw [hnone] at hlook
        cases hlook

theorem cycleStep_unloadR : LifecycleRule rulesSem (.unload 0 c15) c15 c16 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellRleft) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      rcases c15_views dependent cell hlook with hview | hview
      · rw [hview] at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [hview] at hkv
        by_cases hk : key = 20
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have h30 : (3 : Nat) = 0 := Option.some.inj hkv
          omega
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hk, Finmap.lookup_empty] at hkv
          cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_c16_3 : Finmap.lookup 3 c16.registry = some cellPunloading := by
  congr

theorem lookup_c16_1 : Finmap.lookup 1 c16.registry = some cellCinactive := by
  congr

theorem lookup_c16_0 : Finmap.lookup 0 c16.registry = some cellRinactive := by
  congr

theorem c16_views (dependent : Nat) (cell : Cell) :
    Finmap.lookup dependent c16.registry = some cell → cell.committedView = ∅ := by
  intro hlook
  by_cases hd3 : dependent = 3
  · subst dependent
    rw [lookup_c16_3] at hlook
    cases hlook with | refl
    rfl
  · by_cases hd1 : dependent = 1
    · subst dependent
      rw [lookup_c16_1] at hlook
      cases hlook with | refl
      rfl
    · by_cases hd0 : dependent = 0
      · subst dependent
        rw [lookup_c16_0] at hlook
        cases hlook with | refl
        rfl
      · have hnone : Finmap.lookup dependent c16.registry = none := by
          simp [unloadState, leaveState, divertLandState, raiseState, retireState,
            iterState, finishState, beginState, editCell, updateFiber, allocate, hd3, hd1, hd0]
        rw [hnone] at hlook
        cases hlook

theorem cycleStep_unloadP : LifecycleRule rulesSem (.unload 3 c16) c16 c17 := by
  exact LifecycleRule.unload (sem := rulesSem) (cell := cellPunloading) (hlook := by congr)
    (hphase := rfl)
    (hfree := by
      intro h
      rcases h with ⟨dependent, _hne, _hinst, cell, key, hlook, _hkey, hkv⟩
      have hview : cell.committedView = ∅ := c16_views dependent cell hlook
      rw [hview] at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv)
    (haccumulator := by unfold rulesSem fixtureAccumulator; rfl)

theorem lookup_c17_3 : Finmap.lookup 3 c17.registry = some cellPfailed := by
  congr

theorem lookup_c17_1 : Finmap.lookup 1 c17.registry = some cellCinactive := by
  congr

theorem lookup_c17_0 : Finmap.lookup 0 c17.registry = some cellRinactive := by
  congr

theorem cycleStep_removeP : OrchestrationRule (.remove 3) c17 c18 := by
  exact OrchestrationRule.remove (cell := cellPfailed) (hlook := by congr)
    (hretired := rfl) (hphase := by right; rfl) (hnoChild := by
      intro name cell' h hparent
      by_cases hd3 : name = 3
      · subst name
        rw [lookup_c17_3] at h
        cases h with | refl
        cases hparent
      · by_cases hd1 : name = 1
        · subst name
          rw [lookup_c17_1] at h
          cases h with | refl
          cases hparent
        · by_cases hd0 : name = 0
          · subst name
            rw [lookup_c17_0] at h
            cases h with | refl
            cases hparent
          · have hnone : Finmap.lookup name c17.registry = none := by
              simp [unloadState, leaveState, divertLandState, raiseState,
                retireState, iterState, finishState, beginState, editCell, updateFiber,
                allocate, hd3, hd1, hd0]
            rw [hnone] at h
            cases h)

theorem cycleStep_insertN : OrchestrationRule (.insert (some 1) 2 cellN) c18 c19 := by
  exact OrchestrationRule.insert (registrar := some 1) (fresh := 2) (child := cellN)
    (by decide) (by decide)
    (by
      simp [CanonicalInitialCell, Registered, removeState, unloadState,
        leaveState, divertLandState, raiseState, retireState, iterState, finishState,
        beginState, editCell, updateFiber, allocate]
      rfl)
    (by intro name cell' h
        by_cases hd1 : name = 1
        · subst name
          simp [removeState, unloadState, leaveState, divertLandState, raiseState,
            retireState, iterState, finishState, beginState, editCell, updateFiber,
            allocate] at h
          have hcell' : cell' = cellCinactive := h.symm
          subst cell'
          apply Finset.disjoint_left.mpr
          grind only [← Finset.notMem_empty]
        · by_cases hd0 : name = 0
          · subst name
            simp [removeState, unloadState, leaveState, divertLandState,
              raiseState, retireState, iterState, finishState, beginState, editCell,
              updateFiber, allocate] at h
            have hcell' : cell' = cellRinactive := h.symm
            subst cell'
            apply Finset.disjoint_left.mpr
            intro key hkey
            simp at hkey
            subst key
            simp
          · have hnone : Finmap.lookup name c18.registry = none := by
              by_cases hd3 : name = 3
              · subst name
                rfl
              · by_cases hd2 : name = 2
                · subst name
                  decide
                · simp [removeState, unloadState, leaveState,
                    divertLandState, raiseState, retireState, iterState, finishState,
                    beginState, editCell, updateFiber, allocate, hd1, hd0, hd3]
            rw [hnone] at h
            cases h)

/-! ### Cycle-trace endpoint facts -/

theorem lookup_c19_0 : Finmap.lookup 0 c19.registry = some cellRinactive := by
  congr

theorem lookup_c19_1 : Finmap.lookup 1 c19.registry = some cellCinactive := by
  congr

theorem lookup_c19_2 : Finmap.lookup 2 c19.registry = some cellN := by
  congr

theorem c19_lookup_none (name : Nat) (hd0 : name ≠ 0) (hd1 : name ≠ 1) (hd2 : name ≠ 2) :
    Finmap.lookup name c19.registry = none := by
  by_cases hd3 : name = 3
  · subst name
    decide
  · simp [allocate, removeState, unloadState, leaveState, divertLandState,
      raiseState, retireState, iterState, finishState, beginState, editCell, updateFiber,
      hd0, hd1, hd2, hd3]

theorem cycleEndpoint_parentEdges :
    (Finmap.lookup 1 c19.registry).isSome ∧
      (∀ cell, Finmap.lookup 1 c19.registry = some cell → cell.parent = some 0) ∧
      (∀ cell, Finmap.lookup 2 c19.registry = some cell → cell.parent = some 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  all_goals
    intro _ h
    cases h with | refl
    rfl
theorem cycleEndpoint_providerEdge :
    (∀ cell, Finmap.lookup 2 c19.registry = some cell →
      20 ∈ cell.component.provides) ∧
      (∀ cell, Finmap.lookup 0 c19.registry = some cell →
        cell.component.requires = {20}) ∧
      ¬ ProvidesNow c19 3 20 := by
  refine ⟨?_, ?_, ?_⟩
  · intro cell h
    cases h with | refl
    simp
  · intro cell h
    cases h with | refl
    rfl
  · rintro ⟨cell, hlook, _htable, _hphase⟩
    cases hlook

theorem cycleEndpoint_precedenceAcyclic :
    (cellR.birth < cellC.birth ∧ cellC.birth < cellN.birth) ∧
      (∀ cell, Finmap.lookup 0 c19.registry = some cell → cell.birth = cellR.birth) ∧
      (∀ cell, Finmap.lookup 1 c19.registry = some cell → cell.birth = cellC.birth) ∧
      (∀ cell, Finmap.lookup 2 c19.registry = some cell → cell.birth = cellN.birth) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro cell h
    rw [lookup_c19_0] at h
    cases h with | refl
    rfl
  · intro cell h
    rw [lookup_c19_1] at h
    cases h with | refl
    rfl
  · intro cell h
    rw [lookup_c19_2] at h
    cases h with | refl
    rfl

theorem cycleEndpoint_lifetimeFresh :
    (∀ name cell, Finmap.lookup name c19.registry = some cell → name ∈ c19.ledger.everIssued) ∧
      c19.allocationHistory.Nodup := by
  refine ⟨?_, ?_⟩
  · intro name cell h
    by_cases hd2 : name = 2
    · subst name
      rw [lookup_c19_2] at h
      cases h with | refl
      decide
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        decide
      · by_cases hd0 : name = 0
        · subst name
          rw [lookup_c19_0] at h
          cases h with | refl
          decide
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · decide

def cycleProfile : WellFormedProfile Nat Nat Nat Unit Nat Nat Unit Unit Nat :=
  { lifecycleCoherent := fun (_ : State) => True
    root := fun (_ : State) => True
    declarations := fun (_ : State) => True }

theorem c19_parentClosed : ParentClosed c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    trivial
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      change 0 ∈ c19.registry.keys
      rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
      rw [lookup_c19_0]
      rfl
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        change 1 ∈ c19.registry.keys
        rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
        rw [lookup_c19_1]
        rfl
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_parentAcyclic : ParentAcyclic c19 := by
  unfold ParentAcyclic
  have acc0 : Acc (ParentStep c19) 0 := by
    constructor
    intro parent hp
    rcases hp with ⟨c, hc, hpar⟩
    rw [lookup_c19_0] at hc
    cases hc with | refl
    cases hpar
  have acc1 : Acc (ParentStep c19) 1 := by
    constructor
    intro parent hp
    rcases hp with ⟨c, hc, hpar⟩
    rw [lookup_c19_1] at hc
    cases hc with | refl
    have h0 : 0 = parent := Option.some.inj hpar
    subst parent
    exact acc0
  have acc2 : Acc (ParentStep c19) 2 := by
    constructor
    intro parent hp
    rcases hp with ⟨c, hc, hpar⟩
    rw [lookup_c19_2] at hc
    cases hc with | refl
    have h1 : 1 = parent := Option.some.inj hpar
    subst parent
    exact acc1
  constructor
  intro name
  by_cases hd2 : name = 2
  · subst name
    exact acc2
  · by_cases hd1 : name = 1
    · subst name
      exact acc1
    · by_cases hd0 : name = 0
      · subst name
        exact acc0
      · constructor
        intro parent hp
        rcases hp with ⟨c, hc, _hpar⟩
        rw [c19_lookup_none name hd0 hd1 hd2] at hc
        cases hc

theorem c19_tableConfined : TableConfined c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    intro key hkey
    change key ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_insert] at hkey
    rcases hkey with hkey | hempty
    · subst key
      simp
    · rw [Finmap.mem_def] at hempty
      change key ∈ (∅ : Multiset Nat) at hempty
      simp at hempty
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key hkey
      change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
      rw [Finmap.mem_keys, Finmap.mem_def] at hkey
      change key ∈ (∅ : Multiset Nat) at hkey
      simp at hkey
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key hkey
        change key ∈ (Finmap.insert 20 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
        rw [Finmap.mem_keys, Finmap.mem_insert] at hkey
        rcases hkey with hkey | hempty
        · subst key
          simp
        · rw [Finmap.mem_def] at hempty
          change key ∈ (∅ : Multiset Nat) at hempty
          simp at hempty
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_provisionDisjoint : ProvisionDisjoint c19 := by
  intro a b ca cb ha hb hab
  by_cases hd0a : a = 0
  · subst a
    rw [lookup_c19_0] at ha
    cases ha with | refl
    by_cases hd1b : b = 1
    · subst b
      rw [lookup_c19_1] at hb
      cases hb with | refl
      apply Finset.disjoint_left.mpr
      intro key hkey
      simp at hkey ⊢
    · by_cases hd2b : b = 2
      · subst b
        rw [lookup_c19_2] at hb
        cases hb with | refl
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey
        subst key
        simp
      · by_cases hd0b : b = 0
        · subst b
          rw [lookup_c19_0] at hb
          cases hb with | refl
          exfalso
          exact hab rfl
        · rw [c19_lookup_none b hd0b hd1b hd2b] at hb
          cases hb
  · by_cases hd1a : a = 1
    · subst a
      rw [lookup_c19_1] at ha
      cases ha with | refl
      by_cases hd0b : b = 0
      · subst b
        rw [lookup_c19_0] at hb
        cases hb with | refl
        apply Finset.disjoint_left.mpr
        intro key hkey
        simp at hkey ⊢
      · by_cases hd2b : b = 2
        · subst b
          rw [lookup_c19_2] at hb
          cases hb with | refl
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey ⊢
        · by_cases hd1b : b = 1
          · subst b
            rw [lookup_c19_1] at hb
            cases hb with | refl
            exfalso
            exact hab rfl
          · rw [c19_lookup_none b hd0b hd1b hd2b] at hb
            cases hb
    · by_cases hd2a : a = 2
      · subst a
        rw [lookup_c19_2] at ha
        cases ha with | refl
        by_cases hd0b : b = 0
        · subst b
          rw [lookup_c19_0] at hb
          cases hb with | refl
          apply Finset.disjoint_left.mpr
          intro key hkey
          simp at hkey
          subst key
          simp
        · by_cases hd1b : b = 1
          · subst b
            rw [lookup_c19_1] at hb
            cases hb with | refl
            apply Finset.disjoint_left.mpr
            intro key hkey
            simp at hkey ⊢
          · by_cases hd2b : b = 2
            · subst b
              rw [lookup_c19_2] at hb
              cases hb with | refl
              exfalso
              exact hab rfl
            · rw [c19_lookup_none b hd0b hd1b hd2b] at hb
              cases hb
      · rw [c19_lookup_none a hd0a hd1a hd2a] at ha
        cases ha

theorem c19_committedViewClosed : CommittedViewClosed c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    intro key provider hkv
    rw [Finmap.lookup_empty] at hkv
    cases hkv
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key provider hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_committedProvidersClosed : CommittedProvidersClosed c19 := by
  intro name cell h
  by_cases hd0 : name = 0
  · subst name
    rw [lookup_c19_0] at h
    cases h with | refl
    intro key provider hkv
    rw [Finmap.lookup_empty] at hkv
    cases hkv
  · by_cases hd1 : name = 1
    · subst name
      rw [lookup_c19_1] at h
      cases h with | refl
      intro key provider hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv
    · by_cases hd2 : name = 2
      · subst name
        rw [lookup_c19_2] at h
        cases h with | refl
        intro key provider hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
      · rw [c19_lookup_none name hd0 hd1 hd2] at h
        cases h

theorem c19_dataCoherent : DataCoherent c19 := by
  unfold DataCoherent
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro name cell h hactive
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      simp at hactive
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        simp at hactive
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          simp at hactive
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · intro name cell h
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      intro key hkey
      change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
      rw [Finmap.mem_keys, Finmap.mem_def] at hkey
      change key ∈ (∅ : Multiset Nat) at hkey
      simp at hkey
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        intro key hkey
        change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
        rw [Finmap.mem_keys, Finmap.mem_def] at hkey
        change key ∈ (∅ : Multiset Nat) at hkey
        simp at hkey
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          intro key hkey
          change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
          rw [Finmap.mem_keys, Finmap.mem_def] at hkey
          change key ∈ (∅ : Multiset Nat) at hkey
          simp at hkey
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · intro name cell h
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      rfl
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        rfl
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          rfl
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · refine ⟨by decide, ?_⟩
    intro name cell h
    by_cases hd0 : name = 0
    · subst name
      rw [lookup_c19_0] at h
      cases h with | refl
      exact ⟨by decide, by decide⟩
    · by_cases hd1 : name = 1
      · subst name
        rw [lookup_c19_1] at h
        cases h with | refl
        exact ⟨by decide, by decide⟩
      · by_cases hd2 : name = 2
        · subst name
          rw [lookup_c19_2] at h
          cases h with | refl
          exact ⟨by decide, by decide⟩
        · rw [c19_lookup_none name hd0 hd1 hd2] at h
          cases h
  · refine ⟨?_, ?_⟩
    · intro name hkey
      by_cases hd0 : name = 0
      · subst name; decide
      · by_cases hd1 : name = 1
        · subst name; decide
        · by_cases hd2 : name = 2
          · subst name; decide
          · have hisome : (Finmap.lookup name c19.registry).isSome := by
              rw [Finmap.lookup_isSome, ← Finmap.mem_keys]
              exact hkey
            rw [c19_lookup_none name hd0 hd1 hd2] at hisome
            simp at hisome
    · intro name hhist
      simp [allocate, removeState, unloadState, leaveState, divertLandState,
        raiseState, retireState, iterState, finishState, beginState, editCell,
        updateFiber, iterPayload] at hhist
      rcases hhist with h3 | h0 | h1 | h2
      all_goals
        subst name; decide

theorem cycleEndpoint_wellFormed : WellFormed cycleProfile c19 :=
  ⟨c19_parentClosed, c19_parentAcyclic, c19_tableConfined, c19_provisionDisjoint,
    c19_committedViewClosed, c19_committedProvidersClosed, c19_dataCoherent,
    trivial, trivial, trivial⟩


/-! ### Nonconstant factorization evidence -/

abbrev cell1begun : Cell := { cell1 with phase := .reloading, committedView := ∅, payload := { cell1.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }
abbrev cell2begun : Cell := { cell2 with phase := .reloading, committedView := Finmap.insert 10 1 (∅ : Finmap (fun _ : Nat => Nat)), payload := { cell2.payload with iteratorCode := 1, accumulatorCode := 0, flightCode := some () } }

theorem factorization_nonconstant :
    ∃ label1 label2 before1 before2 m1 m2, SelectedBody rulesSem label1 before1 m1 ∧
      SelectedBody rulesSem label2 before2 m2 ∧ m1 ≠ m2 := by
  refine ⟨.inr (.iter 2 0 1 { s6 with ambient := 7 }), .inr (.iter 1 0 1 { s2 with ambient := 9 }),
    s6, s2, { s6 with ambient := 7 }, { s2 with ambient := 9 }, ?_, ?_, ?_⟩
  · refine ⟨cell2begun, by congr, rfl, targetViewAt_s6_2, rfl, by decide, rfl⟩
  · refine ⟨cell1begun, by congr, rfl, ?_, rfl, by decide, rfl⟩
    refine ⟨cell1begun, by congr, rfl, by
      intro key provider hkv
      change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
      rw [Finmap.lookup_empty] at hkv
      cases hkv⟩
  · intro h
    have hh := congrArg (fun state : State => state.ambient) h
    simp at hh

-/
end

end STC.Examples.GlobalRules
