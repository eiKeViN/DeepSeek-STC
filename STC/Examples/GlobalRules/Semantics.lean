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
theorem above, so the same non-degenerate semantics discharges every
rule premise. -/
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

end

end STC.Examples.GlobalRules
