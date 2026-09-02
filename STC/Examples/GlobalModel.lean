module

public import STC.State.Global.Observation

/-!
# Positive global-model evidence

This fixture exercises the data-only global carrier over concrete `Nat` names and
keys with `Unit` codes: two fibers (a provider and a nested consumer), ordered
allocation history, the D45 provider selection, D46 target view and quiescence,
D48 write/read frames, D50 relied-upon, D58 well-formedness, the D32 positive
representation, and the D33 lifted observation. Semantic rule reachability
remains a later lane.
-/

namespace STC.Examples.GlobalModel

open STC STC.State

@[expose] public section

abbrev Cell := FiberCell Nat Nat Nat Unit Unit Unit Unit Unit
abbrev State := GlobalState Nat Nat Nat Unit Unit Unit Unit Unit Unit

def empty : State :=
  { ambient := (), registry := ∅,
    coeffects := Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)),
    ledger := { everIssued := ∅ }, allocationHistory := [] }

theorem empty_history : empty.allocationHistory = [] := rfl

theorem empty_active : activeNames empty = ∅ := by
  simp [activeNames, empty]

def providerComponent : Component Nat Nat Unit Unit Unit Unit Unit :=
  { key := 1, requires := ∅, provides := {10}, actionCode := (), iteratorCode := (),
    accumulatorCode := (), flightCode := (), failureCode := () }

def consumerComponent : Component Nat Nat Unit Unit Unit Unit Unit :=
  { key := 2, requires := {10}, provides := {20}, actionCode := (), iteratorCode := (),
    accumulatorCode := (), flightCode := (), failureCode := () }

def providerCell : Cell :=
  { incarnation := 1, parent := none, birth := 0, component := providerComponent,
    committed := { entries := Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat)) },
    committedView := ∅, retired := false, phase := .inactive,
    payload :=
      { iteratorCode := (), accumulatorCode := (), flightCode := none, failureData := none } }

def consumerCell : Cell :=
  { incarnation := 2, parent := some 1, birth := 1, component := consumerComponent,
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload :=
      { iteratorCode := (), accumulatorCode := (), flightCode := none, failureData := none } }

def boundProviderCell : Cell := { providerCell with phase := .active }

def boundConsumerCell : Cell :=
  { consumerCell with phase := .active, committedView := Finmap.insert 10 1 ∅ }

def state0 : State := empty
def state1 : State := allocate state0 1 providerCell
def state2 : State := allocate state1 2 consumerCell

def boundProvider : State := updateFiber state2 1 boundProviderCell
def boundConsumer : State := updateFiber boundProvider 2 boundConsumerCell

/-! ### Allocation and registry facts -/

theorem state1_history : state1.allocationHistory = [1] := by
  rw [state1, allocate_history, state0, empty_history]
  rfl

theorem state2_history : state2.allocationHistory = [1, 2] := by
  rw [state2, allocate_history, state1_history]
  rfl

theorem state1_keys : state1.registry.keys = ({1} : Finset Nat) := by
  rw [state1, allocate_keys]
  rfl

theorem state2_keys : state2.registry.keys = ({1, 2} : Finset Nat) := by
  grind [state2, allocate_keys, state1_keys]

theorem bound_consumer_keys : boundConsumer.registry.keys = ({1, 2} : Finset Nat) := by
  grind [boundConsumer, updateFiber_keys, boundProvider, updateFiber_keys, state2_keys]

theorem allocation_static : state1.coeffects = empty.coeffects ∧ state1.ledger.everIssued = {1} := by
  constructor
  · rw [state1, allocate_coeffects]
    rfl
  · rw [state1, allocate_ledger, state0]
    rfl

/-! ### D45 provider selection -/

theorem lookup_bound_provider : Finmap.lookup 1 boundProvider.registry = some boundProviderCell := by
  simp [boundProvider, boundProviderCell, providerCell, updateFiber]

theorem lookup_bound_provider_in_consumer :
    Finmap.lookup 1 boundConsumer.registry = some boundProviderCell := by
  simp [boundConsumer, boundProvider, boundProviderCell, providerCell, boundConsumerCell,
    consumerCell, updateFiber]

theorem lookup_bound_consumer : Finmap.lookup 2 boundConsumer.registry = some boundConsumerCell := by
  simp [boundConsumer, boundProvider, boundConsumerCell, consumerCell, updateFiber]

theorem bound_consumer_provides : ProvidesNow boundConsumer 1 10 := by
  refine ⟨boundProviderCell, lookup_bound_provider_in_consumer, ?_, rfl⟩
  change 10 ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys
  rw [Finmap.mem_keys, Finmap.mem_insert]
  simp

theorem bound_consumer_provides_mem : 1 ∈ providersOf boundConsumer 10 :=
  providersOf_complete boundConsumer bound_consumer_provides

/-! ### D48 write-frame and read-noninterference -/

theorem activate_writeFrame : WriteFrame state2 1 boundProvider :=
  updateFiber_writeFrame state2 1 boundProviderCell

theorem activate_readNoninterference : ReadNoninterference state2 1 boundProvider :=
  updateFiber_readNoninterference state2 1 boundProviderCell

/-! ### D50 relied-upon -/

theorem bound_consumer_installed : Installed boundConsumer 2 :=
  ⟨boundConsumerCell, lookup_bound_consumer, by decide⟩

theorem bound_consumer_reliedUpon : ReliedUpon boundConsumer 2 1 := by
  refine ⟨by decide, bound_consumer_installed, boundConsumerCell, 10, lookup_bound_consumer, ?_, ?_⟩
  · simp [boundConsumerCell, consumerCell, consumerComponent]
  · exact Finmap.lookup_insert (∅ : Finmap (fun _ : Nat => Nat))

/-! ### D58 well-formed registry -/

theorem mem_keys_of_lookup {name : Nat} {cell : Cell}
    (h : Finmap.lookup name boundConsumer.registry = some cell) :
    name ∈ boundConsumer.registry.keys := by
  rw [Finmap.mem_keys, ← Finmap.lookup_isSome, h]
  rfl

theorem mem_bound_consumer_keys {name : Nat}
    (h : name ∈ boundConsumer.registry.keys) : name = 1 ∨ name = 2 := by
  rw [bound_consumer_keys] at h
  simp [Finset.mem_insert, Finset.mem_singleton] at h
  exact h

theorem provider_cell_of_lookup {name : Nat} {cell : Cell}
    (h : Finmap.lookup name boundConsumer.registry = some cell) (hname : name = 1) :
    cell = boundProviderCell := by
  subst name
  rw [lookup_bound_provider_in_consumer] at h
  exact (Option.some.inj h).symm

theorem consumer_cell_of_lookup {name : Nat} {cell : Cell}
    (h : Finmap.lookup name boundConsumer.registry = some cell) (hname : name = 2) :
    cell = boundConsumerCell := by
  subst name
  rw [lookup_bound_consumer] at h
  exact (Option.some.inj h).symm

def modelProfile : WellFormedProfile Nat Nat Nat Unit Unit Unit Unit Unit Unit :=
  { lifecycleCoherent := fun (_ : State) => True
    root := fun (_ : State) => True
    declarations := fun (_ : State) => True }

theorem model_parentClosed : ParentClosed boundConsumer := by
  intro name cell h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    trivial
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    simp [boundConsumerCell, consumerCell]
    rw [bound_consumer_keys]
    simp [Finset.mem_insert, Finset.mem_singleton]

theorem model_parentAcyclic : ParentAcyclic boundConsumer := by
  unfold ParentAcyclic
  constructor
  intro name
  constructor
  intro parent hp
  rcases hp with ⟨cell, h, hparent⟩
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    cases hparent
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    have hpar : some (1 : Nat) = some parent := by
      simpa [boundConsumerCell, consumerCell] using hparent
    have hp1 : 1 = parent := Option.some.inj hpar
    subst parent
    constructor
    intro p hp1
    rcases hp1 with ⟨c, hc, hpar⟩
    have hc0 := provider_cell_of_lookup hc (by decide : (1 : Nat) = 1)
    subst c
    cases hpar

theorem model_tableConfined : TableConfined boundConsumer := by
  intro name cell h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    intro key hkey
    change key ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def] at hkey
    change key = 10 ∨ key ∈ (∅ : Multiset Nat) at hkey
    simp at hkey
    subst key
    simp [boundProviderCell, providerCell, providerComponent]
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    intro key hkey
    change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_def] at hkey
    change key ∈ (∅ : Multiset Nat) at hkey
    simp at hkey

theorem model_provisionDisjoint : ProvisionDisjoint boundConsumer := by
  intro a b ca cb ha hb hab
  have hka := mem_bound_consumer_keys (mem_keys_of_lookup ha)
  have hkb := mem_bound_consumer_keys (mem_keys_of_lookup hb)
  rcases hka with h1 | h2 <;> rcases hkb with h1' | h2'
  · grind only
  · have hca := provider_cell_of_lookup ha h1
    have hcb := consumer_cell_of_lookup hb h2'
    subst ca
    subst cb
    apply Finset.disjoint_left.mpr
    intro key hkey
    simp [boundProviderCell, providerCell, providerComponent] at hkey
    subst key
    simp [boundConsumerCell, consumerCell, consumerComponent]
  · have hca := consumer_cell_of_lookup ha h2
    have hcb := provider_cell_of_lookup hb h1'
    subst ca
    subst cb
    apply Finset.disjoint_left.mpr
    intro key hkey
    simp [boundConsumerCell, consumerCell, consumerComponent] at hkey
    subst key
    simp [boundProviderCell, providerCell, providerComponent]
  · grind only

theorem model_committedViewClosed : CommittedViewClosed boundConsumer := by
  intro name cell h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    intro key provider hkv
    simp [boundProviderCell, providerCell, Finmap.lookup_empty] at hkv
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    intro key provider hkv
    by_cases hkey : key = 10
    · subst key
      rw [boundConsumerCell] at hkv
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      rw [bound_consumer_keys]
      simp [Finset.mem_insert, Finset.mem_singleton]
    · rw [boundConsumerCell] at hkv
      change Finmap.lookup key (Finmap.insert 10 (1 : Nat) (∅ : Finmap (fun _ : Nat => Nat))) =
          some provider at hkv
      rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
          Finmap.lookup_empty] at hkv
      cases hkv

theorem model_committedProvidersClosed : CommittedProvidersClosed boundConsumer := by
  intro name cell h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    intro key provider hkv
    simp [boundProviderCell, providerCell, Finmap.lookup_empty] at hkv
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    intro key provider hkv
    by_cases hkey : key = 10
    · subst key
      rw [boundConsumerCell] at hkv
      rw [Finmap.lookup_insert] at hkv
      have hp : provider = 1 := (Option.some.inj hkv).symm
      subst provider
      unfold CommittedProvides
      refine ⟨boundProviderCell, lookup_bound_provider_in_consumer, ?_, ?_⟩
      · change 10 ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys
        rw [Finmap.mem_keys, Finmap.mem_insert]
        simp
      · decide
    · rw [boundConsumerCell] at hkv
      change Finmap.lookup key (Finmap.insert 10 (1 : Nat) (∅ : Finmap (fun _ : Nat => Nat))) =
          some provider at hkv
      rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
          Finmap.lookup_empty] at hkv
      cases hkv

/-! ### D58 data-coherence invariants -/

theorem model_activeTableCoherent : ActiveTableCoherent boundConsumer := by
  intro name cell h hactive
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    intro key hkey
    change key ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def] at hkey
    change key = 10 ∨ key ∈ (∅ : Multiset Nat) at hkey
    simp at hkey
    subst key
    change 10 ∈ (Finmap.insert 10 (0 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def]
    simp
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    intro key hkey
    change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_def] at hkey
    change key ∈ (∅ : Multiset Nat) at hkey
    simp at hkey

theorem model_committedViewDomain : CommittedViewDomain boundConsumer := by
  intro name cell h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    intro key hkey
    change key ∈ (∅ : Finmap (fun _ : Nat => Nat)).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_def] at hkey
    change key ∈ (∅ : Multiset Nat) at hkey
    simp at hkey
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    intro key hkey
    change key ∈ (Finmap.insert 10 (1 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys at hkey
    rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def] at hkey
    change key = 10 ∨ key ∈ (∅ : Multiset Nat) at hkey
    simp at hkey
    subst key
    simp [boundConsumerCell, consumerCell, consumerComponent]

theorem model_incarnationCoherent : IncarnationCoherent boundConsumer := by
  intro name cell h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with h1 | h2
  · have hcell := provider_cell_of_lookup h h1
    subst cell
    subst name
    rfl
  · have hcell := consumer_cell_of_lookup h h2
    subst cell
    subst name
    rfl

theorem model_allocationCoherent : AllocationCoherent boundConsumer := by
  constructor
  · decide
  · intro name cell h
    have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
    rcases hk with h1 | h2
    · have hcell := provider_cell_of_lookup h h1
      subst cell
      subst name
      exact ⟨by decide, rfl⟩
    · have hcell := consumer_cell_of_lookup h h2
      subst cell
      subst name
      exact ⟨by decide, rfl⟩

theorem model_ledgerCoherent : LedgerCoherent boundConsumer := by
  constructor
  · intro name hkey
    rw [bound_consumer_keys] at hkey
    simp [Finset.mem_insert, Finset.mem_singleton] at hkey
    rcases hkey with rfl | rfl
    · simp [boundConsumer, boundProvider, state2, state1, state0, empty, updateFiber_ledger,
        allocate_ledger, Finset.mem_insert]
    · simp [boundConsumer, boundProvider, state2, state1, state0, empty, updateFiber_ledger,
        allocate_ledger, Finset.mem_insert]
  · intro name hhist
    simp [boundConsumer, boundProvider, state2, state1, state0, empty, updateFiber_history,
      allocate_history] at hhist
    rcases hhist with rfl | rfl
    · simp [boundConsumer, boundProvider, state2, state1, state0, empty, updateFiber_ledger,
        allocate_ledger, Finset.mem_insert]
    · simp [boundConsumer, boundProvider, state2, state1, state0, empty, updateFiber_ledger,
        allocate_ledger, Finset.mem_insert]

theorem model_wellFormed : WellFormed modelProfile boundConsumer := by
  refine ⟨model_parentClosed, model_parentAcyclic, model_tableConfined, model_provisionDisjoint,
    model_committedViewClosed, model_committedProvidersClosed, ?_, trivial, trivial, trivial⟩
  unfold DataCoherent
  refine ⟨model_activeTableCoherent, model_committedViewDomain, model_incarnationCoherent,
    model_allocationCoherent, model_ledgerCoherent⟩

/-! ### D46 target view and quiescence -/

theorem bound_consumer_targetSatisfied : targetSatisfied boundConsumer 2 := by
  rw [targetSatisfied_iff boundConsumer 2 lookup_bound_consumer]
  intro key hk
  simp [boundConsumerCell, consumerCell, consumerComponent] at hk
  subst key
  grind [bound_consumer_provides_mem]

theorem bound_consumer_targetView : targetView boundConsumer 2 = some ({1} : Finset Nat) := by
  have hsat := bound_consumer_targetSatisfied
  have hview : targetView boundConsumer 2 = some (targetProviders boundConsumer 2) :=
    (targetView_some_iff boundConsumer 2 (targetProviders boundConsumer 2)).mpr ⟨hsat, rfl⟩
  have hmem : ∀ provider, provider ∈ targetProviders boundConsumer 2 ↔
      ∃ key, key ∈ boundConsumerCell.component.requires ∧ provider ∈ providersOf boundConsumer key := by
    intro provider
    exact targetView_mem boundConsumer 2 hview lookup_bound_consumer
  have htp : targetProviders boundConsumer 2 = ({1} : Finset Nat) := by
    apply Finset.ext
    intro provider
    constructor
    · intro hp
      rcases (hmem provider).mp hp with ⟨key, hkey, hprov⟩
      simp [boundConsumerCell, consumerCell, consumerComponent] at hkey
      subst key
      grind [providersOf_unique modelProfile model_wellFormed hprov bound_consumer_provides_mem]
    · intro hp
      rw [Finset.mem_singleton] at hp
      subst provider
      exact (hmem 1).mpr ⟨10, by simp [boundConsumerCell, consumerCell, consumerComponent],
        bound_consumer_provides_mem⟩
  exact (targetView_some_iff boundConsumer 2 ({1} : Finset Nat)).mpr ⟨hsat, htp⟩

theorem bound_consumer_quiescent : Quiescent boundConsumer := by
  intro name fiber h
  have hk := mem_bound_consumer_keys (mem_keys_of_lookup h)
  rcases hk with rfl | rfl
  · rw [lookup_bound_provider_in_consumer] at h
    have hf : fiber = boundProviderCell := (Option.some.inj h).symm
    subst fiber
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · rfl
    · intro _hactive
      refine ⟨boundProviderCell, lookup_bound_provider_in_consumer, ?_, ?_⟩
      · change (∅ : Finmap (fun _ : Nat => Nat)).keys = ∅
        rw [Finmap.keys_empty]
      · intro key provider hkv
        change Finmap.lookup key (∅ : Finmap (fun _ : Nat => Nat)) = some provider at hkv
        rw [Finmap.lookup_empty] at hkv
        cases hkv
  · rw [lookup_bound_consumer] at h
    have hf : fiber = boundConsumerCell := (Option.some.inj h).symm
    subst fiber
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · rfl
    · intro _hactive
      refine ⟨boundConsumerCell, lookup_bound_consumer, ?_, ?_⟩
      · change (Finmap.insert 10 (1 : Nat) (∅ : Finmap (fun _ : Nat => Nat))).keys = ({10} : Finset Nat)
        apply Finset.ext
        intro key
        rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_def, Finset.mem_singleton]
        change (key = 10 ∨ key ∈ (∅ : Multiset Nat)) ↔ key = 10
        by_cases hkey : key = 10 <;> simp [hkey]
      · intro key provider hkv
        change Finmap.lookup key (Finmap.insert 10 (1 : Nat) (∅ : Finmap (fun _ : Nat => Nat))) =
            some provider at hkv
        by_cases hkey : key = 10
        · subst key
          rw [Finmap.lookup_insert] at hkv
          have hp : provider = 1 := (Option.some.inj hkv).symm
          subst provider
          exact bound_consumer_provides
        · rw [Finmap.lookup_insert_of_ne (∅ : Finmap (fun _ : Nat => Nat)) hkey,
            Finmap.lookup_empty] at hkv
          cases hkv

/-! ### D32 positive representation -/

theorem toPositive_keys_evidence : (toPositiveRegistry boundConsumer).keys = ({1, 2} : Finset Nat) := by
  rw [toPositive_keys, bound_consumer_keys]

theorem toPositive_lookup_evidence :
    Finmap.lookup 1 (toPositiveRegistry boundConsumer) = some (toPositiveCell boundProviderCell) :=
  toPositive_lookup_some boundConsumer 1 lookup_bound_provider_in_consumer

theorem toPositive_lookup_isSome_evidence :
    (Finmap.lookup 2 (toPositiveRegistry boundConsumer)).isSome ↔
      (Finmap.lookup 2 boundConsumer.registry).isSome :=
  toPositive_lookup_isSome_iff boundConsumer 2

/-! ### D33 lifted observation -/

def modelObservation : GlobalObservation (Name := Nat) (Key := Nat) (Value := Nat)
    (Action := Unit) (Iterator := Unit) (Accumulator := Unit) (Flight := Unit)
    (Failure := Unit) (Ambient := Unit) :=
  { registry := fun (_ : Nat) => equality Cell
    coeffects := equality (Finmap (fun _ : Nat => Nat))
    lifecycle := fun (_ : State) (_ : State) => True
    controlEdit := fun (_ : State) (_ : State) => True
    names := fun (_ : State) (_ : State) => True }

theorem stateObs_refl_evidence : StateObs modelObservation boundConsumer boundConsumer := by
  apply stateObs_refl
  · intro state
    trivial
  · intro state
    trivial
  · intro state
    trivial

theorem stateObs_eq_lifted_evidence :
    StateObs modelObservation boundConsumer boundConsumer ↔
      liftedStateObs (observationKit modelObservation)
        (fun state : State => state.registry) (fun state => state.coeffects)
        (fun state => state) (fun state => state) (fun state => state) boundConsumer boundConsumer :=
  stateObs_eq_lifted modelObservation

/-! ### Name-neutrality and factorization profiles -/

def unitAlphaState : AlphaAction Nat State :=
  { act := fun (_ : Equiv.Perm Nat) (state : State) => state
    act_id := by intro state; rfl
    act_comp := by intro χ ψ state; rfl
    act_inv := by intro χ state; rfl }

def unitCodeAlpha : AlphaCodeProfile Nat Unit State :=
  { act := fun (_ : Equiv.Perm Nat) (code : Unit) => code
    stateAction := unitAlphaState
    interprets := fun (_ : Unit) (_ : State) (_ : State) => True
    identity := by intro code; rfl
    composition := by intro χ ψ code; rfl
    equivariant := by intro χ code before after h; trivial }

theorem unitCodes_nameNeutral : NameNeutral unitCodeAlpha := by
  intro χ code
  rfl

def factorSelectedMap (_ : Unit) (state : State) : State := allocate state 3 boundProviderCell

def factorControlEdit (_ : Unit) (state : State) : State := state

def modelFactorization : FactorizationProfile State Unit :=
  { selectedMap := factorSelectedMap
    controlEdit := factorControlEdit
    replay := fun code state => factorControlEdit code (factorSelectedMap code state)
    frame := fun (_ : Unit) (_ : State) (_ : State) => True
    replay_equation := by intro code state; rfl
    frame_holds := by intro code state; trivial
    nonconstant := ⟨(), empty, state1, by
      intro h
      have hh := congrArg (fun state : State => state.allocationHistory) h
      rw [empty_history] at hh
      rw [show state1.allocationHistory = [1] by rw [state1, allocate_history, state0, empty_history]; rfl] at hh
      exact (by decide : ([] : List Nat) ≠ [1]) hh, by
      intro h
      have hh := congrArg (fun state : State => state.allocationHistory) h
      unfold factorSelectedMap at hh
      rw [allocate_history, allocate_history] at hh
      rw [empty_history] at hh
      rw [show state1.allocationHistory = [1] by rw [state1, allocate_history, state0, empty_history]; rfl] at hh
      exact (by decide : ([] ++ [3] : List Nat) ≠ [1] ++ [3]) hh⟩ }

end

end STC.Examples.GlobalModel
