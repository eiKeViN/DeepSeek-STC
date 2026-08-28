module

public import STC.Core.Iterator
public import STC.Foundation.Relation

/-!
# Generic R0 abstraction and simulation seam

`STC.Adapter` is a metatheory-side contract for a future concrete runtime
adapter.  It is intentionally one-way: a concrete state is mapped to an
abstract state, concrete labels are mapped to abstract labels, and each
concrete step supplies a forward abstract successor witness.  No concrete
runtime carrier, scheduler, converse simulation, bisimulation, or R1+
correctness theorem is introduced here.

The seam can be instantiated by a later adapter that connects
`STC.State.FinmapAdapter.ValidState`/`StateLike` to an abstract state and uses
`STC.RankedIterator` as its abstract labelled-step relation.  Such an
instantiation must provide its own admissibility, observation, and preservation
proofs; this file only records their required shape.

## Main declarations

* `StateRefinement`: one-way state abstraction with explicit observations and
  admissibility;
* `Simulates`: labelled concrete-to-abstract forward simulation.
-/

universe u v w x

namespace STC.Adapter

@[expose] public section

/-! ### State abstraction -/

section State

/-- A one-way concrete-to-abstract state refinement contract. -/
structure StateRefinement (Concrete : Type u) (Abstract : Type v) where
  abstract : Concrete → Abstract
  admissible : Concrete → Prop
  concreteObs : Concrete → Concrete → Prop
  abstractObs : RelSpec Abstract
  observes : RespectsOn concreteObs abstractObs.rel abstract

end State

/-! ### Labelled forward simulation -/

section Simulation

/-- A labelled forward simulation from a concrete relation to an abstract one. -/
structure Simulates
    (Concrete : Type u) (Abstract : Type v) (CLabel : Type w) (ALabel : Type x) where
  refinement : StateRefinement Concrete Abstract
  labelMap : CLabel → ALabel
  concreteStep : Concrete → CLabel → Concrete → Prop
  abstractStep : Abstract → ALabel → Abstract → Prop
  forward :
    ∀ {c label c'},
      refinement.admissible c →
      concreteStep c label c' →
      ∃ a',
        abstractStep (refinement.abstract c) (labelMap label) a' ∧
          refinement.abstractObs.rel (refinement.abstract c') a'

end Simulation

end

end STC.Adapter
