module

public import Mathlib.GroupTheory.Perm.Basic
public import STC.Core.Iterator

/-!
# The alpha action core

The generic alpha-renaming layer consumed by the ADR-04/ADR-06 architecture: one
explicit group-action record on `Equiv.Perm N` under the ADR-06 composition convention,
the conjugated-endomorphism view of selected inverses, the preservation/reflection
invariant, and the tag-preserving actions on the P1/P2/P4 result carriers.  In this
name-neutral profile the error `E` and continuation `Q` carriers are deliberately left
unchanged; a named-payload profile must supply its own actions.

## Main declarations

* `AlphaAction`: the explicit permutation action with identity/composition/inverse laws;
* `AlphaInvariant`: the selected relation is preserved and reflected by every
  permutation;
* `renameUndo`: the conjugated endomorphism `z ↦ A.act χ (f (A.act χ.symm z))`;
* `renameEffectResult`, `renameFailure`, `renameExec`, `renameStage`: tag-preserving
  result-carrier actions with rewriting equations and `_id`/`_comp`/`_inv` laws.
-/

universe u v

namespace STC

@[expose] public section

/-! ### The action carrier and the conjugated inverse -/

section ActionCore

variable {N : Type u} {X : Type v}

/-- One generic alpha-renaming witness: an explicit group action of `Equiv.Perm N` on
the state carrier, under the ADR-06 convention that `χ * ψ` applies `ψ` first.  The
action is an explicit reindexing witness; no global `Setoid`, quotient, or
equality-derived action is inferred. -/
structure AlphaAction (N : Type u) (X : Type v) where
  act : Equiv.Perm N → X → X
  act_id : ∀ x, act (Equiv.refl N) x = x
  act_comp : ∀ (χ ψ : Equiv.Perm N) x,
    act (χ * ψ) x = act χ (act ψ x)
  act_inv : ∀ (χ : Equiv.Perm N) x,
    act χ.symm (act χ x) = x

namespace AlphaAction

/-- The opposite cancellation direction, derived from the composition law: applying
`χ` after `χ.symm` is the identity. -/
theorem alpha_act_inv_right (A : AlphaAction N X) (χ : Equiv.Perm N) (x : X) :
    A.act χ (A.act χ.symm x) = x := by
  have h := A.act_comp χ χ.symm x
  have hmul : χ * χ.symm = Equiv.refl N := by
    ext n
    simp
  rw [hmul, A.act_id] at h
  exact h.symm

end AlphaAction

/-- The selected relation is preserved and reflected by every permutation action. -/
def AlphaInvariant (A : AlphaAction N X) (R : X → X → Prop) : Prop :=
  ∀ χ x y, R x y ↔ R (A.act χ x) (A.act χ y)

/-- The preservation direction of `AlphaInvariant`. -/
theorem alphaInvariant_preserve {A : AlphaAction N X} {R : X → X → Prop}
    (hinv : AlphaInvariant A R) {χ : Equiv.Perm N} {x y : X} (h : R x y) :
    R (A.act χ x) (A.act χ y) :=
  (hinv χ x y).1 h

/-- The reflection direction of `AlphaInvariant`. -/
theorem alphaInvariant_reflect {A : AlphaAction N X} {R : X → X → Prop}
    (hinv : AlphaInvariant A R) {χ : Equiv.Perm N} {x y : X}
    (h : R (A.act χ x) (A.act χ y)) : R x y :=
  (hinv χ x y).2 h

/-- Equality is invariant under every action: an action can never identify distinct
states. -/
theorem alphaInvariant_eq (A : AlphaAction N X) :
    AlphaInvariant A (fun x y => x = y) := by
  intro χ x y
  constructor
  · intro h
    exact congrArg (A.act χ) h
  · intro h
    have hs := congrArg (A.act χ.symm) h
    simpa [A.act_inv] using hs

/-- The conjugated endomorphism view of a selected inverse: rename the argument, apply
the inverse, rename the result. -/
def renameUndo (A : AlphaAction N X) (χ : Equiv.Perm N) (undo : X → X) : X → X :=
  fun z => A.act χ (undo (A.act χ.symm z))

/-- The pointwise equation of the conjugated endomorphism. -/
theorem renameUndo_apply (A : AlphaAction N X) (χ : Equiv.Perm N) (undo : X → X)
    (z : X) :
    renameUndo A χ undo z = A.act χ (undo (A.act χ.symm z)) := rfl

/-- Conjugation by the identity permutation leaves the map unchanged. -/
theorem renameUndo_id (A : AlphaAction N X) (undo : X → X) :
    renameUndo A (Equiv.refl N) undo = undo := by
  funext z
  simp [renameUndo, A.act_id]

/-- Conjugation preserves the identity map. -/
theorem renameUndo_id_fn (A : AlphaAction N X) (χ : Equiv.Perm N) :
    renameUndo A χ id = id := by
  funext z
  simp [renameUndo, AlphaAction.alpha_act_inv_right]

/-- Conjugation distributes over function composition, preserving the outer-after-inner
order fixed by P2's `Transformation.twisted` and P4's `execFrom` inverse accumulation. -/
theorem renameUndo_comp (A : AlphaAction N X) (χ : Equiv.Perm N) (f g : X → X) :
    renameUndo A χ (f ∘ g) = renameUndo A χ f ∘ renameUndo A χ g := by
  funext z
  simp [renameUndo, A.act_inv]

/-- Conjugation accumulates over permutation composition in the reverse order: `χ * ψ`
acts `ψ` first on names, so `ψ` is conjugated first. -/
theorem renameUndo_comp_perm (A : AlphaAction N X) (χ ψ : Equiv.Perm N) (f : X → X) :
    renameUndo A (χ * ψ) f = renameUndo A χ (renameUndo A ψ f) := by
  have hsymm : (χ * ψ).symm = ψ.symm * χ.symm := by
    show (χ * ψ)⁻¹ = ψ⁻¹ * χ⁻¹
    simp
  funext z
  simp [renameUndo, hsymm, A.act_comp]

/-- Conjugating by the inverse permutation undoes the conjugation. -/
theorem renameUndo_inv (A : AlphaAction N X) (χ : Equiv.Perm N) (f : X → X) :
    renameUndo A χ.symm (renameUndo A χ f) = f := by
  funext z
  simp [renameUndo, A.act_inv]

/-- The opposite conjugation cancellation: conjugating by `χ` after `χ.symm`. -/
theorem renameUndo_inv' (A : AlphaAction N X) (χ : Equiv.Perm N) (f : X → X) :
    renameUndo A χ (renameUndo A χ.symm f) = f := by
  funext z
  simp [renameUndo, AlphaAction.alpha_act_inv_right]

/-- The conjugated endomorphism of a relation-preserving map is relation-preserving
whenever the relation is alpha-invariant. -/
theorem respects_renameUndo (A : AlphaAction N X) (R : RelSpec X)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (undo : X → X) (hundo : Respects R undo) :
    Respects R (renameUndo A χ undo) := by
  intro x y hxy
  have hxy' : R.rel (A.act χ.symm x) (A.act χ.symm y) :=
    (hinv χ.symm x y).1 hxy
  have hu := hundo hxy'
  exact (hinv χ _ _).1 hu

/-- Pointwise agreement of maps transports through conjugation under `AlphaInvariant`. -/
theorem pointwise_renameUndo (A : AlphaAction N X) (R : RelSpec X)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    {f g : X → X} (hfg : PointwiseRel R f g) :
    PointwiseRel R (renameUndo A χ f) (renameUndo A χ g) := by
  intro z
  have hz : R.rel (f (A.act χ.symm z)) (g (A.act χ.symm z)) := hfg (A.act χ.symm z)
  exact (hinv χ _ _).1 hz

end ActionCore

/-! ### Actions on the result carriers -/

section ResultActions

variable {N : Type u} {S E Q : Type v}

/-- Rename one successful effect application: the state by the action, the selected
inverse by conjugation. -/
def renameEffectResult (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) : EffectResult S :=
  { state := A.act χ result.state, undo := renameUndo A χ result.undo }

/-- Rename a failing run: the neutral error is left unchanged, the boundary state is
acted upon, and the prefix undo is conjugated. -/
def renameFailure (A : AlphaAction N S) (χ : Equiv.Perm N)
    (failure : Failure S E) : Failure S E :=
  { error := failure.error
    boundary := A.act χ failure.boundary
    prefixUndo := renameUndo A χ failure.prefixUndo }

/-- The tag-preserving action on the execution carrier: constructor tags are never
mixed, and the success/failure payloads are renamed componentwise. -/
def renameExec (A : AlphaAction N S) (χ : Equiv.Perm N) :
    ExecResult S E → ExecResult S E
  | .success result => .success (renameEffectResult A χ result)
  | .failure failure => .failure (renameFailure A χ failure)

/-- The tag-preserving action on the stage carrier: a `raise` stage carries the
unchanged neutral error and acquires no fabricated state or undo. -/
def renameStage (A : AlphaAction N S) (χ : Equiv.Perm N) :
    StageResult S E Q → StageResult S E Q
  | .halt result => .halt (renameEffectResult A χ result)
  | .yield result next => .yield (renameEffectResult A χ result) next
  | .raise error => .raise error

/-! #### Rewriting equations -/

/-- The state projection of a renamed effect result. -/
theorem renameEffectResult_state (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) :
    (renameEffectResult A χ result).state = A.act χ result.state := rfl

/-- The undo projection of a renamed effect result. -/
theorem renameEffectResult_undo (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) :
    (renameEffectResult A χ result).undo = renameUndo A χ result.undo := rfl

/-- The error of a renamed failure is exactly the neutral error. -/
theorem renameFailure_error (A : AlphaAction N S) (χ : Equiv.Perm N)
    (failure : Failure S E) :
    (renameFailure A χ failure).error = failure.error := rfl

/-- The boundary of a renamed failure is the acted boundary. -/
theorem renameFailure_boundary (A : AlphaAction N S) (χ : Equiv.Perm N)
    (failure : Failure S E) :
    (renameFailure A χ failure).boundary = A.act χ failure.boundary := rfl

/-- The prefix undo of a renamed failure is the conjugated prefix undo. -/
theorem renameFailure_prefixUndo (A : AlphaAction N S) (χ : Equiv.Perm N)
    (failure : Failure S E) :
    (renameFailure A χ failure).prefixUndo = renameUndo A χ failure.prefixUndo := rfl

/-- A renamed success stays a success with the renamed result. -/
theorem renameExec_success (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) :
    renameExec (E := E) A χ (.success result) = .success (renameEffectResult A χ result) := rfl

/-- A renamed failure stays a failure with the renamed failure payload. -/
theorem renameExec_failure (A : AlphaAction N S) (χ : Equiv.Perm N)
    (failure : Failure S E) :
    renameExec (E := E) A χ (.failure failure) = .failure (renameFailure A χ failure) := rfl

/-- A renamed halt stage stays a halt with the renamed result. -/
theorem renameStage_halt (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) :
    renameStage (E := E) (Q := Q) A χ (.halt result) =
      .halt (renameEffectResult A χ result) := rfl

/-- A renamed yield stage stays a yield with the renamed result and the unchanged
neutral continuation. -/
theorem renameStage_yield (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) (next : Q) :
    renameStage (E := E) (Q := Q) A χ (.yield result next) =
      .yield (renameEffectResult A χ result) next := rfl

/-- A `raise` stage is unchanged: the neutral error carries no name and no state. -/
theorem renameStage_raise (A : AlphaAction N S) (χ : Equiv.Perm N) (error : E) :
    renameStage (E := E) (Q := Q) A χ (.raise error) = .raise error := rfl

/-! #### Action laws -/

/-- `renameEffectResult` satisfies the identity law. -/
theorem renameEffectResult_id (A : AlphaAction N S) (result : EffectResult S) :
    renameEffectResult A (Equiv.refl N) result = result := by
  cases result
  simp [renameEffectResult, A.act_id, renameUndo_id]

/-- `renameEffectResult` satisfies the composition law. -/
theorem renameEffectResult_comp (A : AlphaAction N S) (χ ψ : Equiv.Perm N)
    (result : EffectResult S) :
    renameEffectResult A (χ * ψ) result =
      renameEffectResult A χ (renameEffectResult A ψ result) := by
  cases result
  simp [renameEffectResult, A.act_comp, renameUndo_comp_perm]

/-- `renameEffectResult` satisfies the inverse/cancellation law. -/
theorem renameEffectResult_inv (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : EffectResult S) :
    renameEffectResult A χ.symm (renameEffectResult A χ result) = result := by
  cases result
  simp [renameEffectResult, A.act_inv, renameUndo_inv]

/-- `renameFailure` satisfies the identity law. -/
theorem renameFailure_id (A : AlphaAction N S) (failure : Failure S E) :
    renameFailure A (Equiv.refl N) failure = failure := by
  cases failure
  simp [renameFailure, A.act_id, renameUndo_id]

/-- `renameFailure` satisfies the composition law. -/
theorem renameFailure_comp (A : AlphaAction N S) (χ ψ : Equiv.Perm N)
    (failure : Failure S E) :
    renameFailure A (χ * ψ) failure =
      renameFailure A χ (renameFailure A ψ failure) := by
  cases failure
  simp [renameFailure, A.act_comp, renameUndo_comp_perm]

/-- `renameFailure` satisfies the inverse/cancellation law. -/
theorem renameFailure_inv (A : AlphaAction N S) (χ : Equiv.Perm N)
    (failure : Failure S E) :
    renameFailure A χ.symm (renameFailure A χ failure) = failure := by
  cases failure
  simp [renameFailure, A.act_inv, renameUndo_inv]

/-- `renameExec` satisfies the identity law. -/
theorem renameExec_id (A : AlphaAction N S) (result : ExecResult S E) :
    renameExec A (Equiv.refl N) result = result := by
  cases result with
  | success r => simp [renameExec, renameEffectResult_id]
  | failure f => simp [renameExec, renameFailure_id]

/-- `renameExec` satisfies the composition law. -/
theorem renameExec_comp (A : AlphaAction N S) (χ ψ : Equiv.Perm N)
    (result : ExecResult S E) :
    renameExec A (χ * ψ) result = renameExec A χ (renameExec A ψ result) := by
  cases result with
  | success r => simp [renameExec, renameEffectResult_comp]
  | failure f => simp [renameExec, renameFailure_comp]

/-- `renameExec` satisfies the inverse/cancellation law. -/
theorem renameExec_inv (A : AlphaAction N S) (χ : Equiv.Perm N)
    (result : ExecResult S E) :
    renameExec A χ.symm (renameExec A χ result) = result := by
  cases result with
  | success r => simp [renameExec, renameEffectResult_inv]
  | failure f => simp [renameExec, renameFailure_inv]

/-- `renameStage` satisfies the identity law. -/
theorem renameStage_id (A : AlphaAction N S) (stage : StageResult S E Q) :
    renameStage A (Equiv.refl N) stage = stage := by
  cases stage with
  | halt r => simp [renameStage, renameEffectResult_id]
  | yield r q => simp [renameStage, renameEffectResult_id]
  | raise e => rfl

/-- `renameStage` satisfies the composition law. -/
theorem renameStage_comp (A : AlphaAction N S) (χ ψ : Equiv.Perm N)
    (stage : StageResult S E Q) :
    renameStage A (χ * ψ) stage = renameStage A χ (renameStage A ψ stage) := by
  cases stage with
  | halt r => simp [renameStage, renameEffectResult_comp]
  | yield r q => simp [renameStage, renameEffectResult_comp]
  | raise e => rfl

/-- `renameStage` satisfies the inverse/cancellation law. -/
theorem renameStage_inv (A : AlphaAction N S) (χ : Equiv.Perm N)
    (stage : StageResult S E Q) :
    renameStage A χ.symm (renameStage A χ stage) = stage := by
  cases stage with
  | halt r => simp [renameStage, renameEffectResult_inv]
  | yield r q => simp [renameStage, renameEffectResult_inv]
  | raise e => rfl

end ResultActions

end

end STC
