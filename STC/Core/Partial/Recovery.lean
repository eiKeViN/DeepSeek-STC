module

public import STC.Core.Partial

/-!
# Partial recovery contracts

The theorem-level recovery API keeps mathematical undefinedness, failure
diagnostics, inverse recovery, and foreign continuation stability separate.
-/

universe u v

namespace STC

@[expose] public section

section Recovery

variable {S : Type u} {A : Type v}

/-- A partial operation together with all local laws needed for recovery. -/
structure RecoverySpec (R : RelSpec S) (O : A → A → Prop) where
  op : PartialOp S A
  respects : OperationRespects R O op
  inverseStable : SelectedInverseStableOp R op
  recovers : OperationRecovers R op

/-- Recovery of a defined operation is related to its input. -/
theorem RecoverySpec.recovers_at (R : RelSpec S) (O : A → A → Prop)
    (spec : RecoverySpec R O)
    {input : S} {result : OpResult S A} (h : spec.op input = some result) :
    R.rel (result.undo result.state) input := spec.recovers input result h

/-- Sequential recovery with the inverse-respect premise made explicit. -/
theorem recovery_seq_of_inverse_stable (R : RelSpec S) (_O : A → A → Prop)
    {first second : PartialOp S A}
    (hf : OperationRecovers R first) (hs : OperationRecovers R second)
    (hstable : ∀ input r, first input = some r → Respects R r.undo)
    {input r s} (hr : first input = some r) (hs' : second r.state = some s) :
    R.rel ((r.undo ∘ s.undo) s.state) input := by
  have h₂ : R.rel (s.undo s.state) r.state := hs r.state s hs'
  have h₁ : R.rel (r.undo (s.undo s.state)) (r.undo r.state) :=
    hstable input r hr h₂
  exact R.trans h₁ (hf input r hr)

/-- A finite list of recovery operations is locally recoverable when each item
carries its own recovery law. -/
def ReverseRecovery (R : RelSpec S) (ops : List (PartialOp S A)) : Prop :=
  ∀ op ∈ ops, OperationRecovers R op

theorem reverseRecovery_cons (R : RelSpec S) (op : PartialOp S A)
    (ops : List (PartialOp S A)) (h : ReverseRecovery R (op :: ops)) :
    ReverseRecovery R ops := by
  intro other ho
  exact h other (by simp [ho])

theorem reverseRecovery_mem (R : RelSpec S) (ops : List (PartialOp S A))
    (h : ReverseRecovery R ops) {op : PartialOp S A} (hop : op ∈ ops) :
    OperationRecovers R op := h op hop

end Recovery

end

end STC
