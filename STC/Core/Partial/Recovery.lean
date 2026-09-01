module

public import Mathlib.Data.List.Perm.Basic
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

/-! ### C21: arbitrary-order recovery -/

section ArbitraryOrder

variable {S : Type u}

/-- The selected-inverse word of a run: the inverses in execution order. -/
def inverseWord (effects : List (Effect S)) (input : S) : List (S → S) :=
  match effects with
  | [] => []
  | e :: rest => (e input).undo :: inverseWord rest ((e input).state)

/-- Apply a word of maps left-to-right. -/
def applyWord (maps : List (S → S)) (s : S) : S :=
  match maps with
  | [] => s
  | m :: rest => applyWord rest (m s)

/-- Appending words applies the first word then the second. -/
theorem applyWord_append (maps₁ maps₂ : List (S → S)) (s : S) :
    applyWord (maps₁ ++ maps₂) s = applyWord maps₂ (applyWord maps₁ s) := by
  induction maps₁ generalizing s with
  | nil => rfl
  | cons m rest ih => simp [applyWord, ih]

/-- Applying a word of relation-preserving maps preserves the relation. -/
theorem applyWord_respects (R : RelSpec S) (maps : List (S → S))
    (h : ∀ m ∈ maps, Respects R m) : Respects R (applyWord maps) := by
  intro s t hst
  induction maps generalizing s t with
  | nil => exact hst
  | cons m rest ih =>
      exact ih (fun m' hm' => h m' (by simp [hm'])) ((h m (by simp)) hst)

/-- The `runSequence` undo is exactly the reverse-order application of the inverse word. -/
theorem runSequence_undo_eq_applyWord_reverse (effects : List (Effect S)) (input : S) :
    (runSequence effects input).undo =
      fun s => applyWord (inverseWord effects input).reverse s := by
  induction effects generalizing input with
  | nil => simp [runSequence, inverseWord, applyWord, identityEffect]; rfl
  | cons e rest ih =>
      rw [runSequence]
      funext s
      change (e input).undo ((runSequence rest (e input).state).undo s) =
        applyWord (((e input).undo :: inverseWord rest ((e input).state)).reverse) s
      simp_rw [List.reverse_cons, applyWord_append, ih, applyWord]

/-- The bundle of per-map laws consumed by permuted inverse application. -/
structure InverseWordLaw (R : RelSpec S) (maps : List (S → S)) : Prop where
  respects : ∀ (m : S → S), m ∈ maps → Respects R m
  commutes : ∀ {m m' : S → S}, m ∈ maps → m' ∈ maps → CrossRel R (m ∘ m') (m' ∘ m)

namespace InverseWordLaw

/-- Restrict the law bundle to a sublist. -/
theorem restrict {R : RelSpec S} {maps : List (S → S)} (hlaw : InverseWordLaw R maps)
    {l : List (S → S)} (hsub : l ⊆ maps) :
    InverseWordLaw R l where
  respects := fun (m : S → S) (hm : m ∈ l) => hlaw.respects m (hsub hm)
  commutes := fun {m m' : S → S} (hm : m ∈ l) (hm' : m' ∈ l) =>
    hlaw.commutes (hsub hm) (hsub hm')

end InverseWordLaw

/-- Applying the same word of inverses in two permuted orders yields related states,
provided every map respects the relation and adjacent inverses commute. -/
theorem applyWord_perm_rel (R : RelSpec S) (maps : List (S → S))
    {perm : List (S → S)} (hperm : List.Perm perm maps)
    (hlaw : InverseWordLaw R maps) (s : S) :
    R.rel (applyWord perm s) (applyWord maps s) := by
  induction hperm generalizing s with
  | nil => exact R.refl s
  | cons m h₁₂ ih =>
      exact ih (hlaw.restrict (by intro m' hm'; simp [hm'])) (m s)
  | swap x y l =>
      have hxy : R.rel (x (y s)) (y (x s)) :=
        (hlaw.commutes (by simp) (by simp)) (R.refl s)
      have hl : ∀ m ∈ l, Respects R m := fun m hm => hlaw.respects m (by simp [hm])
      exact (applyWord_respects R l hl) hxy
  | trans h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact R.trans
        (ih₁₂ (hlaw.restrict h₂₃.subset) s)
        (ih₂₃ hlaw s)

/-- Every inverse in the inverse word respects the relation. -/
theorem inverseWord_respects (R : RelSpec S) (effects : List (Effect S))
    (hlawful : ∀ e ∈ effects, IsLawfulEffect R e) (input : S) :
    ∀ (m : S → S), m ∈ inverseWord effects input → Respects R m := by
  intro m hm
  induction effects generalizing input with
  | nil => cases hm
  | cons e rest ih =>
      simp [inverseWord] at hm
      rcases hm with rfl | hm'
      · exact (hlawful e (by simp)).undo_respects input
      · exact ih (fun (e' : Effect S) (he' : e' ∈ rest) => hlawful e' (by simp [he']))
          (e input).state hm'

/-- C21: under pairwise inverse commutation, the selected inverses of a run of lawful
effects may be applied in any permutation and still recover the input.

The inverse-commutation premise is explicit and audited at core removal strength:
the selection-stable derivation that lifts it from an independence contract belongs
to T05B/T05E. -/
theorem arbitrary_order_recovery (R : RelSpec S) (effects : List (Effect S))
    (hlawful : ∀ e ∈ effects, IsLawfulEffect R e)
    (input : S)
    (hcomm : ∀ {g h : S → S}, g ∈ inverseWord effects input → h ∈ inverseWord effects input →
      CrossRel R (g ∘ h) (h ∘ g))
    {perm : List (S → S)}
    (hperm : List.Perm perm (inverseWord effects input).reverse) :
    R.rel (applyWord perm (runSequence effects input).state) input := by
  have hbase : R.rel (applyWord (inverseWord effects input).reverse
      (runSequence effects input).state) input := by
    simpa [runSequence_undo_eq_applyWord_reverse effects input] using
      (runSequence_lawful R effects hlawful).recovers input
  have hresp := inverseWord_respects R effects hlawful input
  have hrel : R.rel (applyWord perm (runSequence effects input).state)
      (applyWord (inverseWord effects input).reverse (runSequence effects input).state) :=
    applyWord_perm_rel R (inverseWord effects input).reverse hperm
      { respects :=
          fun (m : S → S) (hm : m ∈ (inverseWord effects input).reverse) =>
            hresp m (List.mem_reverse.mp hm)
        commutes :=
          fun {m m' : S → S} (hm : m ∈ (inverseWord effects input).reverse)
            (hm' : m' ∈ (inverseWord effects input).reverse) =>
            hcomm (List.mem_reverse.mp hm) (List.mem_reverse.mp hm') }
      (runSequence effects input).state
  exact R.trans hrel hbase

end ArbitraryOrder

end

end STC
