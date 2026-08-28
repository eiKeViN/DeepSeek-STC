import STC.Foundation.Relation
import STC.Foundation.Result

universe u

namespace STC

variable {S : Type u}

/-! The (deliberately shallow) reversible transformation algebra. -/

structure Transformation (S : Type u) where
  forward : S → S
  undo : S → S

namespace Transformation

def identity : Transformation S :=
  ⟨id, id⟩

/- `later` is the left paper operand; `earlier` is executed first. -/
def twisted (later earlier : Transformation S) : Transformation S :=
  ⟨later.forward ∘ earlier.forward, earlier.undo ∘ later.undo⟩

theorem twisted_identity_left (t : Transformation S) :
    twisted identity t = t := by
  cases t
  rfl

theorem twisted_identity_right (t : Transformation S) :
    twisted t identity = t := by
  cases t
  rfl

theorem twisted_assoc (a b c : Transformation S) :
    twisted (twisted a b) c = twisted a (twisted b c) := by
  cases a with
  | mk af au =>
    cases b with
    | mk bf bu =>
      cases c with
      | mk cf cu =>
        simp [twisted, Function.comp_def]

end Transformation

abbrev Undo (S : Type u) := S → S

abbrev EffectContext (S : Type u) := S × Undo S

def track (t : Transformation S) : EffectContext S → EffectContext S :=
  fun ctx => (t.forward ctx.1, ctx.2 ∘ t.undo)

def recover : EffectContext S → EffectContext S :=
  fun ctx => (ctx.2 ctx.1, id)

theorem track_state (t : Transformation S) (ctx : EffectContext S) :
    (track t ctx).1 = t.forward ctx.1 := rfl

theorem track_accumulator (t : Transformation S) (ctx : EffectContext S) :
    (track t ctx).2 = ctx.2 ∘ t.undo := rfl

theorem track_twisted (later earlier : Transformation S) :
    track (Transformation.twisted later earlier) = track later ∘ track earlier := by
  funext ctx
  apply Prod.ext
  · rfl
  · funext x
    rfl

theorem recover_state (ctx : EffectContext S) :
    (recover ctx).1 = ctx.2 ctx.1 := rfl

theorem recover_accumulator (ctx : EffectContext S) :
    (recover ctx).2 = id := rfl

abbrev Effect (S : Type u) := S → EffectResult S

theorem effectResult_ext {x y : EffectResult S}
    (hstate : x.state = y.state) (hundo : x.undo = y.undo) : x = y := by
  cases x
  cases y
  simp_all

def identityEffect : Effect S :=
  fun state => { state := state, undo := id }

def seqRun (first second : Effect S) : Effect S :=
  fun input =>
    let rFirst := first input
    let rSecond := second rFirst.state
    { state := rSecond.state
      undo := rFirst.undo ∘ rSecond.undo }

def effectForward (e : Effect S) : S → S :=
  fun input => (e input).state

def uniformEffect (t : Transformation S) : Effect S :=
  fun input => { state := t.forward input, undo := t.undo }

theorem identityEffect_state (input : S) :
    (identityEffect input).state = input := rfl

theorem identityEffect_undo (input : S) :
    (identityEffect input).undo = id := rfl

theorem seqRun_state (first second : Effect S) (input : S) :
    (seqRun first second input).state = (second (first input).state).state := rfl

theorem seqRun_undo (first second : Effect S) (input : S) :
    (seqRun first second input).undo = (first input).undo ∘ (second (first input).state).undo := rfl

theorem seqRun_identity_left (e : Effect S) :
    seqRun identityEffect e = e := by
  funext input
  apply effectResult_ext
  · rfl
  · funext x
    rfl

theorem seqRun_identity_right (e : Effect S) :
    seqRun e identityEffect = e := by
  funext input
  apply effectResult_ext
  · rfl
  · funext x
    rfl

theorem seqRun_assoc (a b c : Effect S) :
    seqRun (seqRun a b) c = seqRun a (seqRun b c) := by
  funext input
  apply effectResult_ext
  · rfl
  · funext x
    rfl

theorem seqRun_uniformEffect (later earlier : Transformation S) :
    seqRun (uniformEffect earlier) (uniformEffect later) =
      uniformEffect (Transformation.twisted later earlier) := by
  funext input
  apply effectResult_ext
  · rfl
  · funext x
    rfl

structure IsLawfulEffect (R : RelSpec S) (e : Effect S) : Prop where
  run_respects : RespectsOn R.rel (EffectResultRel R) e
  undo_respects : ∀ input, Respects R (e input).undo
  recovers : ∀ input, R.rel ((e input).undo (e input).state) input

structure LawfulEffect (R : RelSpec S) where
  run : Effect S
  lawful : IsLawfulEffect R run

theorem identityEffect_lawful (R : RelSpec S) :
    IsLawfulEffect R (identityEffect : Effect S) := by
  constructor
  · intro x y hxy
    exact ⟨hxy, pointwiseRel_refl R id⟩
  · intro input
    exact respects_id R
  · intro input
    exact R.refl input

theorem uniformEffect_lawful (R : RelSpec S) (t : Transformation S)
    (hforward : Respects R t.forward) (hundo : Respects R t.undo)
    (hrecovers : ∀ input, R.rel (t.undo (t.forward input)) input) :
    IsLawfulEffect R (uniformEffect t) := by
  constructor
  · intro x y hxy
    exact ⟨hforward hxy, pointwiseRel_refl R t.undo⟩
  · intro input
    exact hundo
  · intro input
    exact hrecovers input

theorem seqRun_lawful (R : RelSpec S) {first second : Effect S}
    (hfirst : IsLawfulEffect R first)
    (hsecond : IsLawfulEffect R second) :
    IsLawfulEffect R (seqRun first second) := by
  constructor
  · intro x y hxy
    let firstX := first x
    let firstY := first y
    let secondX := second firstX.state
    let secondY := second firstY.state
    have hfirstRun : EffectResultRel R firstX firstY := hfirst.run_respects hxy
    have hsecondRun : EffectResultRel R secondX secondY :=
      hsecond.run_respects hfirstRun.1
    have hundo : PointwiseRel R
        (firstX.undo ∘ secondX.undo)
        (firstY.undo ∘ secondY.undo) :=
      compose_pointwiseRel (hfirst.undo_respects x) hfirstRun.2 hsecondRun.2
    exact ⟨hsecondRun.1, hundo⟩
  · intro input
    exact respects_comp (hfirst.undo_respects input)
      (hsecond.undo_respects (first input).state)
  · intro input
    let firstResult := first input
    let secondResult := second firstResult.state
    have hlater : R.rel (secondResult.undo secondResult.state) firstResult.state :=
      hsecond.recovers firstResult.state
    have hearlier : R.rel
        (firstResult.undo (secondResult.undo secondResult.state))
        (firstResult.undo firstResult.state) :=
      hfirst.undo_respects input hlater
    exact R.trans hearlier (hfirst.recovers input)

theorem seqRun_recovers (R : RelSpec S) {first second : Effect S}
    (hfirst : IsLawfulEffect R first) (hsecond : IsLawfulEffect R second)
    (input : S) :
    R.rel ((seqRun first second input).undo (seqRun first second input).state) input :=
  (seqRun_lawful R hfirst hsecond).recovers input

def runSequence : List (Effect S) → Effect S
  | [] => identityEffect
  | first :: rest => seqRun first (runSequence rest)

theorem runSequence_lawful (R : RelSpec S) (effects : List (Effect S))
    (h : ∀ e ∈ effects, IsLawfulEffect R e) :
    IsLawfulEffect R (runSequence effects) := by
  induction effects with
  | nil => simpa [runSequence] using identityEffect_lawful R
  | cons first rest ih =>
    rw [runSequence]
    apply seqRun_lawful R
    · exact h first (by simp)
    · apply ih
      intro e he
      exact h e (by simp [he])

theorem runSequence_recovers (R : RelSpec S) (effects : List (Effect S))
    (h : ∀ e ∈ effects, IsLawfulEffect R e) (input : S) :
    R.rel ((runSequence effects input).undo (runSequence effects input).state) input :=
  (runSequence_lawful R effects h).recovers input

theorem lawful_equality_iff (e : Effect S) :
    IsLawfulEffect (equality S) e ↔
      ∀ input, (e input).undo (e input).state = input := by
  constructor
  · intro h input
    exact h.recovers input
  · intro h
    constructor
    · intro x y hxy
      cases hxy
      exact ⟨rfl, pointwiseRel_refl (equality S) (e x).undo⟩
    · intro input
      intro x y hxy
      cases hxy
      rfl
    · intro input
      exact h input

theorem recover_track_rel (R : RelSpec S) (t : Transformation S)
    (ctx : EffectContext S) (hacc : Respects R ctx.2)
    (hlocal : R.rel (t.undo (t.forward ctx.1)) ctx.1) :
    R.rel (recover (track t ctx)).1 (recover ctx).1 := by
  exact hacc hlocal

def liftEffect (e : Effect S) : Effect (EffectContext S) :=
  fun ctx =>
    let result := e ctx.1
    { state := (result.state, ctx.2 ∘ result.undo)
      undo := track
        { forward := result.undo
          undo := effectForward e } }

theorem liftEffect_state_projection (e : Effect S) (ctx : EffectContext S) :
    (liftEffect e ctx).state.1 = (e ctx.1).state := rfl

theorem liftEffect_undo_projection (e : Effect S) (ctx : EffectContext S)
    (x : EffectContext S) :
    (liftEffect e ctx).undo x =
      ((e ctx.1).undo x.1, x.2 ∘ effectForward e) := rfl

theorem liftEffect_seqRun (first second : Effect S) :
    liftEffect (seqRun first second) =
      seqRun (liftEffect first) (liftEffect second) := by
  funext ctx
  apply effectResult_ext
  · rfl
  · funext x
    apply Prod.ext
    · rfl
    · funext z
      rfl

theorem liftEffect_undo_apply (e : Effect S) (ctx : EffectContext S) :
    (liftEffect e ctx).undo (liftEffect e ctx).state =
      ((e ctx.1).undo (e ctx.1).state,
        (ctx.2 ∘ (e ctx.1).undo) ∘ effectForward e) := by
  rfl

theorem liftEffect_recovers_state (R : RelSpec S) (e : Effect S)
    (ctx : EffectContext S)
    (hlocal : R.rel ((e ctx.1).undo (e ctx.1).state) ctx.1) :
    R.rel ((liftEffect e ctx).undo (liftEffect e ctx).state).1 ctx.1 := by
  exact hlocal

theorem liftEffect_preserves_recovery_target (R : RelSpec S) (e : Effect S)
    (ctx : EffectContext S) (hacc : Respects R ctx.2)
    (hf : Respects R (effectForward e))
    (hg : Respects R (e ctx.1).undo)
    (hlocal : R.rel ((e ctx.1).undo (e ctx.1).state) ctx.1) :
    R.rel
      (((liftEffect e ctx).undo (liftEffect e ctx).state).2
        (((liftEffect e ctx).undo (liftEffect e ctx).state).1))
      (ctx.2 ctx.1) := by
  let result := e ctx.1
  let g := result.undo
  let f := effectForward e
  have hgf : R.rel (g (f (g result.state))) (g result.state) := by
    exact hg (hf hlocal)
  have hstate : R.rel (g (f (g result.state))) ctx.1 :=
    R.trans hgf hlocal
  exact hacc hstate

theorem liftEffect_lawful_equality_iff (e : Effect S) :
    IsLawfulEffect (equality (EffectContext S)) (liftEffect e) ↔
      ∀ input, (e input).undo ∘ effectForward e = id := by
  constructor
  · intro h input
    have hr := h.recovers (input, id)
    have hfun : (e input).undo ∘ effectForward e = id := by
      simpa [liftEffect, track, Function.comp_def] using congrArg Prod.snd hr
    exact hfun
  · intro h
    constructor
    · intro x y hxy
      cases hxy
      exact ⟨rfl, pointwiseRel_refl (equality (EffectContext S))
        (liftEffect e x).undo⟩
    · intro input
      intro x y hxy
      cases hxy
      rfl
    · intro input
      have hf := h input.1
      apply Prod.ext
      · exact congrFun hf input.1
      · funext z
        simp only [liftEffect, track]
        exact congrArg input.2 (congrFun hf z)

end STC
