module

public import STC.Core.Effect

/-!
# The shallow/deep effect-code seam

A deliberately type-parametric shallow/deep boundary.  `EffectCode` is supplied by a later
language layer, so this module contains only interfaces: it does not choose a syntax,
evaluator, or runtime state.

## Main declarations

* `EffectInterpreter`: interprets effect codes into the shallow `Effect` kernel;
* `ShallowDeepRefinementSeam`: code and shallow effect agree up to the selected relation;
* `InterpreterLawful`: every interpreted code denotes a lawful effect.
-/

universe u v

namespace STC

variable {EffectCode : Type u} {S : Type v}

@[expose] public section

section InterpreterSeam

/-- An interpreter for the shallow effect kernel over a type-parametric code carrier. -/
structure EffectInterpreter (EffectCode : Type u) (S : Type v) where
  interpret : EffectCode → Effect S

/-- The R0 refinement seam: an interpreted code and its shallow counterpart produce
related results on every input. -/
structure ShallowDeepRefinementSeam
    (R : RelSpec S)
    (interpreter : EffectInterpreter EffectCode S)
    (code : EffectCode)
    (shallow : Effect S) : Prop where
  run_related : ∀ input,
    EffectResultRel R (interpreter.interpret code input) (shallow input)

/-- An interpreter is lawful when every code it interprets denotes a lawful effect. -/
structure InterpreterLawful
    (R : RelSpec S)
    (interpreter : EffectInterpreter EffectCode S) : Prop where
  lawful : ∀ code, IsLawfulEffect R (interpreter.interpret code)

end InterpreterSeam

end

end STC
