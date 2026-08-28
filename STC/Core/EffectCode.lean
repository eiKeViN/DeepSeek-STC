import STC.Core.Effect

universe u v

namespace STC

variable {EffectCode : Type u} {S : Type v}

/-! A deliberately type-parametric shallow/deep boundary.

`EffectCode` is supplied by a later language layer.  This module therefore contains
only interfaces: it does not choose a syntax, evaluator, or runtime state. -/

structure EffectInterpreter (EffectCode : Type u) (S : Type v) where
  interpret : EffectCode → Effect S

structure ShallowDeepRefinementSeam
    (R : RelSpec S)
    (interpreter : EffectInterpreter EffectCode S)
    (code : EffectCode)
    (shallow : Effect S) : Prop where
  run_related : ∀ input,
    EffectResultRel R (interpreter.interpret code input) (shallow input)

structure InterpreterLawful
    (R : RelSpec S)
    (interpreter : EffectInterpreter EffectCode S) : Prop where
  lawful : ∀ code, IsLawfulEffect R (interpreter.interpret code)

end STC
