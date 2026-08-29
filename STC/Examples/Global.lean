module

public import STC.Conformance.Global
public import STC.Examples.GlobalAlpha
public import STC.Examples.GlobalConfluence
public import STC.Examples.GlobalDeletion
public import STC.Examples.GlobalModel
public import STC.Examples.GlobalProgress
public import STC.Examples.GlobalRecovery
public import STC.Examples.GlobalRules
public import STC.Examples.GlobalStructural
public import STC.Examples.PrerequisiteCoeffect
public import STC.Examples.PrerequisiteRecovery
public import STC.Examples.PrerequisiteState
public import STC.Examples.SupportCycle

/-!
# P13 finite evidence umbrella
-/

namespace STC.Examples.Global

open STC STC.Conformance

@[expose] public section

def evidenceCount : Nat := p13Entries.length

theorem evidenceCount_nonzero : evidenceCount > 0 := by decide

def p13Report : Manifest := globalManifestShape

end

end STC.Examples.Global
