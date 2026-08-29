module

public import STC.Control.Preservation

/-!
# Structural-lane evidence
-/

namespace STC.Examples.GlobalStructural

open STC STC.Control

@[expose] public section

def entry : Table1Entry := table1For "finish" "lifecycle"

theorem entry_case : entry.paperCase = "lifecycle" := rfl

end

end STC.Examples.GlobalStructural
