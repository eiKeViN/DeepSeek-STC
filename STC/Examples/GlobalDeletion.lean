module

public import STC.Control.Deletion

/-!
# Closed-episode deletion evidence
-/

namespace STC.Examples.GlobalDeletion

open STC STC.Control

@[expose] public section

def envelope : DeletionEnvelope Nat Nat where
  reachable := fun _ => True
  wellFormed := fun _ => True
  closedEpisode := fun _ => True
  recovery := fun _ _ => True
  continuationIndependent := fun _ _ => True
  noRegisteredChildren := fun _ => True
  totalProvision := fun _ => True
  quiescent := fun _ => True
  structural := fun _ => True

end

end STC.Examples.GlobalDeletion
