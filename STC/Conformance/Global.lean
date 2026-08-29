module

public import STC.Conformance.Manifest
public import STC.Control.Canonical
public import STC.Control.Reachability
public import STC.State.Global.Observation

/-!
# P13 global conformance inventory

This checked inventory names the repaired old-paper targets and keeps evidence
dimensions distinct from acceptance and runtime refinement.
-/

namespace STC.Conformance

open STC

@[expose] public section

def p13Entries : List EvidenceEntry :=
  [ { paperId := "D43-D50", delivery := "in_progress", evidence := .interface,
      note := "positive global state and guarded-rule API; concrete frames remain open" }
  , { paperId := "D53", delivery := "in_progress", evidence := .interface,
      note := "reached traces and episode carrier; per-rule factorization remains open" }
  , { paperId := "L68", delivery := "in_progress", evidence := .kernel,
      note := "restricted support theorem plus explicit cycle profile" }
  , { paperId := "L70", delivery := "in_progress", evidence := .kernel,
      note := "active fixed-point implication remains profile-relative" }
  , { paperId := "T73", delivery := "in_progress", evidence := .kernel,
      note := "canonical/confluence contracts retain alpha and D53 boundaries" }
  , { paperId := "P12", delivery := "completed", evidence := .interface,
      note := "scoped layer remains independent; no realm-aware global theorem" }
  , { paperId := "R0", delivery := "planned", evidence := .r0,
      note := "abstract adapter seam only; Cordis R1+ is outside P13" } ]

def p13Deferred : List DeferredObligation :=
  [ { id := "D27", reason := "expository realization/refinement", evidenceBoundary := "R1+" }
  , { id := "D74", reason := "Cordis runtime refinement", evidenceBoundary := "R1+" }
  , { id := "newer-paper", reason := "version reconciliation",
      evidenceBoundary := "architecture" } ]

def globalManifestShape : Manifest :=
  { schemaVersion := "p13-v1"
    planId := "DH-P13-GLOBAL-METATHEORY-EXEC-01"
    repositoryCommit := "pending"
    repositoryBranch := "pending"
    sources := []
    entries := p13Entries
    deferred := p13Deferred }

example : EvidenceKind.r0 ≠ EvidenceKind.r1Plus := by decide

end

end STC.Conformance
