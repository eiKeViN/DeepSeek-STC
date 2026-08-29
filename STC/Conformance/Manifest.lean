module

public import STC.Foundation.Relation

/-!
# Conformance and readiness manifest schema

This module defines the typed Lean vocabulary used by the derived P8
conformance manifest.  The JSON report is generated from frozen H03/H04
provenance and the current Definition Ledger; these declarations deliberately
do not turn a status label into a proof or an architecture acceptance record.

## Main declarations

* `EvidenceKind`: the distinct alignment, interface, kernel, executable, R0,
  and R1+ evidence classes;
* `EvidenceEntry`: one paper/auxiliary row with its delivery and evidence
  labels;
* `Manifest`: the typed shape of a derived report, including source records,
  rows, and deferred obligations.
-/

universe u

namespace STC.Conformance

@[expose] public section

/-! ### Evidence vocabulary -/

section Evidence

/-- Evidence classes remain distinct: a compiler result is not a proof or a refinement. -/
inductive EvidenceKind where
  | alignment
  | interface
  | kernel
  | executable
  | r0
  | r1Plus
deriving DecidableEq, Repr

/-- Stable text spelling used by derived reports and tooling. -/
def EvidenceKind.label : EvidenceKind → String
  | .alignment => "A"
  | .interface => "I"
  | .kernel => "K"
  | .executable => "E"
  | .r0 => "R0"
  | .r1Plus => "R1+"

/-- One traceability row in a conformance report. -/
structure EvidenceEntry where
  paperId : String
  delivery : String
  evidence : EvidenceKind
  note : String
deriving Repr

end Evidence

/-! ### Derived manifest records -/

section ManifestRecords

/-- A source artifact and its byte hash. -/
structure SourceRecord where
  id : String
  path : String
  sha256 : String
deriving Repr

/-- A blocker retained as a first-class deferred obligation. -/
structure DeferredObligation where
  id : String
  reason : String
  evidenceBoundary : String
deriving Repr

/-- Typed in-memory shape of the generated conformance/readiness report. -/
structure Manifest where
  schemaVersion : String
  planId : String
  repositoryCommit : String
  repositoryBranch : String
  sources : List SourceRecord
  entries : List EvidenceEntry
  deferred : List DeferredObligation
deriving Repr

end ManifestRecords

/-! ### Sanity checks -/

section Checks

/-- Distinct evidence tags cannot be confused by the manifest schema. -/
example : EvidenceKind.kernel ≠ EvidenceKind.interface := by decide

/-- The text spelling of R0 remains separate from R1+. -/
example : EvidenceKind.r0.label ≠ EvidenceKind.r1Plus.label := by decide

end Checks

end

end STC.Conformance
