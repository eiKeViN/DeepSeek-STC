# STC Metatheory: P7–P8 Combined Execution Plan

| Field | Value |
|---|---|
| Plan ID | DH-P7-P8-EXEC-01 |
| Repository | https://github.com/eiKeViN/DeepSeek-STC |
| Prepared | 2026-08-28 |
| Planning baseline | origin/main at a72e3d7; execution starts from the post-P6 merge |
| Blueprint | DH-FORMAL-BP-01, v1.0.2 |
| Scope | complete the finite TwoCounter vertical slice, then publish conformance/readiness evidence and the R0 adapter seam |
| Ownership | one agent, sequentially: P7 must pass before P8 starts |
| Prerequisite | P6 alpha-transport handoff and integration gate |
| Namespace | STC; adapter declarations under STC.Adapter |
| Status | ready to schedule after P6 |

This is one deferred batch. It is planned now so that the post-P6 agent can
execute P7 and P8 without reopening the architecture or inventing an intermediate
API. P7 consumes the production alpha transport and completes the first
end-to-end finite example. P8 consumes that evidence and records exactly what the
package does and does not establish.

The batch does not claim a complete Section 4 lifecycle/control proof, a
support/confluence theorem, scoped-realm semantics, or verification of the
TypeScript Cordis runtime.

## 1. Authority and evidence policy

The paper is authoritative for literal source claims. The Formal Reference and
H03/H04 are frozen provenance/disposition records. Accepted ADR-01 through
ADR-06-CLOSURE are normative for the repaired target; the later ADR-07–10
packets currently describe proposed architecture/interface closures and are not
automatically compiler-validated or semantically accepted. The Lean kernel
validates elaborated declarations and proof terms, while compilation alone is
interface evidence.

Evidence labels remain separate:

- A — paper/ADR alignment and interpretation;
- I — interface/elaboration;
- K — checked kernel proof;
- E — finite executable evidence;
- R0 — explicit abstraction/refinement seam;
- R1+ — concrete runtime simulation/refinement.

P7 finite theorems are not Cordis theorems. P8 documentation must not turn
I/K/E into R1+.

## 2. Batch entry and preflight

P7/P8 must start only after P6 has passed its handoff gate and its public alpha
API is present on the branch selected for integration.

~~~bash
git fetch origin --prune
git switch -c <p7-p8-branch> origin/main
git status --short --branch
git log -1 --oneline
~~~

The branch must be based on the commit that contains the accepted P6 production
files, not merely on the planning commit. Record both the P6 handoff commit and
the actual branch base in the P7 report.

Read without modifying:

~~~text
AGENTS.md
README.md
lean-toolchain
lakefile.toml
lake-manifest.json
STC.lean
STC/Bootstrap.lean
STC/Foundation/Relation.lean
STC/Foundation/Result.lean
STC/Core/Effect.lean
STC/Core/Partial.lean
STC/Core/Iterator.lean
STC/State/Like.lean
STC/State/Observation.lean
STC/State/RegistryLike.lean
STC/State/FinmapAdapter.lean
STC/Alpha/Core.lean
STC/Alpha/Transport.lean
STC/Examples/TwoCounter.lean
STC/Examples/VerticalSlice.lean
STC/Examples/Alpha.lean
STC/Conformance/Manifest.lean (if already present)
STC/Adapter.lean (if already present)
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-05-ADR-01-Equivalence-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-06-ADR-02-Coeffect-Store-and-Partiality-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-08-ADR-04-Incarnation-Identity-and-Alpha-Equivariance-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-09-ADR-05-Iterator-and-Failure-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-10-ADR-06-Equivalence-and-Equivariance-Closure.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-12-ADR-07-Control-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.json
docs/status/P0-baseline.json
docs/status/P3-handoff-report.md
docs/status/P4-handoff-report.md
docs/status/P5-handoff-report.md
docs/status/P6-handoff-report.md
docs/status/Definition-Ledger.json
~~~

The Project Guide and Research Ledger remain historical/context sources and
must not become Lean dependencies. Historical ADR spikes are read-only
compiler mirrors.

Run the preflight gate:

~~~bash
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
~~~

The scanner contract is exit 1 = clean, exit 0 = lexical match requiring
inspection, and exit 2 = scan error. If Lean/Lake is unavailable, record the
gate as blocked; do not promote evidence.

## 3. Existing staged work and ownership

The current main tree already contains finite P3/P4 material:

- STC/Examples/TwoCounter.lean defines CounterState, inc1, inc2, dec1,
  failIfZero, local lawfulness/independence evidence, and a finite failure
  report.
- STC/Examples/VerticalSlice.lean defines the success and failing ranked
  iterators, rank certificates, equation-pinned traces, prefix recovery, and a
  finite slice report.
- The files deliberately say that a later P7 owner may extend them.

Treat these declarations and theorem statements as stable bytes. P7 is an
additive completion/integration wave: do not redeclare the same names, replace
the P4 rank machine, or erase existing finite evidence. The current ledger may
still show pre-integration P3/P4/P5 statuses; P8-T01 reconciles derived status
records after reviewing the actual merged evidence.

P7 owns:

~~~text
STC/Examples/TwoCounter.lean
STC/Examples/VerticalSlice.lean
docs/status/P7-scan-raw.txt
docs/status/P7-handoff-report.md
~~~

P8 owns:

~~~text
STC/Conformance/Manifest.lean
STC/Adapter.lean
docs/status/P8-conformance-manifest.json
docs/status/P8-deferred-obligations.md
docs/status/P8-feedback-log.md
docs/status/P8-scan-raw.txt
docs/status/P8-handoff-report.md
~~~

The following remain integration-owned and must not be edited opportunistically
by the batch agent:

~~~text
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
~~~

The integration owner adds cumulative imports, applies derived ledger changes,
and performs the final merge review. P7 must not edit P8 files before its own
gate; P8 must not alter P7's theorem statements to make the manifest convenient.

## 4. Dependency order and batch gates

The required order is:

~~~text
P7-PREP post-P6 API and staged-example audit
  → P7-T01 two-counter carrier and operations
  → P7-T02 recovery theorems
  → P7-T03 independence and negative evidence
  → P7-T04 ranked success/failure iterators
  → P7-T05 alpha-labelled regression
  → P7-T06 complete trace and vertical-slice report
  → P7 gate
  → P8-T01 derived conformance/readiness manifest
  → P8-T02 generic STC.Adapter R0 seam
  → P8-T03 feedback, rollback, and handoff record
  → P8 gate
~~~

P7-T01 through P7-T04 may reuse already landed proofs, but the agent must
verify their assumptions and extend them rather than silently marking the old
code as new P7 evidence. P7-T05 depends on the exact action and trace API
delivered by P6. P8-T02 depends on P5's state adapter contract and on the P8
manifest boundary, but it does not depend on a concrete runtime implementation.

## 5. P7-T01–T03 — TwoCounter operations, recovery, and independence

Primary file: STC/Examples/TwoCounter.lean.

### 5.1 Preserve and extend the carrier

Keep the existing:

~~~text
CounterState = Nat × Nat
inc1, inc2 : Effect CounterState
dec1, failIfZero : PartialOp CounterState Unit
inc1_lawful, inc2_lawful
inc12_independent
~~~

Add, if absent, the symmetric second-counter partial decrement and its explicit
guard/success behavior:

~~~text
dec2 : PartialOp CounterState Unit
~~~

A defined dec2 run must expose its successor, selected total inverse, and unit
outcome. An undefined branch remains Option.none and is not converted to a
diagnostic failure without an explicit handler. The proof must not hide the
positivity precondition inside an oversized well-formedness predicate.

### 5.2 P7-T02 — recovery and observation evidence

Provide checked proofs for the concrete operations that are actually claimed:

- exact recovery of each total increment under equality CounterState;
- the selected inverse and recovery behavior of defined dec1/dec2;
- any observational recovery specialization under an explicitly supplied
  relation, without installing a global Setoid;
- the Toy-only atomicity of failIfZero, keeping the general failure carrier
  capable of a changed boundary.

Use the existing P3 operation contracts where applicable:
DefinedAt, OperationRecovers, SelectedInverseStableOp, and
OperationIndependenceContract. If a contract is not proved for the partial
decrements, leave it as an explicit pending/deferred item rather than
constructing an unreachable witness.

### 5.3 P7-T03 — independence and negative evidence

Retain the positive disjoint-commutation theorem for inc1 and inc2, including
the selected-inverse relation. Add a genuinely negative finite counterexample
for a tempting but invalid claim if the existing
fstProjectOp_not_foreignStable does not cover the relevant P7 statement. The
negative case must exhibit an input and show the relation fails; a malformed or
impossible object is not a countermodel.

P7-T01 earns I/E for the concrete carriers and finite checks. P7-T02 and P7-T03
earn K only for checked theorem terms; a theorem that merely instantiates an
interface record with unproved fields remains I/contract evidence.

## 6. P7-T04 — ranked success/failure iterators

Primary file: STC/Examples/VerticalSlice.lean.

### 6.1 Preserve the P4 machine as a regression fixture

Preserve the current Control, counterRun, counterRank, counterIterator,
failingRun, and failingIterator unless a genuine P6 API incompatibility is
discovered and documented. Every yielded continuation must still satisfy the
strict rank decrease proved by counterNextLt or failingNextLt. Do not replace
rank recursion with fuel, an unguarded loop, or a coinductive stream.

The existing equation-pinned trace lemmas (for example counterExec_eq and
failingExec_eq) remain valuable P4 regression evidence. Extend them only where
necessary; do not rewrite them into a different rank machine.

### 6.2 Add an explicit two-counter path

The P7 path must exercise both disjoint operations, not merely the existing
first-counter countdown. Add an explicit finite control profile (or additive
constructors to Control) whose success path contains inc1 and inc2 before halt,
and whose failure path contains inc1 followed by failIfZero at a zero second
counter. Keep the existing five-stage P4 path available as a regression fixture
if extending it would change its public equations.

Use the blueprint's concrete inputs unless a checked, documented variant is
needed: the success path starts at (0, 0), reaches (1, 1), and recovers to
(0, 0); the failure path starts at (0, 0), reaches boundary (1, 0), and
retains the successful-prefix inverse. The report may include additional
nonzero-counter cases, but it must keep these canonical checks visible.

The new control profile must carry a strict rank certificate for every yield and
must expose equation-pinned traces. A two-counter path may be implemented as a
separate iterator in VerticalSlice.lean or as an additive phase extension, but
it must not duplicate the generic RankedIterator or failure carrier.

### 6.3 Integrated recovery theorem

Add one or more explicit theorems combining:

- local lawful/recovery evidence for the successful stages;
- the generic execFrom_recovers or its success/failure corollaries;
- the concrete success final state and LIFO inverse;
- the concrete failure boundary, error, and successful-prefix inverse; and
- the Toy-specific atomicity assumption for failIfZero where used.

The integrated theorem must expose every relation and witness hypothesis. It must
not be stated as a theorem about arbitrary lifecycle traces, asynchronous
control, or the Cordis runtime.

A successful P7 trace must visibly include both increments and its selected
LIFO inverse. The retained P4 regression may still have five stages. Every
failing P7 trace must visibly preserve error, boundary, and prefixUndo. No
failure may be represented as Option.none, identity, or an input-state rewrite.

### 6.4 Finite iterator checks

Check the strict rank decrease, success/failure constructor tags, stage counts,
and the equation-pinned final states for both the retained P4 fixture and the
new two-counter path. Use equation-based proofs where the well-founded evaluator
does not kernel reduce under decide. Do not put top-level #eval over exposed
production declarations.

## 7. P7-T05 — alpha-labelled regression

Primary file: STC/Examples/VerticalSlice.lean, using the P6 alpha modules.

### 7.1 Name-bearing labels without a false named-Q theorem

The current P4 iterator's Control carrier is name-neutral. Keep it that way
unless P7 supplies a genuine AlphaAction for a new named control carrier. The
recommended profile is:

- execute the two-counter iterator and retain the P4 regression unchanged;
- attach genuinely name-bearing actor/parent/reference labels through the P6
  trace/freshness boundary;
- apply a non-identity finite permutation to those labels and trace metadata;
- use the P6 exec/execFrom transport theorem for the state result.

Use a small finite name carrier (for example two explicit labels and their
swap) and prove the permutation is not the identity. A permutation over an
empty or unused name carrier is not an acceptable alpha regression.

This makes the alpha test non-vacuous while preserving P6's explicit
name-neutral Q/E assumptions. If a named Q, error, ambient payload, or
accumulator is introduced, the required action and interpreter equivariance
must be supplied in the same theorem; otherwise that extension is deferred.

### 7.2 Required alpha checks

Prove or pin:

- transport under a non-identity finite permutation;
- preservation of the success/failure constructor tag;
- transport of the final state and selected inverse/prefix inverse;
- transport of the label/reference/ledger fields;
- distinction between core-state observation and explicit name-aware
  boundary/trace observation.

Do not call the permutation witness an observational equivalence. Keep
AlphaAction and the P5 RelSpec profiles separate.

## 8. P7-T06 — complete trace and vertical-slice report

Extend or replace the existing SliceReport only additively. Include at least:

~~~text
success final state
successful recovery state
stage count
failure boundary/prefix recovery
independence check
partial-decrement checks (with any deferred precondition made explicit)
alpha-regression status (added in P7-T05)
~~~

Use equation-based proofs where the well-founded evaluator does not kernel
reduce under decide. Do not put top-level #eval over exposed production
declarations.

The P7 report must map each finite result to its paper/ADR interpretation and
state the refinement gap. At minimum it records:

~~~text
P7-T01: two-counter carrier and concrete operations
P7-T02: exact/observational recovery theorems
P7-T03: disjoint commutation, selected-inverse contract, and negative test
P7-T04: ranked success/failure iterators and termination equations
P7-T05: nontrivial alpha-labelled regression
P7-T06: integrated recovery, complete trace, and finite report
~~~

P7 is ready only when:

- all touched files compile under the pinned options;
- substantive theorem claims contain no sorry, admit, custom unchecked axiom,
  or unsafe;
- the finite report has an inspectable expected value;
- the alpha test uses a non-identity permutation and genuinely name-bearing
  fields;
- the new success path exercises both inc1 and inc2, while the failure path
  retains error, boundary, and prefixUndo;
- no P3/P4 theorem or P6 action convention was silently changed; and
- the deferred control/staging/support/scoped/runtime boundaries are listed.

Suggested focused checks:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/TwoCounter.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/VerticalSlice.lean
~~~

After integration imports are added, rerun:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
python scripts/scan_lean.py STC
~~~

The final scanner exit must be 1 (clean); retain raw output in
docs/status/P7-scan-raw.txt.

## 9. P8-T01 — derived conformance and readiness manifest

Primary files: STC/Conformance/Manifest.lean and derived status files under
docs/status.

### 9.1 Manifest purpose and source-of-truth rule

The manifest is generated evidence, not a replacement for H03/H04 or the
accepted ADRs. It must preserve:

~~~text
H03 path and SHA-256
H04 path and SHA-256
accepted ADR artifact hashes/statuses
current repository commit and branch
all 82 paper/auxiliary row IDs
delivery and evidence labels
target module and theorem/file references
deferred blockers and reasons
~~~

Do not regenerate the ledger with scripts/gen_definition_ledger.py; that
P0-era generator would erase later curation. Use the existing validator and a
new deterministic manifest generator or a carefully reviewed derived update.

A suitable typed Lean schema is:

~~~lean
inductive EvidenceKind
  | alignment | interface | kernel | executable | r0 | r1Plus

structure EvidenceEntry where
  paperId : String
  delivery : String
  evidence : EvidenceKind
  note : String
~~~

The exact names may be refined, but the schema must keep interface, proof,
execution, and refinement evidence distinct. A stringly JSON field must not be
allowed to imply a theorem proof.

### 9.2 Derived artifacts

Produce:

~~~text
docs/status/P8-conformance-manifest.json
docs/status/P8-deferred-obligations.md
~~~

The JSON should be deterministic (stable key order and row order), include
source hashes, and list every paper/auxiliary ID exactly once. The Markdown
report should group remaining obligations by BD-CONTROL, BD-STAGING, BD-SUPPORT,
BD-SCOPED, BD-COEFFECT, and runtime refinement, with the exact evidence boundary
for each.

Run at least:

~~~bash
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/generate_conformance_manifest.py
sha256sum docs/status/P8-conformance-manifest.json
~~~

Unless an equivalent deterministic generator already exists, add
scripts/generate_conformance_manifest.py. It must read frozen H03/H04 and the
current derived ledger, fail closed on hash/schema mismatch, and never edit a
frozen file.

### 9.3 Proposed ADR packet integrity

The current main tree includes JSON/Markdown/spike material for ADR-07,
ADR-08, and ADR-09. ADR-10 currently has only its Lean spike in this checkout;
its JSON and Markdown companions are absent. P8-T01 must inventory these
packets and report completeness explicitly. A missing artifact, compiler-pending
status, or proposed status must remain a warning/deferred item; it must not be
upgraded to an accepted ADR or silently repaired inside the manifest task.

## 10. P8-T02 — generic STC.Adapter R0 seam

Primary file: STC/Adapter.lean.

This file is a metatheory-side abstraction contract. It must not import a
Cordis source tree, use a concrete runtime state, or claim implementation
verification. Keep all declarations generic and under namespace STC.Adapter.

A minimal directional interface is:

~~~lean
namespace STC.Adapter

structure StateRefinement (Concrete Abstract : Type u) where
  abstract : Concrete → Abstract
  admissible : Concrete → Prop
  concreteObs : Concrete → Concrete → Prop
  abstractObs : RelSpec Abstract
  observes :
    RespectsOn concreteObs abstractObs.rel abstract

structure Simulates
    (Concrete Abstract CLabel ALabel : Type u) where
  refinement : StateRefinement Concrete Abstract
  labelMap : CLabel → ALabel
  concreteStep : Concrete → CLabel → Concrete → Prop
  abstractStep : Abstract → ALabel → Abstract → Prop
  forward :
    ∀ {c label c'},
      refinement.admissible c →
      concreteStep c label c' →
      ∃ a',
        abstractStep (refinement.abstract c) (labelMap label) a' ∧
          refinement.abstractObs.rel (refinement.abstract c') a'
end STC.Adapter
~~~

The exact universe and relation parameters may be adjusted for Lean
ergonomics, but preserve these semantic properties:

- abstraction is one-way;
- the concrete and abstract step relations are explicit;
- labels are mapped explicitly;
- admissibility is visible;
- the forward simulation witness relates the abstracted concrete successor to
  the abstract successor;
- no converse simulation, bisimulation, scheduler model, or runtime theorem is
  implied.

Do not use an empty relation or impossible admissibility predicate merely to
construct a smoke instance. If a finite signature check is added, use a
nonempty, explicit relation and label map, or leave the interface uninstantiated.
R0 means “seam available,” not “Cordis verified.”

The file should document how future adapters can connect P5 StateLike/ValidState
and P4 RankedIterator without placing runtime declarations into the metatheory
namespace. The reserved name Cordis must not be used as a production namespace
in this wave.

## 11. P8-T03 — feedback, rollback, and superseding-ADR log

Primary files: docs/status/P8-feedback-log.md and
docs/status/P8-deferred-obligations.md.

Record, in reproducible form:

- every failed proof attempt that materially affected an API;
- Lean/Lake/toolchain quirks and the exact workaround;
- finite counterexamples and vacuity checks;
- any mismatch between paper, Formal Reference, accepted ADR, Blueprint, and
  implementation;
- whether the issue is an ordinary deferred obligation or requires a
  superseding ADR;
- the exact commit and command outputs for the final state.

If no new failure occurred, say so explicitly rather than inventing a
counterexample. Preserve failed attempts as history; do not delete them to make
the manifest look clean.

A superseding ADR is required before changing a selected carrier, failure
meaning, alpha action convention, freshness boundary, or one-way R0 semantics.
Editorial wording, theorem-name changes, and additional cross-references do not
require a new decision packet.

## 12. P8 gate and cumulative validation

P8 is ready for merge only when the following all hold:

1. P7's focused checks and finite report pass and are recorded.
2. STC/Conformance/Manifest.lean elaborates with the explicit options.
3. STC/Adapter.lean elaborates with the explicit options.
4. The cumulative STC/Bootstrap.lean import update (performed by the
   integration owner) compiles and lake build is green.
5. The manifest validator covers all 82 IDs, preserves H03/H04 hashes, and
   reports proposed/compiler-pending ADR packets accurately.
6. scripts/scan_lean.py STC exits 1; raw output is retained in
   docs/status/P8-scan-raw.txt.
7. No production file contains placeholders or unchecked axioms.
8. The handoff classifies each result as A/I/K/E/R0/R1+ and explicitly records
   that no R1+ evidence was produced.

Suggested commands:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Conformance/Manifest.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Adapter.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/generate_conformance_manifest.py
python scripts/scan_lean.py STC
git diff --check
~~~

A missing compiler is a blocked validation result, not evidence of success.

## 13. Ledger coordination and expected derived updates

The integration owner, not the P7/P8 implementation agent, applies derived ledger
updates after reviewing the reports. Frozen H03/H04 fields, dependency lists,
paper anchors, and accepted ADR artifacts must remain byte-for-byte unchanged.

The cumulative P3/P4/P5 patches should be reconciled first. D8 remains the
already-completed P2 row and must not be downgraded or overwritten. Likely P7
updates are:

| Rows | Possible update | Remaining boundary |
|---|---|---|
| D19, D34, D39 | concrete operation/independence evidence | complete coeffect-mediated operation calculus remains deferred |
| D51, D52, R.iter, R.fail | finite iterator/failure integration evidence | lifecycle rule constructors remain BD-CONTROL |
| L56 | finite name-neutral alpha regression evidence | named payload/control equivariance remains deferred |
| T73 | finite alpha/support witness only | support/confluence remains BD-SUPPORT + BD-CONTROL |
| R.full | no completion claim | authoritative ten-rule calculus remains deferred |

Likely P8 updates are:

| Row | Possible update | Remaining boundary |
|---|---|---|
| D53 | derived trace/manifest alignment and explicit boundary | lifecycle/control trace semantics remain deferred |
| D74 | R0 adapter seam only | R1+ implementation refinement remains deferred |
| D32, D33, D45, D58 | preserve or refine existing P5 evidence | provider/WF/active-store preservation remains deferred |

Do not mark a row completed/proved merely because a manifest or adapter
signature compiles. Do not remove BD-CONTROL, BD-STAGING, BD-SUPPORT,
BD-SCOPED, or runtime-refinement blockers from evidence that does not discharge
them.

## 14. Reopen rules and downstream boundary

This batch may add finite theorem instances, derived reports, and generic
interfaces without a new ADR. A superseding ADR is mandatory for:

- changing the CounterState/EffectResult/ExecResult/RankedIterator semantics;
- treating the alpha action as a default observation relation;
- adding names to Q/E without explicit actions and interpreter laws;
- moving the freshness ledger into P5 RawState or default core observation;
- making STC.Adapter a concrete Cordis implementation or claiming R1+;
- changing the one-way simulation direction or silently adding a converse.

After P8, the intended order is:

~~~text
P8 evidence/R0 seam
  → control and staging instantiation (ADR-07/08)
  → support/well-foundedness integration (ADR-09)
  → scoped coeffect integration (ADR-10)
  → concrete Cordis source audit and R1+ refinement
~~~

P7/P8 therefore provide the first auditable finite end-to-end slice and a clean
abstraction boundary, not the end of the STC/Cordis verification program.
