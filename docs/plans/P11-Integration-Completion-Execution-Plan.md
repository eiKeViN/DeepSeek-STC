# STC P11 Integration and Completion Execution Plan

| Field | Value |
|---|---|
| Plan ID | DH-P11-INTEGRATION-CLOSEOUT-EXEC-01 |
| Repository | https://github.com/eiKeViN/DeepSeek-STC |
| Prepared | 2026-08-29 |
| Planning baseline | origin/main at 7beb9cb, after the P10/P11 Staging and P11 Support Core merges |
| Depends on | P9 accepted ADR-07/08/09 records; P10 Control freeze; P11 Staging handoff; P11 Support Core handoff |
| Scope | close the P11 production-integration package without claiming P13 global metatheory |
| Modules/namespaces | STC.State.Support.* modules with established STC declarations; additive STC.Control and STC.Staging bridges |
| Status | ready to schedule after this plan is merged |

This plan is the join promised by the two parallel P11 plans. The entry gate is
now satisfied: production Control and Staging are merged, and the independent
Support Core is merged. The join may therefore consume all three frozen public
surfaces rather than guessing an unfinished sibling API.

Completing P11 has a precise meaning here. It means completing the accepted
ADR-08/ADR-09 production package, cross-module transport hooks, finite
integration evidence, cumulative imports, and central traceability. It does not
mean that every paper row mentioning control or support becomes proved. The
concrete guarded ten-rule calculus, reached-state invariants, support at
quiescence, episode deletion, and confluence remain P13 work.

## 1. Verified entry state

The planning audit found the following commits on origin/main:

~~~text
47c3b80  P10 Control production API and finite evidence
a18407c  P11 derived Staging macro/view and finite evidence
2f6d357  P11 Support Core, LFP/rank evidence, and finite graph fixtures
cdcdd6d  merge of the Control/Staging lane
7beb9cb  merge of the Support Core lane
~~~

The corresponding handoffs report focused Lean checks, the cumulative build,
the Definition Ledger validator, the production scanner, and diff checks as
passing:

~~~text
docs/status/P10-api-freeze.md
docs/status/P10-handoff-report.md
docs/status/P11-staging-handoff-report.md
docs/status/P11-support-core-handoff-report.md
~~~

This is sufficient to begin the join. It is not sufficient to mark literal
L68, L70, L72, or T73 complete: the current ControlModel deliberately packages
arbitrary relation ports, and no production state-to-support projection or
concrete Section-4 rule implementation yet establishes the hypotheses of those
results.

## 2. Authority and evidence boundary

Literal paper claims remain paper claims. Frozen H03/H04 and the Formal
Reference preserve the audited source dependencies and repairs. The repaired
production target is governed by the accepted ADRs, especially the P9 status
records:

~~~text
docs/blueprint/architecture-decision/status/ADR-07-accepted.json
docs/blueprint/architecture-decision/status/ADR-08-accepted.json
docs/blueprint/architecture-decision/status/ADR-09-accepted.json
~~~

The candidate ADR Markdown/JSON and historical spikes retain their pre-P9
metadata as frozen provenance. The later accepted status records are the
normative architecture-state source. Do not edit either family in this plan.

The join targets:

* A: checked alignment with accepted ADR-08/09 contracts;
* I: production declarations elaborate through the cumulative package root;
* K: fixed-point uniqueness, alpha transport, and conditional trace/macro
  transport theorems with every premise explicit;
* E: finite positive and negative integration fixtures.

It does not target Cordis R1+ refinement or an unconditional global Section-4
theorem.

## 3. Preflight and branch gate

Create the execution branch from the commit containing this plan. Its base must
descend from 7beb9cb and contain the three delivery commits above.

~~~bash
git fetch origin --prune
git switch -c <p11-integration-branch> origin/main
git status --short --branch
git log -1 --oneline

git merge-base --is-ancestor 47c3b80 HEAD
git merge-base --is-ancestor a18407c HEAD
git merge-base --is-ancestor 2f6d357 HEAD
git merge-base --is-ancestor 7beb9cb HEAD

jq -e '
  .record_status == "accepted" and
  .architecture_status == "closed" and
  .formal_acceptance == true
' docs/blueprint/architecture-decision/status/ADR-08-accepted.json

jq -e '
  .record_status == "accepted" and
  .architecture_status == "closed" and
  .formal_acceptance == true
' docs/blueprint/architecture-decision/status/ADR-09-accepted.json

lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
~~~

The four ancestry commands and both acceptance checks must exit 0. For
scripts/scan_lean.py, exit 1 means clean, exit 0 means lexical matches requiring
classification, and exit 2 is a scanner error.

Read before editing:

~~~text
AGENTS.md
README.md
STC.lean
STC/Bootstrap.lean
STC/Control.lean
STC/Staging.lean
STC/State/Support.lean
STC/Alpha/Core.lean
STC/Alpha/Trace.lean
STC/Examples/Control.lean
STC/Examples/Staging.lean
STC/Examples/Support.lean
docs/plans/P10-P11-Staging-Execution-Plan.md
docs/plans/P11-Support-Core-Execution-Plan.md
docs/status/P10-api-freeze.md
docs/status/P11-staging-handoff-report.md
docs/status/P11-support-core-handoff-report.md
docs/status/Definition-Ledger.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.md
~~~

Record the actual execution base rather than copying 7beb9cb mechanically if
new unrelated main commits have appeared.

## 4. Ownership and protected surfaces

The join owns additive work in:

~~~text
STC/Staging.lean
STC/State/Support/Closure.lean
STC/State/Support/Alpha.lean
STC/Control/Support.lean
STC/Staging/Support.lean
STC/Examples/Staging.lean
STC/Examples/SupportTrace.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/P11-integration-handoff-report.md
docs/status/P11-integration-scan-raw.txt
README.md
AGENTS.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
~~~

The exact Closure/Alpha split may be consolidated if the dependency DAG and
public surface become simpler. The Control and Staging support files remain
additive consumers: they must not duplicate SupportSnapshot, Control.Trace, or
Staging.MacroPath.

STC.State.Support.Closure and STC.State.Support.Alpha are module names. Their
declarations remain in the established STC namespace used by Support.lean
unless a deliberately nested namespace re-exports one coherent API; do not
fork the support carrier into a competing STC.State.Support declaration
namespace.

Protected and unchanged:

~~~text
STC/Control.lean
STC/State/Support.lean
STC/Alpha/**
docs/blueprint/baseline/**
docs/blueprint/architecture-decision/md/**
docs/blueprint/architecture-decision/json/**
docs/blueprint/architecture-decision/lean-spike/**
docs/blueprint/architecture-decision/status/**
docs/status/P8-conformance-manifest.json
~~~

The merged Support Core definitions and the P10-frozen STC/Control.lean remain
byte-for-byte unchanged. All new closure and bridge theorems live in additive
modules.

The status-only Blueprint edits are limited to the live execution snapshot,
module current_status fields, and P9/P10/P11 phase state. They must not edit
H03/H04, candidate ADR semantics, recorded hashes, or historical P8 claims.

## 5. Required dependency shape

Use an acyclic graph equivalent to:

~~~text
STC.State.Support
  └─> STC.State.Support.Closure

STC.State.Support.Closure + STC.Alpha.Trace
  └─> STC.State.Support.Alpha

STC.Control + STC.State.Support.Closure
  └─> STC.Control.Support

STC.Staging + STC.Control.Support
  └─> STC.Staging.Support

all production modules + finite fixtures
  └─> STC.Bootstrap ─> STC
~~~

Support Core must remain usable without importing Control or Staging. Control
Support may import the core/closure layer. Staging Support consumes the Control
bridge and the already authoritative MacroPath trace. Production files never
import examples.

## 6. Task order

~~~text
P11I-T00  entry audit and freeze checks
  -> P11I-T01  close local Staging contract gaps
  -> P11I-T02  fixed-point uniqueness and alpha transport
  -> P11I-T03  Control trace support contract
  -> P11I-T04  Staging macro lift and L70 algebraic seam
  -> P11I-T05  finite integrated evidence
  -> P11I-T06  cumulative imports and live-guidance reconciliation
  -> P11I-T07  central Ledger adjudication
  -> P11I-GATE handoff and clean commit
~~~

T03 depends on the closure API from T02. T04 consumes T03 and the repaired
Staging surface from T01. Do not edit Ledger statuses incrementally before the
corresponding declarations and focused checks exist.

## 7. P11I-T01 — close the local Staging contract gaps

The merged Staging layer correctly derives Rb from MacroPath over the
authoritative Control trace. Two interface details still need closure before
the P11 package is frozen.

### 7.1 Explicitly permitted stuttering

The current AtomicAdequacy conclusion contains a bare before = after branch.
ADR-08 permits stuttering only as an explicitly tagged, profile-authorized
no-op. Replace the bare branch with a visible permission boundary, for example:

~~~lean
structure StutterProfile (model : StagingModel ...) where
  Tag : Type
  orchestration : Tag → List (Sum FullOrchLabel FullLifeLabel) → BaseState → Prop
  lifecycle : Tag → List (Sum FullOrchLabel FullLifeLabel) → BaseState → Prop

inductive AdequacyOutcome ... where
  | macro ...
  | stutter (tag : profile.Tag) (allowed : ...) (endpoint : before = after)
~~~

The exact packaging may differ, but all of these are mandatory:

* a stutter carries a visible profile permission or tag;
* endpoint equality alone is insufficient;
* failing, unfinished, interleaved, yielded, or pending-async paths cannot be
  reclassified as stuttering success;
* orchestration and lifecycle permissions remain distinct;
* AtomicAdequacy still classifies only profile-accepted paths between embedded
  endpoints.

Update the finite Staging fixture with one permitted no-op and one equal-endpoint
path rejected because it lacks the required permission.

### 7.2 Quiescence bridge boundary

Expose a profile/contract for the stable-image quiescence bridge. Its premises
must name stable-image closure, completeness of the selected macro partition,
absence of a pending in-flight/failure endpoint, and the matching guard,
provider, and WellFormed assumptions.

It is acceptable for P11 to provide the contract and a finite instance. Do not
prove or advertise an unconditional quietFull (embed b) iff quietBase b theorem.
The concrete implication from lifecycle rules belongs to P13.

### 7.3 Complete the finite macro surface

Add the missing explicit singleton orchestration macro witness and a checked
finite AtomicAdequacy realization for the selected toy profile. Retain the
existing reload/unload, forward, composition, and rejection evidence.

This task may edit STC/Staging.lean and STC/Examples/Staging.lean, but it must
not edit STC/Control.lean or introduce an independent base calculus.

## 8. P11I-T02 — fixed-point uniqueness and alpha transport

### 8.1 Uniqueness under an explicit support order

In STC/State/Support/Closure.lean, prove that the accepted rank certificate
makes the positive support fixed point unique. The required theorem shape is:

~~~lean
theorem supportSet_eq_of_fixed
    (order : SupportOrder snapshot)
    (hfixed : SupportOperator snapshot A = A) :
    SupportSet snapshot = A := ...
~~~

An equivalent orientation is acceptable. The proof must use well-founded/rank
induction over the actual prerequisite edges. It may not assume uniqueness as a
field or derive it from finiteness alone.

Also provide:

* a version taking both inclusions A ⊆ SupportOperator snapshot A and the
  converse;
* a NoLateRegistration corollary through NoLateRegistration.toOrder;
* a finite negative profile showing why an order/certificate hypothesis may
  not be discarded, if such a counterprofile exists for the implemented
  operator.

If the uniqueness statement is false for the accepted operator, stop and
record the smallest counterexample. Do not silently strengthen SupportClause or
SupportOrder.

### 8.2 Rename support snapshots, not keys

In STC/State/Support/Alpha.lean, rename the incarnation carrier N by an
Equiv.Perm N while keeping the provision-key carrier K fixed. The renamed
snapshot must transport:

* dom by the existing renameFinset;
* retired, requires, provides, and birth by inverse reindexing;
* parent through renameParentRef;
* Precedes, ParentEdge, SupportRel, and SupportDep in both directions;
* SupportOperator and SupportSet membership;
* SupportOrder, SupportWF, NoLateRegistration, and CommittedSnapshot.

Provide identity, composition, and inverse/cancellation laws, either directly
or through an AlphaAction instance. Transport the existence/property of a rank
certificate; do not require one particular numeric rank function to be
pointwise invariant.

Add a non-identity finite swap fixture. An identity-only example is not alpha
evidence.

## 9. P11I-T03 — Control trace support contract

Create STC/Control/Support.lean without changing the P10-frozen Control file.
The module connects a Control state carrier to support through an explicit
projection and invariant contract. A suitable surface is:

~~~lean
def HasCommittedSupport
    (snapshot : C → SupportSnapshot N K) (state : C) : Prop :=
  Nonempty (CommittedSnapshot (snapshot state))

structure SupportTraceContract
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) where
  snapshot : C → SupportSnapshot N K
  orchestration_preserves : ∀ {label before after},
    orchestration label before after →
      HasCommittedSupport snapshot before →
      HasCommittedSupport snapshot after
  lifecycle_preserves : ∀ {label before after},
    lifecycle label before after →
      HasCommittedSupport snapshot before →
      HasCommittedSupport snapshot after
~~~

The precise packaging may transport SupportOrder directly, use a subtype, or
split projection and preservation into smaller records. It must transport a
support-bearing certificate in each step; a global field saying that every
state satisfying an unrelated eligible predicate already has a certificate is
only seam evidence and is insufficient for the L68-facing K theorem. The
following boundaries are mandatory:

* snapshot projection is explicit and is not cached in RawState;
* orchestration and lifecycle preservation fields remain separate;
* the initial certificate premise is explicit;
* no scheduler, reachability axiom, or hidden WellFormed strengthening is added;
* a certificate at every reached endpoint is derived by induction over the
  existing indexed Control.Trace;
* endpoint SupportWF and supportDep_wellFounded corollaries are proved from the
  transported certificate;
* an optional constructor from a per-state NoLateRegistration proof must still
  expose the premise rather than asserting it for every Control relation.

This is a genuine conditional K theorem about the shared trace carrier. It is
not literal L68, because this plan does not instantiate the contract from the
paper's concrete rule guards.

## 10. P11I-T04 — Staging macro lift and algebraic L70 seam

### 10.1 Reuse MacroPath.trace

Create STC/Staging/Support.lean. Lift the T03 theorem through:

* MacroPath.trace;
* AtomicOrchMacro/RbOrch;
* AtomicLifeMacro/RbLife;
* append_macro_paths.

Every theorem must reuse the Control trace and its per-step contract. Do not
add a second trace carrier, a second full relation, or a separately maintained
base relation.

Prove that a profile-approved Rb macro beginning with committed support ends
with an explicit SupportOrder/SupportWF certificate. Ordinary RbOrch/RbLife
lifts always consume MacroPath.trace; do not add stuttering to Rb itself.

Separately, prove the support-facing theorem for AtomicAdequacy's
AdequacyOutcome. Its macro branch uses the trace bridge. Its stutter branch may
transport support only through the explicit T01 permission together with
endpoint equality. This keeps tagged converse stuttering distinct from the
forward Rb relation.

### 10.2 Algebraic support-equals-active hook

Export the exact fixed-point hook later L70 needs. For an explicitly supplied
active set, prove SupportSet snapshot = active when:

* SupportOrder snapshot is available; and
* active is both generated by and closed under SupportOperator, equivalently a
  fixed point.

Do not call those algebraic hypotheses quiescence, nonfailure, or total
provision unless concrete predicates and implication theorems are supplied.
P13 must prove those semantic conditions imply the fixed-point hypotheses for
the actual lifecycle calculus.

## 11. P11I-T05 — finite integrated evidence

Create STC/Examples/SupportTrace.lean. Reuse the production modules and, where
helpful, the existing finite Control/Staging fixture. Include:

* a nonempty labelled Control lifecycle trace;
* a state-to-snapshot projection with a nontrivial finite domain;
* explicit initial and per-step support certificates;
* endpoint SupportWF and restricted SupportDep well-foundedness obtained from
  the generic trace theorem;
* one Staging lifecycle macro using the same certificate bridge;
* one singleton orchestration macro using the same bridge;
* one support-equals-active fixed-point example;
* the non-identity alpha swap from T02;
* one rejected missing-certificate or cyclic profile.

Do not relabel the existing graph-only cycle as a reachable counterexample to
the paper's full lifecycle calculus. A semantic F-L68-CYCLE witness requires
the concrete rule implementation and belongs to P13.

All executable checks are example ... := by decide or theorem blocks. Do not
add top-level eval over exposed library declarations.

## 12. P11I-T06 — cumulative imports and live guidance

Update STC/Bootstrap.lean so lake build reaches:

~~~text
STC.Control
STC.Staging
STC.State.Support
the new closure/alpha/trace/macro integration modules
STC.Examples.Control
STC.Examples.Staging
STC.Examples.Support
STC.Examples.SupportTrace
~~~

Keep public imports sorted and update the Bootstrap module docstring and main
declaration inventory. STC.lean should continue to import Bootstrap rather than
duplicating the list.

Reconcile live guidance in README, AGENTS, and the executable Blueprint:

* P9 accepted ADR-07 through ADR-10 through separate status records;
* P10 is merged and Control is frozen;
* P11 Staging and Support Core are merged;
* this join closes the P11 production-integration package;
* ADR-10 is accepted but Scoped production remains a separate P12 state unless
  a newer main commit proves otherwise;
* global Section-4 K results and runtime refinement remain pending.

Preserve dated historical snapshots where they are explicitly labelled as
snapshots; replace only prose or current_status fields that claim the modules
do not exist or that the ADRs are still currently unaccepted.

Do not regenerate the historical P8 conformance manifest.

## 13. P11I-T07 — central Definition Ledger adjudication

This join is the central integration owner and must edit the Ledger in place.
Do not run gen_definition_ledger.py. Preserve every frozen H03/H04 provenance
field, including h04_blocking_decisions and h04_readiness.

Use the following conservative disposition unless execution produces stronger
exact evidence:

| Row | P11 closeout disposition | Evidence boundary |
|---|---|---|
| D44 | keep in_progress/aligned; append STC/Control.lean | control carrier delivered; concrete FiberCell integration pending |
| D46 | in_progress/seam_only; append STC/Staging.lean | embed/project/stable and quiescence contract only |
| D47 | in_progress/seam_only; append STC/Control.lean | insert label/fixture exist; concrete nested-registration action and frame laws pending |
| D49 | in_progress/seam_only; target STC/Control.lean | modes, in-flight/outcome, labels delivered; installed/failed/quiescence guards pending |
| D53 | keep in_progress/seam_only; append STC/Control.lean | Step/Trace/policy/append delivered; episode/factorization and state relations pending |
| D65 | in_progress/seam_only; target STC/State/Support.lean | Precedes is defined on snapshots; exact production-registry projection remains pending |
| D67 | in_progress/proved; target STC/State/Support.lean; STC/State/Support/Closure.lean | positive LFP, fixedness, leastness, and conditional uniqueness delivered; exact state projection pending |
| L68 | in_progress/proved; target STC/State/Support.lean; STC/Control/Support.lean | abstract-contract endpoint well-foundedness under explicit initial-certificate and per-step certificate-transport premises; no concrete-rule preservation or reached-state L68 theorem |
| L70 | in_progress/proved; target STC/State/Support/Closure.lean; STC/Staging/Support.lean | conditional equality from SupportOrder plus active fixed-point hypotheses; quiescent/nonfailed/total-provision implication pending P13 |
| L56 | keep in_progress/proved; target STC/Alpha/Transport.lean; STC/State/Support/Alpha.lean | snapshot/support alpha transport added; full name-bearing Control equivariance pending |
| R.base | in_progress/seam_only; target STC/Staging.lean | derived Rb interface and finite macro evidence delivered; concrete rule family/global adequacy remain pending |
| R.withdraw | in_progress/seam_only; append STC/Control.lean | labels and finite path exist; concrete guards/frame theorems pending |
| R.iter | keep in_progress/proved; append STC/Control.lean | iterator evidence plus lifecycle labels; concrete full rules pending |
| A.async | in_progress/seam_only; target STC/Control.lean | landing/abort contract and finite evidence; derivation from concrete rules and global trace/progress use pending |
| R.fail | keep in_progress/proved; append STC/Control.lean | complete Failure/L-Raise bridge; concrete raise transition pending |
| R.full | in_progress/seam_only; target STC/Control.lean | authoritative relation ports and typed labels/steps; ten guarded relations not instantiated |

The following rows do not become complete in P11:

~~~text
L54 L55 L57 T59 T61 C62 T63 T64 T66
D60 D69 L71 L72 T73 Table1
~~~

Retain their current status/evidence unless an exact theorem was independently
implemented and checked within authorized scope. Replace stale deferred_reason
phrases such as BD-CONTROL deferred with the exact remaining production or P13
obligation, but do not erase the historical H04 blocker arrays.

Do not promote a row merely because a structure field states the desired law.
A supplied contract is interface/seam evidence; a theorem deriving the law from
weaker premises is K evidence.

## 14. Required validation

Run every touched Lean file with the repository flags, including at minimum:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Staging.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Support/Closure.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Support/Alpha.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Control/Support.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Staging/Support.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Staging.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/SupportTrace.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean

lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
git diff --check
~~~

Also run boundary checks from the recorded branch base:

~~~bash
git diff --exit-code <branch-base> -- STC/Control.lean
git diff --exit-code <branch-base> -- STC/State/Support.lean
git diff --exit-code <branch-base> -- docs/status/P8-conformance-manifest.json
git diff --exit-code <branch-base> -- docs/blueprint/baseline
git diff --exit-code <branch-base> -- docs/blueprint/architecture-decision

rg -n 'architecture-decision/lean-spike|STCADR0[789]' STC
rg -n 'sorry|admit|axiom|unsafe' \
  STC/Staging.lean STC/State/Support STC/Control/Support.lean \
  STC/Staging/Support.lean STC/Examples/Staging.lean \
  STC/Examples/SupportTrace.lean
~~~

The first four diff commands must be clean. Production imports of historical
spikes are a hard failure. Classify scanner lexical matches rather than treating
exit 0 as clean. Store raw scanner output in
docs/status/P11-integration-scan-raw.txt.

## 15. Acceptance criteria

P11 is phase-complete only when:

1. all P9/P10/P11 ancestry and accepted-status gates pass;
2. the P10 Control file remains unchanged;
3. Rb remains derived from the authoritative Control trace;
4. AtomicAdequacy no longer admits bare equality as an untagged stutter;
5. the quiescence bridge exposes every ADR-08 premise and makes no global claim;
6. Support fixed-point uniqueness is checked under an explicit SupportOrder;
7. support alpha transport covers relations, SupportSet, and certificates under
   a non-identity permutation while keeping keys fixed;
8. a state-to-snapshot contract whose per-step fields transport the actual
   support certificate yields endpoint certificates through nonempty Control
   traces;
9. the same contract lifts through Staging MacroPath and derived Rb;
10. the algebraic L70 hook is proved without pretending its semantic premises
    have been derived;
11. finite evidence is nonvacuous and includes a rejected profile;
12. Bootstrap imports every P10/P11 production and example module;
13. live guidance no longer describes ADR-07/08/09 as currently unaccepted or
    the merged P10/P11 modules as nonexistent;
14. the central Ledger records exact partial/full evidence and leaves global
    theorem rows open;
15. focused Lean checks, full build, Ledger validator, scanner, and diff checks
    pass;
16. the final handoff records exact declarations, assumptions, row deltas,
    commands, hashes, and the clean commit.

## 16. Explicit P13 boundary

P11 completion leaves these substantive obligations for P13:

* instantiate the full guarded orchestration/lifecycle relations over the
  production state rather than arbitrary relation ports;
* define reached states/episodes and prove registry/SupportOrder preservation;
* mechanize the exact reachable F-L68-CYCLE counterexample or prove the
  strengthened invariant that excludes it;
* prove support equals active at reachable quiescent, nonfailed states under
  total provision;
* prove adjacent-step transposition and deletion of a closed episode;
* combine support ordering, termination, alpha/equivalence transport, and
  schedule normalization into the repaired T73 package.

Therefore the P11 handoff must say production-integration complete and global
metatheory pending. It must never say all of L68/L70/L72/T73 are complete.

## 17. Stop and reopen rules

Stop rather than improvising if:

* fixed-point uniqueness is false for the accepted operator/order;
* explicit stutter permission requires changing the authoritative R+ or making
  Rb independently authoritative;
* alpha transport needs renaming provision keys K without an accepted profile;
* trace preservation can be proved only by hiding NoLateRegistration or
  SupportOrder inside an unrelated WellFormed field;
* a proof requires changing the frozen Control API;
* a purported F-L68 counterexample uses an arbitrary toy relation but is
  presented as reachable under the paper's full rules;
* completing L70/L72/T73 would require inventing missing lifecycle guards,
  episode semantics, or transposition laws;
* a shared or frozen artifact outside this ownership list must change;
* finite computation is the only evidence for a row labelled proved.

The reopen report must identify the smallest conflicting signature or theorem
and classify it as ADR inconsistency, source ambiguity, Lean engineering, or
P13 dependency.

## 18. Handoff and downstream scheduling

Create docs/status/P11-integration-handoff-report.md with:

* branch base/head and all relevant ancestor commits;
* public API and import graph;
* Staging stutter/quiescence repair summary;
* closure, alpha, Control-trace, and Staging-macro theorem inventory;
* exact assumptions for every K theorem;
* finite positive/negative evidence;
* itemized Definition Ledger before/after values;
* protected-path hash/diff confirmation;
* raw validation results and scanner classification;
* explicit P13 deferred inventory.

P12 remains independent and may execute concurrently if it follows its existing
ownership plan. Once P11 closes, P13 planning may use the frozen P11 interfaces;
P13 execution still waits for P12 wherever scoped claims are included.
