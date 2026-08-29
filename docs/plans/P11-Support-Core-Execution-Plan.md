# STC P11 Support Core Execution Plan

| Field | Value |
|---|---|
| Plan ID | DH-P11-SUPPORT-CORE-EXEC-01 |
| Repository | https://github.com/eiKeViN/DeepSeek-STC |
| Prepared | 2026-08-29 |
| Planning baseline | origin/main at 2f83afb, post-P9 merge |
| Depends on | P8 complete; P9 complete; ADR-09 accepted |
| Scope | production snapshot support closure, support ordering, and core evidence |
| Ownership | one independent lane; no dependency on unfinished Control or Staging code |
| Namespace | STC, with the production module STC/State/Support.lean |
| Status | ready to schedule from the common post-planning merge |

This lane implements the Control-independent core of accepted ADR-09. It turns
the support graph from a blueprint contract into a production Lean API: an
explicit committed snapshot, directed support relations, a positive closure
operator and least fixed point, plus the well-founded order needed by later
proofs.

The lane intentionally stops before trace-facing support theorems. Statements
that quantify over Control traces, lifecycle transitions, or Staging macros are
an integration join after the Control/Staging lane has frozen its API. This
separation is what makes P11 Support Core genuinely parallel with P10/P11
Staging and P12 Scoped.

## 1. Authority and accepted-decision baseline

The paper remains authoritative for literal source claims. Frozen H03/H04 and
the Formal Reference preserve audited provenance and source defects. The
repaired formal target for this lane is governed by accepted ADR-01 through
ADR-09, especially the independent P9 status record:

~~~text
docs/blueprint/architecture-decision/status/ADR-09-accepted.json
~~~

That record reports record_status = accepted, architecture_status = closed,
and formal_acceptance = true. Candidate ADR Markdown/JSON, historical spikes,
and the P8 manifest retain their earlier pre-P9 status as provenance. They are
not current architecture-state authorities and must not be rewritten merely to
make their wording match the later acceptance record.

If older Blueprint, AGENTS, README, candidate-packet, or P8 prose still says
proposed or acceptance_pending, the P9 acceptance record together with
docs/status/P9-handoff-report.md governs the current decision state.

The accepted ADR-09 contracts for this lane are:

* a committed snapshot exposes dom, retired, parent, requires, provides, and
  birth data rather than reading a mutable global registry during a proof;
* Precedes, ParentEdge, and SupportRel have explicit directions, with
  provider or parent pointing toward the dependent;
* SupportDep is the converse relation used for recursive descent or
  well-founded induction;
* SupportOperator is positive, SupportSet is its least fixed point or
  equivalently the intersection of prefixed sets, and monotonicity, leastness,
  and fixed-point facts are proved;
* a SupportOrder or rank certificate establishes well-foundedness of
  SupportDep on the relevant committed domain;
* support rank is not iterator rank;
* NoLateRegistration and CommittedSnapshot are explicit assumptions or
  boundaries, not facts silently inferred from a mutable registry.

Evidence dimensions remain separate. This lane targets source/ADR alignment
(A), interface elaboration (I), substantive checked theorems (K), and finite
examples (E). It does not claim a runtime adapter or concrete refinement
(R1+).

## 2. Entry gate and reproducible preflight

Create the execution branch from the commit containing all three parallel plan
files. Do not branch from an older P9 execution branch or from a sibling lane.

~~~bash
git fetch origin --prune
git switch -c <support-core-branch> origin/main
git status --short --branch
git log -1 --oneline

jq -e '
  .record_status == "accepted" and
  .architecture_status == "closed" and
  .formal_acceptance == true
' docs/blueprint/architecture-decision/status/ADR-09-accepted.json

lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
~~~

Before editing, read at least:

~~~text
AGENTS.md
README.md
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.md
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/status/Definition-Ledger.json
docs/blueprint/architecture-decision/md/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.md
docs/blueprint/architecture-decision/json/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.json
docs/blueprint/architecture-decision/status/ADR-09-accepted.json
docs/status/P9-handoff-report.md
STC/State/Like.lean
STC/State/RegistryLike.lean
STC/State/FinmapAdapter.lean
STC/Alpha/Core.lean
STC/Alpha/Transport.lean
~~~

## 3. Ownership and parallel-edit boundary

This lane owns only:

~~~text
STC/State/Support.lean
STC/Examples/Support.lean
docs/status/P11-support-core-handoff-report.md
docs/status/P11-support-core-scan-raw.txt
~~~

If a tiny internal split is essential, files may be added below
STC/State/Support/, but STC/State/Support.lean remains the public production
entry point and the handoff must justify the split.

This lane must not edit:

~~~text
STC/Control/**
STC/Staging/**
STC/Scoped/**
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/blueprint/**
AGENTS.md
README.md
docs/status/P8-conformance-manifest.json
~~~

It also must not change RawState, WellFormed, the existing registry API, the
coeffect store, or alpha-renaming primitives simply to make a support proof
shorter. Any truly necessary upstream change is a surfaced integration request,
not an opportunistic edit in this branch.

The Support production module must not import STC.Control or STC.Staging.
Enforce this with a raw import scan in addition to the normal build.

## 4. Intended public surface

Names may be adjusted to established repository style, but the concepts and
directions are fixed. Prefer an explicit, small public API resembling:

~~~lean
structure SupportSnapshot (N K : Type) where
  dom      : Finset N
  retired  : N → Bool
  parent   : N → Option N
  requires : N → Finset K
  provides : N → Finset K
  birth    : N → Nat

def Precedes (S : SupportSnapshot N K) (a b : N) : Prop := ...
def ParentEdge (S : SupportSnapshot N K) (a b : N) : Prop := ...
def SupportRel (S : SupportSnapshot N K) (a b : N) : Prop := ...
def SupportDep (S : SupportSnapshot N K) (b a : N) : Prop :=
  SupportRel S a b

def SupportOperator (S : SupportSnapshot N K) (A : Set N) : Set N := ...

def SupportSet (S : SupportSnapshot N K) : Set N := ...
~~~

The actual snapshot fields may use a finite-map representation or reuse
existing registry-facing types. However, the public meaning must stay
extensional and the committed data boundary must remain visible.

If conversion from an existing state or registry is needed, define a narrow
projection seam such as SupportSnapshot.ofState or SupportSnapshotOf. Do not
make SupportSet query mutable state at every unfolding, and do not cache the
closure inside RawState.

## 5. Task sequence

### T01 — Committed snapshot and directed relations

Implement the finite committed snapshot and state its invariants. At minimum:

* dom is the universe over which support obligations are interpreted;
* retired names and parent references have an explicit policy;
* requires and provides are finite at a snapshot;
* birth metadata is available for order/rank evidence;
* NoLateRegistration states the freeze boundary needed by later theorems.

Define Precedes, ParentEdge, SupportRel, and SupportDep with one unambiguous
orientation. Provider-to-dependent and parent-to-dependent are the forward
support directions. The converse is named SupportDep; do not overload one
relation and reverse arguments informally from theorem to theorem.

Prove basic membership and domain lemmas, including whichever endpoint-domain
facts the accepted ADR requires. If retired objects are excluded, prove the
exclusion. If they remain readable in a committed snapshot, separate readable
presence from eligibility for new support edges.

### T02 — Positive closure operator and least fixed point

Define SupportOperator using only positive occurrences of its recursive set
argument. Prove:

* monotonicity;
* the exact membership clause for domain, retirement, parent support, and
  provision of every required key;
* SupportSet is a prefixed point;
* leastness among all prefixed points;
* the accepted fixed-point equality or pair of inclusions.

Use the repository's available order/fixed-point library where it improves the
proof boundary. Do not hide positivity in an opaque executable loop and then
label finite termination as least-fixed-point evidence. An executable finite
closure may be added for E evidence, but it is not the definition of the
mathematical LFP unless its equivalence is proved.

### T03 — Support order and well-foundedness

Introduce the accepted SupportOrder or equivalent rank certificate. Its laws
must connect every SupportRel edge to a strict change in a well-founded measure
with the orientation needed for SupportDep recursion.

Deliver a genuine WellFounded theorem for SupportDep, normally restricted to
the committed domain or encoded through a subtype. A theorem excluding only
self-loops or two-cycles is insufficient. The result should support Lean
well-founded induction in downstream proofs.

Keep names and types distinct from RankedIterator and iterator rank. A shared
natural-number codomain is harmless; a shared semantic concept is not.

The theorem statement must expose the assumptions actually used, such as
NoLateRegistration, birth monotonicity, parent discipline, or a supplied order
certificate. Do not infer these from unrelated WellFormed facts.

### T04 — Profiles, examples, and negative evidence

Provide small finite snapshots covering:

* a parent dependency;
* a provider dependency;
* a nontrivial canonical support closure generated by the positive clause;
* a valid order certificate and usable well-founded induction;
* the shorthand acyclicity counterexample discussed by ADR-09.

Be precise about the counterexample. If a cycle requires an additional edge
such as n to r, include it explicitly. Do not present a graph-theoretic model
as a reachable lifecycle trace unless reachability has actually been proved.

Executable examples must be deterministic and finite. Keep E evidence labelled
as E; it supplements but does not replace the K theorems from T02 and T03.

### T05 — Projection and alpha-transport seam

Connect support snapshots to the already accepted state and alpha-renaming
architecture without modifying either architecture. Prove the strongest
reasonable extensional transport statements available at this layer:

* renaming the name component preserves Precedes and ParentEdge;
* SupportRel and SupportDep commute with the induced permutation;
* SupportSet membership transports between renamed snapshots;
* existence of a SupportOrder or WellFounded certificate transports.

Keys remain fixed unless the existing alpha architecture explicitly renames
them. A particular numeric rank assignment need not be invariant; transport of
the certified ordering property is the semantic requirement.

If the existing alpha API cannot express a theorem without an upstream change,
record the exact missing signature and a minimal proposed adapter in the
handoff. Do not edit Alpha production files in this lane.

### T06 — Freeze the core API and package evidence

Once T01–T05 build, freeze the names and signatures required by the later
trace-facing join. Add doc comments for direction-sensitive relations and for
the distinction between snapshot birth/support rank and iterator rank.

The handoff must contain:

* the exact public declarations and module import path;
* theorem names classified as A/I/K/E;
* all assumptions on committed snapshots and no-late-registration;
* the SupportRel and SupportDep orientation in prose and notation;
* the exact unresolved interface, if any;
* proposed Definition Ledger deltas;
* commands run and their raw results;
* the commit hash and clean-tree status.

## 6. Explicitly deferred trace-facing join

The following Definition Ledger rows or theorem families are not owned by this
parallel core lane when they require production Control traces:

~~~text
L68
L70
L72
T73
~~~

The precise row meanings remain those in the current ledger. This list is a
dependency boundary, not permission to reinterpret the rows. After both the
Support Core and Control/Staging branches merge, a small integration plan may
instantiate these claims using the frozen APIs.

The integration work may import Support from Control-facing proof modules. The
Support core itself must remain import-independent from Control and Staging so
that its graph and well-foundedness theory is reusable.

## 7. Definition Ledger handling

Do not edit docs/status/Definition-Ledger.json in this parallel branch. The
handoff proposes exact deltas for central integration after all lanes merge.

Expected candidates include D67 and the support-core portions of the accepted
ADR-09 family. For each proposed row update record:

* current status and proposed status;
* delivery classification;
* Lean symbol and file;
* evidence dimension;
* theorem strength and assumptions;
* any deferred_reason that remains.

Dependency-blocked trace rows remain planned with an explicit deferred_reason
until their Control-facing proofs exist. Use delivery = deferred only when the
repository's post-P9 ledger policy explicitly chooses that convention; do not
mix the two encodings inside this plan's proposed patch.

## 8. Required validation

Run at minimum:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Support.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Support.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC

rg -n '^import .*Control|^import .*Staging|STC\.Control|STC\.Staging' \
  STC/State/Support.lean STC/State/Support STC/Examples/Support.lean

rg -n 'sorry|admit|axiom' STC/State/Support.lean STC/State/Support \
  STC/Examples/Support.lean

git diff --check
git status --short
~~~

Adjust the rg scan paths if no internal Support directory was created. Any
match must be explained; production imports of historical spike modules are a
hard failure. A newly introduced axiom, sorry, or admit is a hard failure unless
it is already part of an explicitly accepted repository policy and is
documented as such. For scripts/scan_lean.py, exit 1 means clean, exit 0 means a
lexical match requiring classification, and exit 2 means a scan failure.

Also retain the raw scan output in
docs/status/P11-support-core-scan-raw.txt. The handoff must distinguish a clean
scan from a scan that produced reviewed false positives.

## 9. Acceptance criteria

P11 Support Core is complete only when all of the following hold:

1. ADR-09 has an accepted P9 status record at the execution baseline.
2. The Support production API elaborates without importing Control or Staging.
3. The committed snapshot boundary and NoLateRegistration assumptions are
   explicit.
4. SupportRel and SupportDep have one documented, theorem-consistent direction.
5. SupportOperator is proved monotone and SupportSet satisfies the accepted
   LFP leastness and fixed-point properties.
6. A genuine WellFounded theorem is available for the relevant SupportDep
   relation, not merely a local acyclicity result.
7. Support rank remains semantically separate from iterator rank.
8. Finite examples cover parent, provider, transitive closure, and a negative
   graph profile without overstating reachability.
9. Alpha transport or an exact minimal blocked seam is documented.
10. Trace-facing rows remain out of this branch.
11. The full build and repository validators pass.
12. The handoff proposes, but does not race to edit, central ledger metadata.

## 10. Reopen and stop rules

Stop and reopen planning rather than improvising if any of these occur:

* the accepted ADR-09 record is missing or no longer formally accepted;
* implementation requires a second mutable registry or cached support field in
  RawState;
* the LFP cannot be stated positively with the accepted relation direction;
* well-foundedness requires an assumption not represented in ADR-09;
* production Support must import unfinished Control/Staging code;
* alpha transport requires changing the accepted alpha architecture;
* a claimed K theorem is supported only by finite computation;
* the lane needs to edit a shared integration path owned outside this plan.

The reopen report must identify the smallest conflicting signature or law and
classify the issue as source ambiguity, ADR inconsistency, Lean engineering, or
integration ordering.

## 11. Merge and downstream handoff

Commit this lane independently after all gates pass. It may merge in any order
relative to the Control/Staging and Scoped lanes because it owns disjoint files
and consumes only pre-existing accepted APIs.

After merge, retain two distinct facts:

* Support Core is production-ready and usable without Control.
* Trace-facing support integration is still pending until the Control API has
  also merged and the dedicated join plan is executed.

That join, not this branch, is allowed to connect Support well-foundedness to
Control trace theorems and to propose completion of L68/L70/L72/T73.
