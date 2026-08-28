# DeepSeek Harness ADR-07: Control, Nondeterminism, Asynchrony, and Failure

| Field | Value |
|---|---|
| Packet ID | ADR-07 |
| Title | Control, nondeterminism, asynchrony, and failure |
| Status | Proposed architecture closure; compiler validation pending |
| Packet version | 0.1.1-proposed |
| Date | 2026-08-28 |
| Resolves | BD-CONTROL at the architecture/interface level |
| Semantic change | None to the frozen paper, H03/H04, or accepted ADRs |
| Depends on | ADR-03 closure, ADR-04, ADR-05, ADR-06 closure; P3/P4/P5 APIs when instantiated |
| Namespace | STC for production; STCADR07 for this standalone spike |

This packet fixes the control boundary needed by Section 4 without pretending that its
concrete lifecycle guards or global theorems are already implemented. It is deliberately
an architecture packet: a compiling spike below demonstrates that the chosen carriers and
relations are well formed, but it does not prove the full lifecycle calculus.

## 1. Decision summary

The formal target uses one state carrier with two explicitly different classes of step:

1. an orchestration step is an external input chosen by the orchestrator; and
2. a lifecycle step is an internal transition enabled by the current state.

The two relations are not merged into an unlabelled transition relation. A labelled step
is their typed sum, and its constructor carries the rule label together with a proof that
the corresponding relation holds. This makes nondeterministic choices explicit while
remaining independent of a scheduler.

The state observed by control contains:

* the ADR-03 raw/valid state interface (represented abstractly here by S);
* trace metadata, including the ADR-04 freshness ledger at the orchestration boundary;
* a lifecycle mode and optional in-flight snapshot; and
* an optional per-fiber outcome.

An InFlight record stores the acting incarnation, launch/committed view, remaining
iterator code, successful-prefix accumulator token, and an explicit landing witness.
The landing witness binds an abstract future/task token to a predicate over the current
state; it is the contract that makes `mustLand` refer to the operation launched in this
snapshot rather than to an unrelated scheduler event. It is a control wrapper, not an
additional mutable root store and not a replacement for the ADR-03 RawState registry.

Asynchrony is represented by an explicit landing policy. An in-flight operation may land
after the raw state or target view has changed. The policy requires landing to remain
admissible and permits abort only at an explicit iterator boundary. No scheduler or
promise implementation is assumed by the metatheory.

Failure is carried by the existing P4-shaped Failure and ExecResult contract. The
L-Raise label carries the complete failure payload (error, boundary, and prefix undo);
failure is not Option.none, an identity transition, or an invented state rewrite.

## 2. Scope and non-goals

This packet closes the shared control interfaces and their admissibility conditions. It
does not yet:

* choose the concrete provider, target, or WellFormed predicates;
* decide the base-versus-extended staging correspondence (BD-STAGING);
* prove the support recursion or confluence envelope (BD-SUPPORT);
* instantiate name-bearing payload actions or a Cordis runtime refinement;
* prove every Section 4 guard, preservation theorem, or progress theorem; or
* modify production STC modules, the Definition Ledger, Bootstrap, H03/H04, or accepted
  ADR artifacts.

In particular, “BD-CONTROL closed” below means that later modules no longer need to
invent a control carrier or silently choose between external and internal steps. Concrete
rule proofs remain implementation obligations with their evidence classified separately.

## 3. Normative control architecture

### 3.1 Control state and in-flight snapshot

The production state is parameterized rather than hard-coded to a particular registry:

~~~text
ControlState S Meta Incarnation Q View Future Error Accumulator
  raw       : S
  meta      : Meta
  mode      : Inactive | Reloading | Active | Unloading
  inFlight  : Option (InFlight Incarnation S Q View Future Accumulator)
  outcome   : Option Error
~~~

The mode is a control observation. The raw state S is where the ADR-03 registry and
ambient data live; Meta is where allocation history and trace labels live. A concrete
multi-fiber implementation may store one such control payload in each fiber cell or
use a finite map of them, but it must preserve the same separation.

~~~text
InFlight Incarnation S Q View Future Accumulator
  owner      : Incarnation
  launch     : S
  committed  : View
  remaining  : Q
  prefixUndo : Accumulator

LandingWitness S Future
  future      : Future
  admissible  : S → Prop
~~~

The launch state and committed view are snapshots for the transition in progress. They
are not recomputed from the changed target at landing time. The accumulator denotes the
successful prefix only; its interpretation is supplied by the P4 iterator/effect layer.
`remaining` is an iterator/code cursor, not the future token itself; the separate
`landingWitness` field is therefore mandatory at the architecture boundary.

No unrestricted state transformer is stored in an ADR-03 registry cell. If the selected
P4 specialization uses S → S as its accumulator, that function is a control/iterator
payload and its relation/properness laws remain explicit.

### 3.2 Two labelled relations

The external labels are:

~~~text
O-Insert  (fresh incarnation, component payload)
O-Retire  (incarnation)
O-Remove  (incarnation)
~~~

The internal labels are:

~~~text
L-Begin   (incarnation, target view)
L-Iter    (incarnation, next iterator code)
L-Finish  (incarnation)
L-Divert  (incarnation, abort-or-land choice)
L-Raise   (incarnation, complete Failure payload)
L-Leave   (incarnation)
L-Unload  (incarnation)
~~~

The exact payload types may be specialized by the lifecycle implementation, but every
label must retain the witness needed by its rule. In particular:

* O-Insert carries the allocated identity and its component payload;
* O-Retire and O-Remove carry the identity they target;
* L-Begin carries the committed target view selected by that run;
* L-Iter carries the selected continuation code;
* L-Divert carries whether the in-flight stage aborts or lands; and
* L-Raise carries Error, boundary state, and prefixUndo together.

The semantics are relations:

~~~text
orchestration : OrchestrationLabel → ControlState → ControlState → Prop
lifecycle     : LifecycleLabel     → ControlState → ControlState → Prop
~~~

The relation may have more than one successor for a state and label. A runtime scheduler
is not part of the abstract semantics; any sequence of relation witnesses is an admissible
candidate trace once the trace policy below accepts it.

### 3.3 Typed step witnesses

The canonical step is a sum of the two relation classes:

~~~text
Step
  | orchestration (label) (premise : orchestration label before after)
  | lifecycle     (label) (premise : lifecycle label before after)
~~~

Because the before and after states index Step, a proof cannot silently use an
orchestration premise as a lifecycle premise or drop the rule label. This is the
minimal witness-carrying nondeterminism needed by L55, L59, L71, and the later trace
theorems.

### 3.4 Trace, admissibility, and maximal lifecycle suffix

Traces are finite indexed lists of typed steps:

~~~text
Trace.nil  : Trace s s
Trace.cons : Step s t → Trace t u → Trace s u
~~~

Every step already contains its local rule premise. A TracePolicy adds the boundary
conditions that are not local to a single state transition:

* the initial metadata condition;
* freshness/ledger monotonicity for orchestration labels;
* host/inertia admissibility for landing labels; and
* any chosen reachability envelope.

The executable interface has an explicit state-dependent hook in addition to the label
filter:

~~~text
TracePolicy:
  initial : Meta → Prop
  labelOk : List (OrchestrationLabel ⊎ LifecycleLabel) → Bool
  stepOk  : ∀ meta, Step before after → Prop
~~~

`Trace.admissible` requires `initial`, the boolean label filter, and `stepOk` for every
typed step. The standalone spike instantiates `stepOk` with `True` only as a neutral
architecture example; concrete freshness, landing, host, and reachability guards must
be supplied by the production policy.

An admissible trace is a finite trace satisfying both the typed step witnesses and the
TracePolicy. No claim is made that every runtime schedule is finite; the finite carrier is
the theorem-facing trace fragment used by the current blueprint.

A lifecycle-only suffix is a trace whose every step is a lifecycle constructor. It is
maximal when its endpoint has no lifecycle successor under the supplied lifecycle
relation:

~~~text
LifecycleOnly trace ∧ ¬ ∃ next, LifecycleStep endpoint next
~~~

This definition does not confuse “maximal lifecycle suffix” with “the whole execution”.
External orchestration inputs may occur before or after such a suffix.

## 4. Asynchrony and inertia

The paper describes inertia as a restriction on which L-Divert alternative may be taken.
The repaired interface makes the restriction visible without adding a scheduler:

~~~text
AsyncPolicy:
  allowed     : InFlight → ControlState → LandingChoice → Prop
  landingWitness : InFlight → ControlState → Prop
  mustLand    : ∀ flight state, allowed flight state Land
  landSound   : ∀ flight state, allowed flight state Land →
                landingWitness flight state
  abortGuard  : ∀ flight state, allowed flight state Abort → AtBoundary flight state
~~~

Thus, if an iteration is in flight and is not at a declared iterator boundary, an
aborting L-Divert is not admissible; the landing alternative remains available even when
the target view changed. At a boundary, either alternative may be admitted by a concrete
policy. A landing step uses the committed snapshot in InFlight and then routes through
the ordinary lifecycle/unload protocol. `landSound` connects the policy-level landing
choice to the `InFlight.landingWitness` supplied by the launched operation; no concrete
promise or scheduler is required at this layer.

The policy is intentionally abstract about Future, promises, and host event queues.
A host/refinement artifact may implement it with a task handle, but must prove that the
handle and its landing witness satisfy the same allowed/mustLand/landSound/abortGuard
contract.

## 5. Failure bridge and L-Raise

The control layer reuses the P4 result shape:

~~~text
Failure S Error
  error      : Error
  boundary   : S
  prefixUndo : S → S

ExecResult S Error
  | success (EffectResult S)
  | failure (Failure S Error)
~~~

The concrete production declarations come from STC.Foundation.Result and P4's iterator
module. The spike mirrors them in its own namespace solely to keep the packet standalone.

L-Raise is available only from a failure result. Its label carries the complete Failure
record. The transition first schedules the successful-prefix undo through the unloading
path and records the error in the inactive outcome; it does not retry L-Begin from the
error outcome. A bridge must preserve all three fields:

~~~text
raiseFromExec (.failure f) = L-Raise owner f
raiseFromExec (.success r) = no L-Raise label
~~~

An implementation may choose a richer error relation for observational transport, but
it must not erase error, boundary, or prefixUndo merely to fit a success-only relation.

## 6. Freshness and the two-state boundary

ADR-04 places everIssued and allocation history at the orchestration/trace boundary.
Accordingly:

* O-Insert observes (RawState, TraceMeta), not RawState alone;
* an insertion label carries the fresh IncarnationId it allocates;
* retirement/removal may delete the current registry entry but never erase the ledger;
* lifecycle steps that do not inspect freshness may be stated over RawState; and
* if a unified Step relation includes allocation, its observation and trace policy include
  the metadata component.

This keeps freshness-sensitive rule applicability Markovian without polluting the default
CoreStateObs projection.

## 7. Consequences for downstream rows

The packet supplies the architecture needed to begin the following rows, but does not
claim their proofs:

| Row | Architecture supplied here | Remaining obligation |
|---|---|---|
| D47 | Fresh insertion/retirement labels and witness boundary | ADR-03/NAMES concrete registration and inverse laws |
| D49 | Explicit mode, in-flight, and outcome slots | STAGING concrete lifecycle datatype and guards |
| D53 | Indexed labelled traces and separate step classes | Concrete state relations and episode definitions |
| L54 | Rule labels expose write/read cases | Per-constructor frame lemmas |
| L55 | Same-label witness transport boundary | Relation-respect proofs for every concrete rule |
| L57 | Explicit control payload supports vestigial erasure | Erasure/preservation proofs |
| D60 | Continuation payload and control relation are explicit | Reach-closed generated monoid and independence |
| T61/C62 | Episode and unload boundaries are representable | Recovery proofs under P3/P4 and concrete rules |
| T63 | Reliance guard has a lifecycle-step home | Provider/consumer proof |
| T64 | Landing and committed snapshot are visible | Resolution-coherence proof |
| T66 | Lifecycle-only maximal suffix is definable | Progress, finite-name, and rank hypotheses |
| L71 | Adjacent labelled steps can be compared | Independence/diamond hypotheses |
| R.fail | L-Raise carries complete failure result | P4 execution and lifecycle integration |
| R.full/Table1 | One authoritative labelled relation can host subfamilies | STAGING/control implementation and derived write facts |

Rows L72 and T73 still retain BD-SUPPORT in addition to their control dependencies.
R.base still retains BD-STAGING. D29/D31 retain BD-SCOPED.

## 8. Ownership and integration rules

The ADR-07 author owns only this packet and its standalone spike. The packet must not
edit:

~~~text
STC/ production modules
STC.lean or STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/*-scan-raw.txt or *-handoff-report.md
docs/blueprint/baseline/
docs/blueprint/architecture-decision/json/ (accepted ADRs)
historical ADR spikes
~~~

After P3, P4, and P5 handoffs, an integration owner may instantiate the abstract labels
against the production Failure, ExecResult, iterator, and state APIs. That integration
must preserve this two-relation boundary and record evidence separately:

* A: paper/ADR alignment and repair rationale;
* I: interface/elaboration;
* K: checked guard, preservation, recovery, or progress theorem;
* E: finite trace execution;
* R0: abstraction/refinement seam only; and
* R1+: concrete runtime simulation.

## 9. Acceptance and reopen policy

Architecture-level acceptance requires:

1. the standalone spike compiles with no errors and no proof placeholders;
2. the spike has a nonempty finite positive trace and a negative check showing that a
   wrong class or forbidden abort is rejected;
3. the failure bridge preserves error, boundary, and prefixUndo;
4. the in-flight policy makes landing mandatory, ties landing to an explicit witness,
   and keeps abort boundary-guarded;
5. no frozen input, accepted ADR, or production module is modified; and
6. concrete guard/proof obligations remain listed rather than hidden in a broad invariant.

The packet must be superseded by a new ADR if a later implementation changes any of:

* the distinction between orchestration and lifecycle relations;
* the explicit in-flight snapshot or failure payload;
* the finite trace/maximality meaning; or
* the placement of freshness metadata.

Adding concrete rule constructors, provider predicates, or proof lemmas within this
boundary is not a semantic change and may proceed in downstream implementation tasks.
