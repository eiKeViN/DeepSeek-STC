# DeepSeek Harness ADR-08: Base/Extended Staging Architecture

| Field | Value |
|---|---|
| Packet ID | ADR-08 |
| Title | Base/extended staging through one authoritative labelled relation |
| Status | Proposed architecture closure — compiler validated (formal acceptance pending) |
| Packet version | 0.1-proposed-compiler-validated |
| Date | 2026-08-28 |
| Resolves | BD-STAGING at the architecture/interface level only |
| Semantic change | None to the paper, frozen H03/H04, or accepted ADRs |
| Depends on | ADR-01/02/03/04/05/06; ADR-07 control interfaces when instantiated |
| Namespace | STCADR08 in this standalone spike; production target remains STC |
| Companion files | DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.json; DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture-Spike.lean |
| Formal acceptance | `false`; no explicit lead acceptance record |

## 1. Decision summary

The extended labelled semantics R+ is the single authoritative transition relation.
The base relation Rb is not a second independently maintained calculus and is not
obtained by taking an arbitrary subrelation of R+. Instead, Rb is a derived
AtomicProfile-controlled view: one base-labelled step denotes a finite, named macro path
of R+ steps whose endpoints lie in the stable/base image.

The architecture therefore has three layers:

1. R+ records every authoritative orchestration and lifecycle label and its local
   premises.
2. An embedding embed : BaseState -> ExtendedState and partial projection
   project : ExtendedState -> Option BaseState identify the stable image.
3. AtomicProfile specifies which full paths count as one atomic base step. The derived
   relation Rb is defined by those paths, together with an optional stuttering identity
   case where the base view does not change.

This preserves the H04 disposition of R.base as SUBSUMED/specialization: the base
calculus is recoverable by a proved macro/view and simulation contract, without duplicating
the global metatheory.

This packet is an architecture closure, not a claim that BD-STAGING is fully proved.
Concrete K, guard, WellFormed, provider, control, and support obligations remain owned by
their respective modules and blockers.

## 2. Why a direct subrelation is insufficient

The printed base lifecycle rules are atomic while the extended rules expose intermediate
states. In particular:

* base L-Reload corresponds to L-Begin followed by L-Finish;
* base L-Unload corresponds to L-Leave followed by L-Unload;
* the intermediate Reloading and Unloading states are not base states.

Consequently, filtering R+ to transitions whose endpoints project to base states either
loses the lifecycle steps or accidentally admits unrelated full paths. A direct
subrelation also cannot state the conditions under which an arbitrary multi-step path is
one atomic base action. AtomicProfile supplies those conditions explicitly.

Orchestration labels may be one-step macros in the initial profile; the interface does not
assume that all future profiles have that shape. A lifecycle macro must retain its exact
ordered labels, endpoint witness, and stable-image condition.

## 3. Normative carriers and relations

The production interfaces are parameterized by state and label types. The standalone
spike mirrors only these interfaces and does not import or redeclare production modules.

    R+_orch : FullOrchLabel -> ExtendedState -> ExtendedState -> Prop
    R+_life : FullLifeLabel -> ExtendedState -> ExtendedState -> Prop

The two relation classes remain distinct, as required by ADR-07. A labelled full step
may be represented by their typed sum in the control module; this packet only requires
the two projections.

    embed   : BaseState -> ExtendedState
    project : ExtendedState -> Option BaseState
    stable  : ExtendedState -> Prop

The embedding laws are:

    project (embed b) = some b
    stable (embed b)

The converse project x = some b -> x = embed b is deliberately not assumed globally:
an implementation may choose a canonicalization or quotient-like stable view. If a
concrete model needs this stronger property, it must state and prove it as an additional
profile field rather than smuggling it into stable.

## 4. Derived base view

### 4.1 Atomic profile

For an orchestration or lifecycle base label, AtomicProfile provides:

* a finite expansion list of full labels;
* an atomicity predicate over that list;
* endpoint stability and projection/embedding witnesses;
* no interleaved external orchestration step;
* no unaccounted yield, raise, or asynchronous landing branch;
* the guard/confinement premise required by the corresponding full rules.

The exact guard and WellFormed predicates are parameters of the later control/state
modules. This packet names their ports but does not choose their definitions.

### 4.2 Macro relation

For a base lifecycle label l, base states b and b', the derived macro relation is:

    Rb_life l b b' :=
      AtomicProfile.life l
      and Trace (fun fullLabel => R+_life fullLabel) (embed b) (expandLife l) (embed b')

The orchestration case is:

    Rb_orch l b b' :=
      AtomicProfile.orch l
      and Trace (fun fullLabel => R+_orch fullLabel) (embed b) (expandOrch l) (embed b')

A concrete profile
may add a stuttering branch b = b' for a no-op atomic action; it must be tagged and
proved separately. It may not identify a failing or unfinished full path with a
successful base step.

The finite Trace carrier is theorem-facing. If a host later supplies infinite traces,
the host/refinement layer must provide a separate productivity/boundedness argument; no
coinductive semantics is silently introduced here.

### 4.3 Base quiescence and stable image

Base quiescence is a view predicate, not a second transition relation:

    quietBase b := stable (embed b) and
                 no admissible base macro from b

Full quiescence is evaluated in R+ under the selected control/profile policy. The bridge
is only claimed on the stable image:

    quietFull (embed b)  <->  quietBase b

when the profile supplies:

* stable-image closure for each accepted macro;
* completeness of the atomic macro partition for the full lifecycle paths considered;
* no pending in-flight/failure branch at the endpoint; and
* matching guard and provider/WF premises.

Outside that profile, quietBase is not a shortcut for full quiescence.

## 5. Correspondence contracts

### 5.1 Forward simulation

ForwardSimulation is the primary direction. Every base step is mapped to the declared
full macro with the same endpoint embedding:

      Rb_orch l b b' -> Trace (fun fullLabel => R+_orch fullLabel) (embed b) (expandOrch l) (embed b')
      Rb_life l b b' -> Trace (fun fullLabel => R+_life fullLabel) (embed b) (expandLife l) (embed b')

The trace labels are part of the witness; endpoint equality alone is insufficient.
Concatenating base traces therefore maps to concatenated full traces by the ordinary
Trace.append lemma. No duplicate base proof of recovery, equivalence, alpha transport,
or control admissibility is introduced.

### 5.2 Atomic adequacy / stuttering converse

The converse is intentionally weaker and profile-relative. For an AtomicProfile
accepted full path between embedded endpoints, AtomicAdequacy yields either:

* the corresponding base label and expansion witness; or
* a permitted stuttering identity (b = b') explicitly marked by the profile.

The converse does not classify arbitrary multi-step full traces. Paths containing
interleaved orchestration, a failure, a pending asynchronous branch, or a non-atomic
yield are outside the adequacy premise. This prevents a false claim that every full
trace is one base step.

### 5.3 Embedding/project round trips

At minimum the interface proves:

    project (embed b) = some b

and provides stable (embed b). A projection theorem for a full macro is only stated
under project/stable hypotheses. No global inverse of embed is required.

## 6. Concrete atomic profile retained from the paper

The initial profile records the paper's lifecycle correspondence:

| Base label | Full expansion | Intermediate state | Atomicity condition |
|---|---|---|---|
| L-Reload | L-Begin ; L-Finish | Reloading | committed target, one finite iterator stage, no interleaving/failure |
| L-Unload | L-Leave ; L-Unload | Unloading | retirement/withdrawal guard, stable endpoint, no interleaving/failure |

The base orchestration labels O-Insert, O-Retire, and O-Remove may initially expand
to singleton full labels. Their freshness, parent, and frame premises come from ADR-04,
ADR-03, and ADR-07; this packet does not restate those laws.

The words “one finite iterator stage” are a profile port, not a decision about the
concrete iterator implementation. ADR-05's ranked machine supplies the eventual
termination evidence.

The standalone toy profile is intentionally non-degenerate: orchestration labels are
accepted only at their declared lifecycle endpoints, and the atomicity predicate rejects
an extra/interleaved label or a failure label. These are finite negative checks on the
macro boundary, not claims about the full calculus.

## 7. Ownership and boundaries

| Obligation | Owner | This packet |
|---|---|---|
| authoritative full labelled relation and typed step witnesses | ADR-07 / control | consumes interface |
| ranked finite iterator and failure payload | ADR-05 / P4 | consumes interface |
| raw/valid state, provider and static-field invariants | ADR-03 / P5 | names ports only |
| identity, freshness, and alpha action | ADR-04 / P6 | requires label transport later |
| relation/effect/observation contracts | ADR-01/06 / P1-P3 | reuses, no duplicate theory |
| concrete guard and WF proofs | state/control implementation | deferred |
| support, confluence, and runtime refinement | ADR-09+, P5/P8 | deferred |

The packet neither changes the frozen H03 graph/H04 disposition nor updates status,
Blueprint, Ledger, Bootstrap, or production STC files. STC.Adapter remains the one-way
refinement seam; Cordis names remain reserved for a future runtime project.

## 8. Readiness effect and non-claims

At the architecture level, BD-STAGING has a named solution and can be removed from
future interface-design ambiguity once this packet is accepted. It is not evidence that
the following are already proved:

* concrete R+ constructors and all ten paper rules;
* K-level forward simulation for every guard;
* WellFormed preservation or provider uniqueness;
* lifecycle progress, support well-foundedness, confluence, or asynchronous inertia;
* the exact Section-4 quiescence theorem;
* a refinement theorem for Cordis code.

Readiness reports should therefore distinguish architecture_closed from
implementation_proved. The H04 R.base row remains SUBSUMED/specialization; no
second base relation should be added to the global metatheory.

## 9. Acceptance and reopen rules

The architecture packet is accepted when the Markdown, JSON, and spike agree on:

1. R+ as the unique authoritative relation;
2. Rb as an AtomicProfile-controlled finite macro/view;
3. explicit embed/project and stable-image laws;
4. forward simulation and atomic adequacy/stuttering-converse interfaces; and
5. no claim of concrete K/WF/guard or full BD-STAGING closure.

Reopen this decision only if a concrete full relation cannot expose ordered lifecycle
labels, if an accepted macro is not finite/atomic under the declared profile, or if a
proof requires a second independently maintained base calculus. Such a finding must be
recorded as a superseding ADR rather than silently changing this packet.

## 10. Validation evidence

The spike is a standalone compiler target in namespace STCADR08; it uses no historical
spike imports and contains no sorry, admit, project-defined axiom, or unsafe.
The intended command is:

    lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture-Spike.lean

The repaired spike was independently checked on 2026-08-28 with the pinned Lean 4.33.0 /
Mathlib v4.33.0 command above: it exited 0 with zero warnings.  This is compiler/interface
evidence only.  The packet remains proposed, `full_bd_staging_closed` remains false, and
formal acceptance, production integration, concrete `K` proofs, guards, and runtime
refinement remain separate gates.  JSON syntax and lexical placeholder checks are also
performed locally before handoff.
