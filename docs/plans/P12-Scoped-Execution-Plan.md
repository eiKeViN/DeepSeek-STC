# STC P12 Scoped Execution Plan

| Field | Value |
|---|---|
| Plan ID | DH-P12-SCOPED-EXEC-01 |
| Repository | https://github.com/eiKeViN/DeepSeek-STC |
| Prepared | 2026-08-29 |
| Planning baseline | origin/main at 2f83afb, post-P9 merge |
| Depends on | P8 complete; P9 complete; ADR-10 accepted; P5 coeffect store stable |
| Scope | typed realms, finite resolution, scoped store adapter, metadata and context laws |
| Ownership | one independent lane; no dependency on Control, Staging, or Support Core |
| Namespace | STC.Scoped, adapting STC.Coeffect.Store |
| Status | ready to schedule from the common post-planning merge |

This lane implements the accepted ADR-10 scoped-coeffect architecture as a
typed layer over the existing P5 dependent coeffect store. It adds typed realm
references, finite resolution, scoped lookup/update operations, metadata
precedence, interception and persistent context derivation, plus the accepted
one-way flat embedding.

The existing STC.Coeffect.Store remains the authoritative physical store. P12
must adapt it rather than duplicate it or redesign P5. The lane is therefore
independent of P10 Control, P11 Staging, and P11 Support Core and can execute in
parallel from the same post-planning commit.

## 1. Authority and accepted-decision baseline

The paper remains authoritative for literal source claims. Frozen H03/H04 and
the Formal Reference preserve audited provenance and source defects. The
repaired production target for this lane is governed by accepted ADR-01 through
ADR-10, especially:

~~~text
docs/blueprint/architecture-decision/status/ADR-10-accepted.json
~~~

The P9 status record reports record_status = accepted,
architecture_status = closed, and formal_acceptance = true. Older candidate
ADR packets, historical spikes, and the P8 manifest retain their earlier
pre-P9 wording as provenance. If Blueprint, AGENTS, README, a candidate packet,
or P8 still says proposed or acceptance_pending, the later P9 status record and
docs/status/P9-handoff-report.md govern current architecture status.

The accepted ADR-10 boundaries are:

* RealmModel provides a typed logical-key family and RealmRef packages a key
  with its realm while retaining safe casts and a default reference;
* ResolverSpec is the relational contract; executable Resolver has finite
  support and is connected to the specification;
* ResolverUpdate changes the resolver through an explicit finite operation;
* RealmStoreOps and scopedLookup/scopedInsert/scopedErase operate through a
  typed adapter to the existing coeffect store;
* PhysicalDistinct is stronger than mere logical key inequality;
* MetaAlgebra and MetadataPrecedence state merge behavior explicitly;
* InterceptionSpec, ScopedContext, deriveIsolate, deriveIntercept, and
  ProviderAdapter preserve the accepted persistent-context boundary;
* FlatEmbedding is one-way. No arbitrary structured-to-flat converse is
  assumed or manufactured.

This lane targets A/I/K/E evidence. It does not claim a Cordis runtime,
Section-4 global metatheory, or R1+ refinement.

## 2. Entry gate and reproducible preflight

Create the execution branch from the commit containing all three parallel plan
files. Do not branch from an older P9 execution branch or a sibling lane.

~~~bash
git fetch origin --prune
git switch -c <scoped-branch> origin/main
git status --short --branch
git log -1 --oneline

jq -e '
  .record_status == "accepted" and
  .architecture_status == "closed" and
  .formal_acceptance == true
' docs/blueprint/architecture-decision/status/ADR-10-accepted.json

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
docs/blueprint/architecture-decision/md/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.md
docs/blueprint/architecture-decision/json/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.json
docs/blueprint/architecture-decision/status/ADR-10-accepted.json
docs/status/P9-handoff-report.md
STC/State/CoeffectStore.lean
STC/State/FinmapAdapter.lean
STC/State/Like.lean
STC/Foundation/Result.lean
~~~

## 3. Ownership and parallel-edit boundary

This lane owns:

~~~text
STC/Scoped.lean
STC/Scoped/Model.lean
STC/Scoped/Resolver.lean
STC/Scoped/Store.lean
STC/Scoped/Context.lean
STC/Scoped/Flat.lean
STC/Examples/Scoped.lean
docs/status/P12-scoped-handoff-report.md
docs/status/P12-scoped-scan-raw.txt
~~~

Minor file consolidation is allowed if it yields a smaller dependency graph,
but STC/Scoped.lean must be the public umbrella for this family and the handoff
must list the actual module graph.

This lane must not edit:

~~~text
STC/State/CoeffectStore.lean
STC/State/FinmapAdapter.lean
STC/Control/**
STC/Staging/**
STC/State/Support.lean
STC/State/Support/**
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/blueprint/**
AGENTS.md
README.md
docs/status/P8-conformance-manifest.json
~~~

Do not introduce a second authoritative store, change the P5 dependent Finmap
representation, or push realm information into the entire core state. Any
missing P5 law must be recorded as a minimal upstream request in the handoff;
it is not silently patched in this parallel branch.

## 4. Module and dependency shape

Use an acyclic production structure equivalent to:

~~~text
STC.Scoped.Model
        ↓
STC.Scoped.Resolver
        ↓
STC.Scoped.Store       imports STC.State.CoeffectStore
        ↓
STC.Scoped.Context
        ↓
STC.Scoped.Flat
        ↓
STC.Scoped             public umbrella
~~~

The exact imports may share Model directly, but later modules must not be
required to define earlier contracts. In particular, flat embedding is a
consumer of the structured scoped model, not its foundation.

STC/Examples/Scoped.lean is evidence and must not be imported by production
modules.

## 5. Intended public surface

Names may follow repository style, but the typed boundary should resemble:

~~~lean
structure RealmModel (K : Type u) (V : K → Type v) where
  Realm      : Type w
  keyOf      : Realm → K
  default    : (k : K) → Realm
  default_key : ∀ k, keyOf (default k) = k

structure RealmRef (M : RealmModel K V) (k : K) where
  token  : M.Realm
  key_eq : M.keyOf token = k

def RealmRef.defaultRef (M : RealmModel K V) (k : K) : RealmRef M k := ...

def ResolverSpec (M : RealmModel K V) :=
  (k : K) → RealmRef M k → Prop

structure Resolver (M : RealmModel K V) [DecidableEq K] where
  resolve      : (k : K) → RealmRef M k
  overrideKeys : Finset K
  finite_support : ∀ {k}, k ∉ overrideKeys →
    (resolve k).token = (RealmRef.defaultRef M k).token

def ResolverSatisfies (ρ : Resolver M) (spec : ResolverSpec M) : Prop :=
  ∀ k, spec k (ρ.resolve k)
~~~

Here K and V are explicit parameters, with V : K → Type. Lean details may
require decidable equality, sigma types, or dependent cast helpers. Those
requirements must appear in signatures or instances; they must not be hidden
behind unsafe casts or proof irrelevance assumptions stronger than needed.

The physical adapter should instantiate the P5 store at physical key type
M.Realm and value family fun r => V (M.keyOf r). It must retain enough token
equality or distinctness evidence to support the claimed frame laws.

## 6. Task sequence

### T01 — Realm model and typed references

Implement RealmModel and RealmRef with:

* the logical key type K and dependent value family V : K → Type;
* a physical realm token type M.Realm and its map M.keyOf : M.Realm → K;
* M.default, M.default_key, and RealmRef.defaultRef;
* typed equality/cast helpers sufficient for lookup and update;
* extensionality and simp lemmas that do not erase the dependency.

Prefer safe dependent equality elimination or existing sigma/equality APIs.
Do not use unsafe casts. Equality of logical keys alone must not imply equality
of realm references without the corresponding dependent evidence.

Provide finite toy instances showing at least two logical keys and multiple
realms for one key. This catches accidental collapse to a flat key type.

### T02 — Resolver specification and executable finite resolver

Separate the relational contract from its executable realization:

* ResolverSpec describes when a context/query resolves to a RealmRef;
* Resolver has finite support and a deterministic executable resolve function;
* a satisfaction theorem connects Resolver to ResolverSpec;
* ResolverUpdate performs an explicit finite override/update;
* update-hit, update-miss, support, and preservation laws are proved.

If ambiguity is allowed in ResolverSpec, state how the executable resolver
chooses or rejects it. Do not silently replace a relational source claim with a
deterministic function and call the two identical.

Finite support must be represented in data or proved from a concrete finite
map. A function accompanied only by an uncheckable prose assertion is not an
executable Resolver.

### T03 — Existing-store adapter and scoped operations

Define RealmStoreOps over the authoritative STC.Coeffect.Store from P5. Add:

* scopedLookup;
* scopedInsert;
* scopedErase;
* lookup-after-insert at the selected realm;
* frame laws for physically distinct references;
* erase laws and selected-reference restoration data where rollback needs it.

Instantiate or wrap the P5 store at the physical realm token type so that its
dependent family is:

~~~lean
STC.Coeffect.Store (fun r : M.Realm => V (M.keyOf r))
~~~

The adapter's RealmRef key_eq witness supplies the casts between the physical
value V (M.keyOf rr.token) and logical value V k. These cast laws must be proved
at the boundary. Do not duplicate the Finmap implementation.

PhysicalDistinct must express inequality of the selected physical realm
tokens. Logical-key inequality may imply token inequality because equal tokens
have equal keyOf images, but logical inequality is not the definition of
PhysicalDistinct and says nothing about two distinct tokens for the same key.

For update or erase operations intended to support undo, capture the resolved
RealmRef at operation time. Re-running a changed resolver during rollback is
not an admissible substitute unless an explicit stability theorem proves the
same result.

### T04 — Metadata, interception, and persistent contexts

Implement MetaAlgebra and MetadataPrecedence as separate contracts:

* algebraic metadata combination has its stated identity/associativity laws;
* precedence identifies which side wins on conflicting bindings;
* any right-biased override law is explicit and is not inferred merely from a
  generic monoid instance.

Define InterceptionSpec, ScopedContext, deriveIsolate, deriveIntercept, and
ProviderAdapter. Prove the accepted persistence laws:

* deriving a context does not mutate the parent context;
* isolation exposes only the intended resolver/store/metadata view;
* interception composes according to MetadataPrecedence;
* provider adaptation preserves the typed RealmRef boundary;
* unrelated physically distinct realms satisfy frame properties.

Keep an interception specification relational where the ADR requires it. An
executable interceptor may be added as a realization with a satisfaction proof,
not as an undocumented replacement for the specification.

### T05 — One-way flat embedding

Implement FlatEmbedding only in the accepted direction. Prove the laws stated
by ADR-10, such as preservation of lookup, update, metadata, or default-realm
behavior for values in the image.

Do not add an arbitrary flatten/unflatten equivalence, universal projection, or
surjectivity theorem. If a partial projection on a stable image is useful,
define the image predicate and prove the restriction explicitly. The existence
of a legacy flat representation is not evidence that every structured scoped
state can be losslessly flattened.

### T06 — Executable examples and API freeze

In STC/Examples/Scoped.lean, provide finite deterministic evidence for:

* default realm resolution;
* resolver override and miss behavior;
* two realms under one logical key remaining physically distinct;
* scoped insert, lookup, erase, and a frame case;
* metadata precedence under interception;
* persistent deriveIsolate and deriveIntercept behavior;
* the flat embedding on values inside its image.

Freeze the production API after these examples elaborate. The handoff must
list the exact module imports and public declarations, classify evidence as
A/I/K/E, and identify any assumptions that keep a result below the strongest
paper-level claim.

## 7. Definition Ledger handling

Do not edit docs/status/Definition-Ledger.json in this parallel branch. Propose
exact central-integration deltas in the P12 handoff instead.

The expected row family includes D28–D31 and any explicitly ADR-10-scoped rows
present in the current ledger. D27 remains expository/deferred unless its exact
paper claim has been formalized, and D74 remains deferred unless this plan's
implemented theorem exactly discharges it. Do not upgrade a row based only on
a similarly named interface.

For every proposed change record:

* current and proposed status;
* delivery vocabulary;
* Lean symbol and module;
* A/I/K/E evidence classification;
* exact theorem strength;
* remaining deferred_reason.

Use one post-P9 convention for dependency-blocked rows within the proposed
patch. Prefer planned plus an explicit deferred_reason until the repository
adopts a single global normalization rule.

## 8. Required validation

Run at minimum:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Model.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Resolver.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Store.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Context.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Flat.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Scoped.lean
lake build

python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC

rg -n '^import .*Control|^import .*Staging|^import .*Support' \
  STC/Scoped.lean STC/Scoped STC/Examples/Scoped.lean

rg -n 'sorry|admit|axiom|unsafe' \
  STC/Scoped.lean STC/Scoped STC/Examples/Scoped.lean

git diff --check
git status --short
~~~

If files were consolidated, adjust individual Lean commands while retaining a
check for every production and example module. Keep raw scans in
docs/status/P12-scoped-scan-raw.txt and classify any reviewed false positives.
For scripts/scan_lean.py, exit 1 means clean, exit 0 means a lexical match
requiring classification, and exit 2 means a scan failure. Production imports
of historical spike modules are a hard failure.

Also inspect the diff directly to confirm STC/State/CoeffectStore.lean and
shared integration paths are untouched:

~~~bash
git diff --name-only <branch-base>...HEAD
~~~

## 9. Acceptance criteria

P12 Scoped is complete only when all of the following hold:

1. ADR-10 has an accepted P9 status record at the execution baseline.
2. RealmRef preserves its dependent key/realm typing and uses no unsafe cast.
3. ResolverSpec and executable finite Resolver remain distinct and have a
   checked satisfaction bridge.
4. ResolverUpdate has checked hit, miss, finite-support, and preservation laws.
5. Scoped operations adapt the existing P5 STC.Coeffect.Store rather than
   introducing a competing authoritative store.
6. PhysicalDistinct, including the same-key/different-realm case, is handled at
   the physical adapter boundary.
7. Store lookup/update/erase and frame laws elaborate with substantive K
   evidence where claimed.
8. Metadata algebra and precedence are explicit, and persistent context laws
   are proved.
9. FlatEmbedding is one-way; no unjustified global converse appears.
10. Finite examples exercise the typed and physical-distinctness boundaries.
11. No Control, Staging, or Support dependency has been introduced.
12. Full build, ledger validation, and spike-import validation pass.
13. The handoff proposes central ledger deltas without editing the shared file.

## 10. Reopen and stop rules

Stop and reopen planning rather than improvising if:

* the accepted ADR-10 status record is missing or no longer formally accepted;
* RealmRef cannot be represented without changing the accepted RealmModel;
* the P5 store lacks a necessary operation or law and the missing seam cannot
  be defined as a local adapter;
* physical non-aliasing would require treating logical inequality as sufficient
  in a same-key/different-realm case;
* executable resolution cannot be related to ResolverSpec;
* rollback would re-resolve through a mutable resolver without stability;
* a flat converse is needed to prove a claimed theorem;
* implementation requires editing Control, Staging, Support, P5, or a shared
  integration path outside this plan's ownership;
* an E example is the only evidence for a result labelled K.

The reopen report must give the smallest conflicting type or law and classify
the issue as source ambiguity, ADR inconsistency, Lean engineering, or
integration ordering.

## 11. Merge and downstream handoff

Commit this lane independently after every gate passes. Because it owns a
disjoint namespace and adapts only stable P5 APIs, it may merge before or after
the Control/Staging and Support Core lanes.

The handoff report must contain:

* final file and import graph;
* public declaration inventory;
* precise P5 adapter representation;
* all PhysicalDistinct and resolver assumptions;
* theorem evidence classification;
* finite example inventory;
* proposed Definition Ledger deltas;
* raw command results, commit hash, and clean-tree state;
* any exact integration request left for the post-parallel join.

Merging P12 establishes the scoped production layer. It does not by itself
establish global STC metatheory, concrete runtime refinement, or correspondence
with every statement in a later paper revision.
