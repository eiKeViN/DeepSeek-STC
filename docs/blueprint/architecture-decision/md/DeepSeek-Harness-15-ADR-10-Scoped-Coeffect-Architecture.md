# DeepSeek Harness ADR-10: Scoped Coeffect and Realm Architecture

| Field | Value |
|---|---|
| Packet ID | ADR-10 |
| Title | Typed scoped coeffects, interception, and flat embedding |
| Status | **Proposed architecture closure; compiler validation pending** |
| Packet version | 0.1-proposed |
| Date | 2026-08-28 |
| Resolves | BD-SCOPED at the architecture/interface level |
| Semantic change | None to the frozen paper, H03/H04, or accepted ADRs |
| Depends on | ADR-02, ADR-03 closure, ADR-04, ADR-06 closure; P5 state-side interfaces |
| Production namespace | STC |
| Spike namespace | STCADR10 |
| Companion artifacts | DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.json; DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture-Spike.lean |

## 1. Decision summary

This packet fixes the type and composition boundary for the scoped coeffect
extension (D28--D31). It is an architecture packet, not a claim that the
Section 4 lifecycle calculus or a runtime implementation has already been
proved.

The formal target has two deliberately separate resolver layers:

1. A semantic resolver specification is a proposition-valued relation. It
   says which realm references are admissible for a logical key.
2. An executable resolver chooses one typed reference for every key and
   carries a finite override-support envelope. Its result type already contains
   the key-preservation witness, so an ill-typed V_r cannot enter a V_k
   operation.

The selected scoped context is persistent:

~~~text
ScopedContext
  = resolver + abstract realm store + interception metadata
~~~

isolate derives a child with a changed resolver and the same store/metadata.
intercept derives a child with changed metadata and the same resolver/store.
The parent value is never mutated or implicitly discarded by the core model.

Metadata composition is explicit. If ⊕_k is the per-key algebra, ordinary
provider lookup uses

~~~text
declared(k) ⊕_k contextMeta(k)
~~~

so the context operand has precedence. An interception extends an inherited
context as

~~~text
inherited(k) ⊕_k new(k)
~~~

so the newly installed metadata has precedence. Associativity and identity
come from the monoid fields; right priority is a separate law and is never
inferred from the monoid laws alone. Metadata presence is represented
separately from the metadata value.

The flat model is a one-way embedding. Under an identity resolver, no aliasing,
and neutral interception metadata, a flat store embeds into a scoped store and
preserves lookup, insert, and erase. The packet does not assert that an
arbitrary realm configuration can be flattened faithfully.

## 2. Why the scoped equations need a repair

The paper writes an isolation context using a partial rho : K ⇀ R and a
dependent store of the shape (r : R) ⇀ V_r, then applies rho(k) with a
default. This has two independent defects:

* a partial resolver is used as if it were total; and
* a value at the resolved realm has type V (rho(k)), not automatically the
  logical-key type V k.

The packet keeps the paper's intent (logical keys may resolve to physical
realms) while making both obligations visible. A RealmRef M k contains a
physical token and a proof that its model key is k. Conversion between
V (keyOf token) and V k is performed only through that witness. The
default realm is a total model operation, not an implicit fallback hidden in a
partial function.

The inverse of a scoped write captures the selected physical token at the
time of the forward application. It must not recompute a later resolver and
then erase whichever realm happens to be selected at that later time.

## 3. Typed model and resolver layers

The standalone spike uses the following shape (names are stable API guidance,
not a demand to copy this file into production):

~~~lean
structure RealmModel (K : Type u) (V : K → Type v) where
  Realm : Type w
  keyOf : Realm → K
  default : (k : K) → Realm
  default_key : ∀ k, keyOf (default k) = k

structure RealmRef (M : RealmModel K V) (k : K) where
  token : M.Realm
  key_eq : M.keyOf token = k
~~~

The semantic layer is a relation:

~~~lean
ResolverSpec M := ∀ k, RealmRef M k → Prop
~~~

The executable layer is a total choice with finite support:

~~~lean
structure Resolver M [DecidableEq K] where
  resolve : (k : K) → RealmRef M k
  overrideKeys : Finset K
  finite_support :
    ∀ {k}, k ∉ overrideKeys →
      (resolve k).token = (defaultRef M k).token
~~~

Thus resolve k is executable and type-preserving by construction, while a
semantic specification can remain nondeterministic or abstract. A refinement
must explicitly prove that the chosen executable reference satisfies the
semantic relation; no coercion silently identifies the two layers.

ResolverUpdate is an interface for an isolation operation. Its laws expose
same-key replacement, other-key preservation, and finite-support growth. The
concrete update algorithm is intentionally left to the P5/ADR-02 store and
resolver implementation.

## 4. Realm store and scoped operations

The packet does not introduce another authoritative finite-map
implementation. Instead it defines a proof-facing operation interface:

~~~lean
structure RealmStoreOps (M : RealmModel K V) (Store : Type x) where
  empty : Store
  lookup : Store → (r : M.Realm) → Option (V (M.keyOf r))
  insert : Store → (r : M.Realm) → V (M.keyOf r) → Store
  erase : Store → M.Realm → Store
  lookup_empty : ...
  lookup_insert_same : ...
  lookup_insert_other : ...
  lookup_erase_same : ...
  lookup_erase_other : ...
~~~

The ellipses above denote explicit law fields in the spike; they are not
unchecked axioms. ADR-02's dependent Finmap remains the authoritative
production implementation and may later instantiate this interface.

For rr : Resolver.resolve k, the scoped operations are:

~~~text
scopedLookup(s,k) = lookup(s, rr.token) |> map rr.cast
scopedInsert(s,k,v) = insert(s, rr.token, rr.castInv(v))
scopedErase(s,k) = erase(s, rr.token)
~~~

PhysicalDistinct rho k j is an explicit premise for a frame theorem:
logical-key inequality alone does not imply physical noninterference when two
keys may resolve to one realm. Provider, frame, and recovery statements in a
realm-aware model must therefore quantify over the selected physical tokens.

## 5. Interception metadata and merge precedence

Each key has its own metadata type and algebra:

~~~lean
structure MetaAlgebra (K : Type u) (Meta : K → Type v) where
  empty : (k : K) → Meta k
  merge : (k : K) → Meta k → Meta k → Meta k
  left_id : ...
  right_id : ...
  assoc : ...
~~~

An InterceptionSpec has a finite support and an Option (Meta k) payload.
The support records where an entry is present; none is not confused with a
present metadata value. deriveIntercept merges inherited metadata with the
new specification at every key, using empty outside the finite support.

The spike also defines MetadataPrecedence. Its right_wins field is a
separate proposition, parameterized by a present predicate. This is the
precise place to state right-biased override behavior for a concrete metadata
algebra. A monoid instance without this field provides no priority guarantee.

Provider behavior remains an adapter boundary:

~~~lean
ProviderAdapter M Meta := (k : K) → Meta k → V k → V k
~~~

The generic scoped store and generic metadata algebra do not, by themselves,
prove a particular provider function or a runtime service-delivery theorem.

## 6. Persistent derived contexts

The core carrier is:

~~~lean
structure ScopedContext (M : RealmModel K V)
    (Meta : K → Type y) (Store : Type x) where
  resolver : Resolver M
  realms : Store
  contextMeta : (k : K) → Meta k
~~~

deriveIsolate requires a ResolverUpdate interface and changes only resolver.
deriveIntercept requires a MetaAlgebra and changes only contextMeta. The
spike proves the structural persistence laws:

* isolation leaves the realm store and interception metadata definitionally
  unchanged;
* interception leaves the resolver and realm store definitionally unchanged.

This is the abstract/derived realization of D27. Object identity, aliasing,
in-place mutation, and a production persistent data structure remain
refinement questions, not hidden semantics of the metatheory carrier.

## 7. Flat embedding and finite Toy laws

FlatEmbedding packages a one-way embedding from a flat store into a scoped
store and requires three commuting diagrams:

~~~text
lookup (embed s)                 = flatLookup s
scopedInsert (embed s,k,v)       = embed (flatInsert s,k,v)
scopedErase  (embed s,k)         = embed (flatErase s,k)
~~~

The concrete Toy model uses K = Bool, V _ = Nat, R = Bool, the identity
resolver, and ToyStore = Bool → Option Nat. Its store operations are
executable functions with finite key behavior. The spike checks:

* identity-resolver type preservation;
* lookup after insertion;
* absence after erasure;
* all three flat-embedding commuting diagrams;
* right-biased metadata merge on present entries; and
* persistence of the untouched context fields.

These checks are finite witnesses for the interface laws. They do not
instantiate ADR-02's Finmap, prove arbitrary alias-free flattening, or claim
the full D29/D31 lifecycle semantics.

## 8. Scope and deferred obligations

Included in this packet:

* D28's total, type-preserving resolver contract;
* D29's captured-realm operation boundary and persistent isolation context;
* D30's typed metadata algebra, finite specification, and presence separation;
* D31's explicit merge order, right-priority law, and persistent interception;
* a realm-store operation interface and one-way flat embedding;
* finite executable Toy laws for the above contracts.

Deferred by design:

* concrete ADR-02 Finmap integration and P5 STC/State implementation;
* provider uniqueness, active-store fold, lifecycle visibility, and WellFormed
  preservation;
* concrete D24 operation codes and operation-test AST;
* realm-aware Section 4 control, staging, support, confluence, and recovery
  theorems;
* runtime/refinement artifacts and name-bearing payload actions.

Consequently, BD-SCOPED is closed only as an architecture/interface blocker.
The deferred items retain their own evidence labels and must not be marked
proved merely because this spike elaborates.

## 9. Ownership and validation

This packet owns exactly:

~~~text
docs/blueprint/architecture-decision/md/
  DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.md
docs/blueprint/architecture-decision/json/
  DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.json
docs/blueprint/architecture-decision/lean-spike/
  DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture-Spike.lean
~~~

It does not edit production STC, P5 state modules, frozen H03/H04 inputs,
the Blueprint, status/Ledger/Bootstrap files, or accepted ADR artifacts.

The intended gate is:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  docs/blueprint/architecture-decision/lean-spike/\
  DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture-Spike.lean
~~~

The current creation environment has no working lake/lean executable, so
the initial packet records pending-toolchain. A later pinned-toolchain run
must report zero errors and no sorry, admit, custom unchecked axioms, or
unsafe declarations before the packet is promoted.
