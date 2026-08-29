# DeepSeek Harness ADR-09: Support Well-Foundedness Architecture

| Field | Value |
|---|---|
| Packet ID | `ADR-09` |
| Global blocker | `BD-SUPPORT` |
| Status | **Proposed — architecture-only, compiler validated (formal acceptance pending)** |
| Packet version | `0.1-proposed-compiler-validated` |
| Date | `2026-08-28` |
| Scope | Support carrier, least-fixed-point contract, rank certificate, and restricted profiles |
| Semantic change | **No change to the frozen paper/H03/H04 records** |
| Production namespace reserved | `STC` (future P5 module) |
| Spike namespace | `STCADR09` |
| Companion artifacts | `DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.json`; `DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture-Spike.lean` |
| Frozen inputs | H03 dependency graph and H04 disposition are read-only |
| Formal acceptance | `false`; no explicit lead acceptance record |

## 1. Decision in brief

This packet closes only the *architecture* question in `BD-SUPPORT`: support is a
positive operator on a finite registry snapshot, its canonical support is the least
fixed point (the intersection of all prefixed sets), and well-foundedness is supplied
by an explicit `SupportOrder`/`RankCertificate`.  The construction does not put a
recursive `State → State` value in a registry cell and does not rely on a forward
reference from D67 to L68.

The relation direction is fixed and written explicitly:

\[
a \mathbin{\triangleleft} b \quad\overset{\mathrm{def}}{\Longleftrightarrow}\quad
a \prec b \;\lor\; \operatorname{parent}(b)=a.
\]

Thus an edge points from a provider/parent `a` to the dependent/child `b`, and a rank
certificate requires `rank a < rank b`.  A certificate is a visible hypothesis or
proof object; it is not silently inferred from `WellFormed`.

For recursion, use the named converse `SupportDep s b a := SupportRel s a b`:
following a dependent `b` to one of its support predecessors `a` strictly decreases
the rank.  This makes clear why the provider→dependent order has an increasing rank
while the induction-facing dependency relation is well founded.

This is deliberately not a claim that literal L68, L70, L72, or T73 has been proved.
Those theorems still need reachable labelled traces, lifecycle/control guards, name
identity, and the exact strengthened invariants owned by later work.

## 2. Why this is the smallest safe closure

H04 records two separate issues:

1. D67 must define support before L68 can use it.  A recursive definition whose
   well-foundedness is supplied only by the following lemma is not a Lean-safe carrier.
2. The recorded `F-L68-CYCLE` is a reachability/theorem problem, not merely a datatype
   problem.  A support carrier can be total on cyclic snapshots while the corrected L68
   theorem is conditional on a rank certificate (or an equivalent control invariant).

The packet therefore fixes interfaces and proof obligations without choosing a new
runtime scheduler or weakening the frozen baseline.  It gives later proofs a common
place to state the exact assumptions they consume.

## 3. Chosen carrier and contracts

### 3.1 Finite snapshot

The spike models a snapshot as:

```lean
Snapshot N K := {
  dom       : Finset N,
  retired   : N → Bool,
  parent    : N → Option N,
  requires  : N → Finset K,
  provides  : N → Finset K,
  birth     : N → Nat
}
```

`N` is the ADR-04 incarnation identity domain and `K` is a requirement/provision key
domain.  This is an architecture mirror, not the final P5 state representation.  The
finite domain makes support snapshots inspectable and gives a later executable fold a
clear boundary; no claim is made that the dynamic runtime state itself is immutable.

### 3.2 Support relation

For a snapshot `s`:

```lean
Precedes s a b   := (s.provides a ∩ s.requires b).Nonempty
ParentEdge s a b := s.parent b = some a
SupportRel s a b := Precedes s a b ∨ ParentEdge s a b
```

The `⊲` orientation above is normative for this packet.  If a downstream theorem uses
the converse (for example, a dependency-first traversal), it must name the converse
relation explicitly rather than reversing an inequality by convention.

### 3.3 Positive least-fixed-point support

For a candidate set `A : Set N`, the support clause is:

```lean
n ∈ s.dom ∧ s.retired n = false ∧
  (s.parent n = none ∨ ∃ p, s.parent n = some p ∧ p ∈ A) ∧
  (∀ k, k ∈ s.requires n → ∃ m, m ∈ A ∧ k ∈ s.provides m)
```

`SupportOperator s A` is the set of nodes satisfying that clause.  The canonical
support is defined positively as:

\[
\operatorname{SupportSet}(s)
 = \bigcap\{A \mid F_s(A)\subseteq A\}.
\]

The spike proves monotonicity of `F`, leastness, and the fixed-point equation
`F (SupportSet s) = SupportSet s`.  This is an ordinary least-fixed-point contract,
not an inductive declaration with a hidden negative occurrence.  It remains total on a
cyclic or otherwise malformed snapshot; later theorems add `SupportWF` when they need
well-founded induction, non-empty support, or uniqueness of a provider closure.

### 3.4 Rank certificate / `SupportWF`

```lean
structure SupportOrder (s : Snapshot N K) where
  rank : N → Nat
  edge_lt : ∀ {a b}, a ∈ s.dom → b ∈ s.dom →
    SupportRel s a b → rank a < rank b

abbrev RankCertificate s := SupportOrder s
def SupportWF s := Nonempty (SupportOrder s)
```

`SupportWF` is intentionally a proposition that carries an explicit certificate.  The
finite snapshot plus `edge_lt` yields the usual no-cycle consequence (the spike proves
the two-edge case; a production module can derive `WellFounded` for `SupportDep`, the
converse/restricted relation).  The certificate is the boundary imported by corrected L68 and by any
linearisation/confluence proof; it is not a proof that every reachable state satisfies
it.

### 3.5 Restricted profiles

Two optional profiles are supplied:

* `NoLateRegistration s` requires every support edge to increase the immutable `birth`
  index.  It converts directly to a `SupportOrder`.  This is a deliberately strong
  profile: it is a safe theorem domain for traces that forbid support-relevant late
  registration, not a replacement for the paper's current-fresh O-Insert rule.
* `CommittedSnapshot s` packages a finite committed domain together with a
  `SupportOrder`.  Its two domain-inclusion fields express that the committed domain is
  exactly the snapshot domain.  Staging/control work decides when such a snapshot may be
  taken and when it remains valid.

These profiles let later work prove useful restricted results without pretending that
the full asynchronous rules already imply support well-foundedness.

## 4. Frozen `F-L68-CYCLE` adjudication

The shorthand in H04 lists (with the orientation fixed above):

| edge | meaning |
|---|---|
| `r → n` | `r ≺ n` |
| `r → c` | `parent(c) = r` |
| `c → n` | `parent(n) = c` |

Those three edges are acyclic.  The spike gives the rank `rank(x) = x.val` for the
three-node illustration and proves that no directed three-cycle can be formed from the
shorthand alone.  It would be incorrect to report those edges as a counterexample.

A genuine *combined-support* cycle is obtained only after adding an extra precedence
edge `n ≺ r` (the edge `n → r`).  The resulting cycle is `r → c → n → r`; precedence
alone can still be acyclic in this small model (the reverse rank `2 - x.val` witnesses
the precedence fragment).  The spike proves that no single support rank can orient all
three combined edges.

This corrected graph is a finite witness, **not a reachable lifecycle trace**.  To call
it a semantic counterexample one must additionally provide a labelled control trace
showing the retired/reloading child, removal of the former provider, and late
registration.  That reachability argument belongs to `BD-CONTROL`/`BD-STAGING` and is
not fabricated here.

## 5. Downstream theorem envelope

| Item | What ADR-09 supplies | What remains deferred |
|---|---|---|
| D67 | Named `SupportRel`, positive `SupportOperator`, canonical LFP `SupportSet` | Exact Section-4 typing and provider semantics in P5 |
| L68 | `SupportWF`/rank certificate interface; corrected theorem can quantify over it | Reachability, control invariant, and full K proof |
| L70 | Explicit input envelope: quiescent + nonfailed + total provision + support certificate | Equality with active fibers and lifecycle proof |
| L72 | Support assumptions can be stated without hidden forward references | Deletion preservation, equivalence, control, and staging |
| T73 | A rank/order hook for linearisation and canonical-form arguments | Confluence, termination, name/trace transport, and all K obligations |

No frozen H03 edge or H04 disposition row is edited by this packet.  “Architecture
closed” means the carrier and assumptions are now named and reviewable; it does not
promote any deferred theorem to accepted status.

## 6. Interaction with the current execution plans

* **P3 (partial/failure):** independent.  Failure-preserving iterators may carry a
  snapshot identifier, but failure semantics do not establish `SupportWF`.
* **P4 (iterator):** iterator `Nat` rank and support `Nat` rank are different measures.
  No proof may reuse one as the other without an explicit decreasing-map theorem.
* **P5 (state carrier):** owns the production `STC/State/**` representation.  After its
  interface freeze, the likely integration point is a support module exposing this
  packet's contracts; this ADR does not create that module concurrently.
* **P6 (equivariance/refinement):** must transport `SupportRel`, `SupportSet`, and rank
  certificates under ADR-04 alpha permutations.  The certificate transports
  existentially; a particular numeric rank need not be invariant.
* **BD-CONTROL/BD-STAGING:** supply labelled reachability, no-late-registration guards,
  and committed-snapshot validity.  They determine whether the restricted profiles apply
  to a given trace.

## 7. Spike and validation boundary

The companion spike is standalone and uses namespace `STCADR09`; it does not import
`STC` production code and contains no `sorry`, `admit`, `unsafe`, or project axiom.  It
proves the LFP laws, rank/no-two-cycle lemma, acyclicity of the frozen shorthand, and
the no-rank result for the corrected finite graph witness.  Two `#eval` checks expose
the finite edge witnesses.

The repaired spike was independently checked on 2026-08-28 with the pinned Lean 4.33.0 /
Mathlib v4.33.0 command in a complete checkout.  It exited 0 with zero warnings (the two
`true` lines are the expected finite edge checks).  This packet therefore records compiler
validation as interface evidence only; it remains proposed and no formal acceptance,
production integration, or downstream `K` theorem is implied.  The command is:

```text
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture-Spike.lean
```

Compilation will establish interface evidence only.  The L68/L70/L72/T73 semantic
proofs still require the explicit downstream hypotheses listed above.

## 8. Ownership and revision policy

This packet may add or patch only its three companion files under
`docs/blueprint/architecture-decision/{md,json,lean-spike}/`.  It must not modify
production `STC`, `STC/Bootstrap.lean`, `Cordis`, status/ledger files, H03/H04 baselines,
or historical accepted ADR artifacts.

An editorial clarification is a patch version.  Changing the support carrier,
reversing edge orientation, moving freshness/ledger assumptions, or adding a new rule
class requires a superseding ADR.  Complete K proofs remain downstream deliverables.
