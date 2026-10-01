# Paper Baseline

This directory preserves the reference material used to begin the Lean formalization of *A Programming Paradigm for Spatiotemporal Composability*. It records the paper's formal content, its dependency structure, and the initial treatment assigned to each item for formalization. Source identities and version information are recorded in the documents themselves.

## Contents

| Document | Purpose |
|---|---|
| [Formal Reference](DeepSeek-Harness-01-Formal-Reference.md) | Explains the notation, definitions, results, assumptions, and formalization caveats. |
| [Definition and Result Dependency Graph](DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.md) · [JSON](DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json) | Records direct statement and proof dependencies for all 74 numbered items and 8 auxiliary formal blocks. |
| [Formalization Disposition Specification](DeepSeek-Harness-04-Formalization-Disposition-Specification.md) · [JSON](DeepSeek-Harness-04-Formalization-Disposition-Specification.json) | Records whether each item is to be formalized directly, repaired, subsumed, retained as exposition, or deferred, together with its intended artifact and architectural blockers. |

Start with the Formal Reference for the concepts and claims. Use the dependency graph to trace prerequisites, then consult the disposition specification for the proposed treatment of individual items. The Markdown files explain the records; their JSON companions support structured queries and downstream tooling.

## Relationship to Later Work

These materials are preserved as provenance records. They retain the source claims and identified defects; accepted or superseding [architecture decisions](../architecture-decision/) determine the repaired formal targets.

The [executable blueprint](../DeepSeek-Harness-11-Executable-Formalization-Blueprint.md) organizes implementation around those decisions. Current work and evidence are tracked in [execution plans](../../plans/) and [status records](../../status/), with the formal implementation under [`STC/`](../../../STC/).

The paper's metatheory and the Lean proofs concern abstract models. Applying their guarantees to the Cordis runtime requires separate implementation-refinement evidence.
