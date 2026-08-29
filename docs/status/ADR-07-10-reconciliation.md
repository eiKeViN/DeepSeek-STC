# ADR-07..10 Status Reconciliation

This report records the focused reconciliation performed against the current
`origin/main` before P7/P8 execution.

| Field | Value |
|---|---|
| Repository baseline | `origin/main` = `d2f8caafe1081e2a154d7bad0d307e72b6930d8f` |
| Repair commit | `c73000cefaa61a4ea8f8e816864b3f7dab9a8484` (merged by the baseline) |
| Guidance change audited | PR #8 merge `85de511` / change commit `f6a5d16` (the four files named in the request) |
| Audit date | 2026-08-28 |
| Lean | 4.33.0 (`d8b18978322de05a8f3dba51ef03cf5461676c17`) |
| Lake | 5.0.0-src+d8b1897 |
| Mathlib | v4.33.0, resolved revision `db584cd6d46c92f209a44c0f1c829460d327499d` |

## Artifact inventory and status

Every candidate has a Markdown packet, JSON packet, and Lean spike.  The
`formal_acceptance` value is explicitly `false` in each JSON packet; no separate
lead acceptance record was found.  The `architecture_status` therefore remains
`acceptance_pending` and the packets remain proposed.

| ADR | Markdown (SHA-256) | JSON (SHA-256) | Lean spike (SHA-256) | Packet status | Completeness |
|---|---|---|---|---|---|
| ADR-07 | `docs/blueprint/architecture-decision/md/DeepSeek-Harness-12-ADR-07-Control-Architecture.md`<br>`75bab7d6425be9daa3127844d25db1fe45a382930d512d88c75bb78f7190aeaa` | `docs/blueprint/architecture-decision/json/DeepSeek-Harness-12-ADR-07-Control-Architecture.json`<br>`3232b49cca3161542b07eb8682b335e75c1297805c8595114bc1f75094a9e8da` | `docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-12-ADR-07-Control-Architecture.lean`<br>`28d4a90934d9248d229813ae7336f946025e077df2ad68bd308eafa73b8d45ee` | `proposed-architecture-compiler-validated` | `md+json+lean-spike` |
| ADR-08 | `docs/blueprint/architecture-decision/md/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.md`<br>`dfa9a69f0e92919cea33edd1f736e6846bb04212e933419927939a24206a0b55` | `docs/blueprint/architecture-decision/json/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.json`<br>`6cd62aec94d0dc2e59418093b6e49bbde098bb97ec892d39c55c5ed24fe501db` | `docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture-Spike.lean`<br>`63aaf2e76bb9a64f5ea2e18c8293a5f0f5580da60df9c21e5237fcb266948c8f` | `proposed-architecture-closure-compiler-validated` | `md+json+lean-spike` |
| ADR-09 | `docs/blueprint/architecture-decision/md/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.md`<br>`e65e36e4538cfc838fd4bb8a825d518db040eabd61020a077397c7f0c93b738b` | `docs/blueprint/architecture-decision/json/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.json`<br>`4cacf55bedc496309ff9c88baab969ec47f6e1dd4526426571cabc066a6cee61` | `docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture-Spike.lean`<br>`4c7c9c51a5366bc34f215e6279c0e9365ffe1c3b033c51484b4d4d96f4ddd243` | `proposed-architecture-compiler-validated` | `md+json+lean-spike` |
| ADR-10 | `docs/blueprint/architecture-decision/md/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.md`<br>`377ddbd5cc433fd9047206d22a22b3f55241ee934f114c10249803d818591bff` | `docs/blueprint/architecture-decision/json/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.json`<br>`eb483253fbab9ace7a92610bb4136b3499da68d72ba37888d0b3e8a7797daab8` | `docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture-Spike.lean`<br>`9088bf7c1e0e5c6c35dbf2fec1ac8ff270e88c9afa6d433079881eea7eb1dc4c` | `proposed-architecture-compiler-validated` | `md+json+lean-spike` |

The JSON packets intentionally leave `integrity.json_sha256` as `null` because
the JSON self-hash is excluded by their hash policy.  Their recorded Markdown
and Lean hashes match the companion bytes above.

## Focused compiler results

Each command was run independently from the repository root with the pinned
options.  Exit `0` and the absence of `warning:` diagnostics establish the
recorded zero-warning result.  The nonempty output for ADR-09 and ADR-10 is
expected finite `#eval` output, not a warning.

| ADR | Command | Exit | Warnings | Observed output |
|---|---|---:|---:|---|
| ADR-07 | `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-12-ADR-07-Control-Architecture.lean` | 0 | 0 | *(empty)* |
| ADR-08 | `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture-Spike.lean` | 0 | 0 | *(empty)* |
| ADR-09 | `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture-Spike.lean` | 0 | 0 | `true`<br>`true` |
| ADR-10 | `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture-Spike.lean` | 0 | 0 | `some 7`<br>`none` |

## Interpretation and downstream gate

The repaired spikes remove the compiler-pending dimension only.  They do not
establish semantic or architectural acceptance, production integration, kernel
theorem coverage, or runtime refinement.  P9 therefore remains the explicit
ADR-acceptance gate; P10+ production reservations remain untouched, and no
Definition Ledger theorem row is promoted by this reconciliation.

Frozen H03/H04 inputs and accepted ADR-01..06 artifacts were not modified.
