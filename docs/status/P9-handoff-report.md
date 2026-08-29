# P9 Handoff Report: ADR Promotion Gates

| Field | Value |
|---|---|
| Plan | `DH-P9-EXEC-01` (`docs/plans/P9-Execution-Plan.md`) |
| Wave | P9 — ADR promotion gates |
| Base | `fb154a6` (post-P8 merge) |
| Date | 2026-08-29 |
| Toolchain | Lean 4.33.0 / Mathlib v4.33.0 |

## Task status

| Task | Result |
|---|---|
| P9-T01 | Passed: P8 manifest and all four complete candidate companion sets audited |
| P9-T02 | Passed: explicit accepted status recorded independently for ADR-07, ADR-08, ADR-09, and ADR-10 |
| P9-T03 | Passed: architecture closure is separated from production, kernel, executable, and runtime evidence |
| P9-T04 | Passed: JSON, companion hashes, focused Lean, build/cache, ledger, and scan checks recorded below |

## Promotion decision

The four records under `docs/blueprint/architecture-decision/status/` are the
normative P9 acceptance records. They were created from the explicit project-lead
instruction for this run. The candidate packet bytes remain unchanged, including
their historical `formal_acceptance: false` metadata; the separate status record
is the authority required by the repository's status model.

| ADR | Blocker | Architecture | Production | Kernel | Runtime |
|---|---|---|---|---|---|
| ADR-07 | `BD-CONTROL` | closed | pending | pending | deferred |
| ADR-08 | `BD-STAGING` | closed | pending | pending | deferred |
| ADR-09 | `BD-SUPPORT` | closed | pending | pending | deferred |
| ADR-10 | `BD-SCOPED` | closed | pending | pending | deferred |

Acceptance therefore authorizes the corresponding P10–P12 implementation gates,
but it does not subtract production or theorem obligations from the Definition
Ledger and does not establish Cordis `R1+` refinement.

## Integrity boundaries

* H03/H04, accepted ADR-01..06 artifacts, candidate ADR-07..10 packets, Lean
  spikes, `STC/`, `STC/Bootstrap.lean`, and `docs/status/Definition-Ledger.json`
  were not modified by P9.
* The P8 conformance manifest remains a historical P8 snapshot. P9's accepted
  status records are additive and do not rewrite that derived artifact.
* No `sorry`, `admit`, project-defined unchecked axiom, or `unsafe` declaration
  was added.

## Verification record

The exact local outputs are retained here after execution:

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-12-ADR-07-Control-Architecture.lean
  exit 0, no output (cached)
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture-Spike.lean
  exit 0, no output (cached)
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture-Spike.lean
  exit 0, output: true / true (cached)
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true docs/blueprint/architecture-decision/lean-spike/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture-Spike.lean
  exit 0, output: some 7 / none (cached)
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
  exit 0, no output (cached root module now available)
$ lake build
  exit 0, Build completed successfully (756 jobs; cached dependency reuse)
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
  exit 0, Definition-Ledger validation: PASS (82/82; H03/H04 hashes OK)
$ python scripts/scan_lean.py STC
  exit 1, clean; no forbidden markers found
$ git diff --check
  exit 0

$ python - <<'PY'
  P9 status JSON parse: PASS (4/4 accepted records)
  P9 candidate companion hashes: PASS (12/12)
  PY
```

## Rollback and next action

P9 changes are documentation-only and recoverable by removing the four status
records, this plan, and this report. P10 may now begin only in a separate task
that consumes the accepted ADR-07 record; P11/P12 retain their dependency gates
and must add independent `I`/`K`/`E` evidence.
