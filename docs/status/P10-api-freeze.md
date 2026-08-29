# P10 Control API Freeze

| Field | Value |
|---|---|
| Plan | `DH-P10-P11-STAGING-EXEC-01` |
| Branch | `codex/p10-p11-control-staging` |
| Base | `69b4184f682e53010abaf1d153fa9b9453924d50` |
| Freeze commit | `47c3b8018d0b688cbbfc1ef41448d4e6e518596c` |
| ADR-07 accepted-record SHA256 | `6eaa56eb94384e7e225f024436d5fa996cb0dd8e4c31a4d4fa736204c31a6152` |
| Toolchain | Lean 4.33.0 / Mathlib v4.33.0 |

## Public API

Production declarations are in `STC.Control`:

* `ControlMode`, `LandingChoice`, `LandingWitness`, `InFlight`, `ControlState`;
* `OrchestrationLabel`, `LifecycleLabel`, `ControlModel`, `Step`;
* `Trace`, `Trace.labels`, `Trace.length`, `Trace.append`,
  `Trace.append_labels`, `Trace.length_append`, `Trace.onlyLifecycle`;
* `HasLifecycleSuccessor`, `MaximalLifecycleSuffix`, `TracePolicy`,
  `Trace.stepsOk`, `Trace.admissible`, and `lifecycleOnlyPolicy`;
* `AsyncPolicy`, `landingAllowed`, `landingAllowed_has_witness`, `raiseLabel`,
  `raiseLabel_failure_preserves`, and `raiseLabel_success_absent`.

`STC.Examples.Control` supplies nonempty orchestration/lifecycle relations, a
two-step reload trace, a two-step unload trace with a maximal terminal suffix,
an allowed landing, a rejected mid-stage abort, and complete failure-label
preservation checks.

## Gate evidence

* `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Control.lean`: exit 0.
* `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Control.lean`: exit 0.
* `lake build`: exit 0, 756 jobs (reused cached dependencies).
* `python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json`: PASS, 82/82.
* `python scripts/scan_lean.py STC`: exit 1, clean.
* `git diff --check`: exit 0.

The P10 preflight generator was intentionally not run because it rewrites the
historical `docs/status/P8-conformance-manifest.json`; this file remains
unchanged.

## Boundary

This is interface and local A/I/K/E evidence only. The abstract model has no
scheduler and makes no global preservation, progress, confluence, or R1+
runtime-refinement claim. P11 Staging may consume this API but may not modify
the Control files after this freeze.
