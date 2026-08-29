# P11 Staging Handoff Report

P11 Staging is complete at commit
`a18407cd8034ae1822873b4c6c52e023cab99537`, immediately after the frozen P10
Control commit `47c3b8018d0b688cbbfc1ef41448d4e6e518596c`, on branch
`codex/p10-p11-control-staging`.

## Production surface

`STC.Staging` defines `StagingModel` and `MacroPath` over the shared
`STC.Control.Trace` carrier. `AtomicOrchMacro` and `AtomicLifeMacro` are derived
from the authoritative full relations and explicit expansion lists; `RbOrch`
and `RbLife` are aliases for those derived macro propositions. `ForwardSimulation`
and `AtomicAdequacy` preserve endpoint embeddings, labels, and profile-relative
converse boundaries. `append_macro_paths` composes macro traces using the
Control append theorem.

No independent base transition calculus, scheduler, historical spike import, or
runtime refinement declaration was added. The P10 Control files were not changed
after the API freeze.

## Finite evidence

`STC.Examples.Staging` demonstrates:

* singleton orchestration and two-step reload/unload lifecycle expansions;
* project/embed round-trip and stable-image facts;
* forward macro witnesses and concatenated full traces;
* an accepted reload adequacy case;
* wrong endpoint projection rejection; and
* rejection of non-atomic, interleaved, and unfinished label profiles.

## Validation

* `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Staging.lean`: exit 0.
* `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Staging.lean`: exit 0.
* `lake build`: exit 0, 756 jobs (reused cached dependencies).
* `python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json`: PASS, 82/82.
* `python scripts/scan_lean.py STC`: exit 1, clean; raw output is retained in
  `docs/status/P11-staging-scan-raw.txt`.
* `git diff --check`: exit 0.

The historical `docs/status/P8-conformance-manifest.json` was not regenerated;
the generator writes that artifact in place. Definition Ledger updates remain
proposed for central integration, as required by the execution plan.

This lane supplies A/I/K/E local evidence only. Global theorem completion,
Support/Scoped joins, and Cordis R1+ refinement remain deferred.
