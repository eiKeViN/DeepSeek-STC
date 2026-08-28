# P8 Feedback and Rollback Log

| Field | Value |
|---|---|
| Plan | `DH-P7-P8-EXEC-01` |
| Wave | P8 conformance, R0 seam, and handoff evidence |
| Toolchain | Lean 4.33.0 / Lake 5.0.0-src+d8b1897 / Mathlib v4.33.0 |
| Decision status | ADR-07..10 remain proposed and acceptance-pending |

## Proof and API attempts

No new failed proof attempt materially changed a production API in P8.  The
adapter is a pure record contract and the manifest schema compiles directly
under the pinned options.  Existing P7 equation-pinned proofs and P6 alpha
conventions were treated as stable inputs.

## Toolchain and generator checks

The manifest generator intentionally validates H03/H04 schema versions, hashes,
82-row coverage, title alignment, accepted-artifact workspace hashes, and all
four candidate packet companion hashes.  It fails closed before writing the
derived file on any mismatch.  JSON output uses stable insertion order,
newline-terminated UTF-8, and no wall-clock timestamp.

The P0 provenance record reports the repository-canonical variants of
ADR-01, ADR-02, and the ADR-06 spike.  Their bytes intentionally differ from
the older Blueprint companion hashes; the generator records both values and
does not rewrite either source.

## Vacuity and counterexample checks

The P7 report retains a non-identity finite alpha swap, used name-bearing trace
fields, the explicit foreign-stability counterexample, and tagged failure
boundary/prefix undo data.  The R0 interface has no smoke instance with an
empty relation or impossible admissibility predicate.

## Rollback and superseding decisions

No rollback was required.  Removing the derived JSON and status reports would
be a recoverable regeneration from the frozen inputs using
`python scripts/generate_conformance_manifest.py`.  No superseding ADR was
triggered: P8 adds only derived evidence and generic one-way contracts.

## Reproducibility commands

The final command/output record is in `docs/status/P8-handoff-report.md` and
the scanner's raw result is retained in `docs/status/P8-scan-raw.txt`.
