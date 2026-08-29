# P11 Support Core Handoff

Date: 2026-08-29  
Base: `69b4184` (`origin/main`, post-P9/P10-P11/P12 planning merge)  
Scope: accepted ADR-09 support core only

## Delivered

- `STC/State/Support.lean` defines `SupportSnapshot`, provider/parent-oriented
  `SupportRel`, converse `SupportDep`, positive `SupportOperator`, and the
  least fixed-point `SupportSet`.
- Monotonicity, prefixedness, leastness, and the fixed-point equality are proved.
- `SupportOrder`/`RankCertificate`, `SupportWF`, and a domain-restricted
  `supportDep_wellFounded` theorem make the rank assumption explicit.
- `NoLateRegistration` and `CommittedSnapshot` expose the freeze/order boundary.
- `STC/Examples/Support.lean` provides finite parent/provider closure evidence,
  a usable well-founded certificate, and a graph-only cycle witness rejecting a
  global rank.

## Evidence and boundaries

| Area | Evidence |
|---|---|
| Snapshot and relation API | A/I |
| Positive closure monotonicity, leastness, fixed point | K |
| Restricted `SupportDep` well-foundedness | K, under `SupportOrder` |
| Parent/provider/cycle fixtures | E/K |
| Control/Staging integration | deferred; no imports or trace-facing claims |
| Definition Ledger | unchanged; central integration must propose deltas |

Support rank is intentionally distinct from iterator rank. `SupportRel` points
from provider/parent to dependent; `SupportDep` reverses those arguments for
dependency-first recursion. The cycle fixture is a finite graph witness only,
not a reachable lifecycle trace.

## Verification

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Support.lean
  exit 0
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Support.lean
  exit 0
$ lake build
  exit 0, Build completed successfully (756 jobs)
$ python scripts/scan_lean.py STC
  exit 1, clean; raw output in docs/status/P11-support-core-scan-raw.txt
$ rg Control/Staging imports on owned files
  no matches
$ rg sorry/admit/axiom on owned files
  no matches
$ git diff --check
  exit 0
```

The production module imports only Mathlib and has no dependency on Control or
Staging. Trace-facing support rows (`L68`, `L70`, `L72`, `T73`) remain deferred
for the later integration join.
