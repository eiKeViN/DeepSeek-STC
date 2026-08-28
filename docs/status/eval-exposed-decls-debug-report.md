# Debugging report: `#eval` over `@[expose]`d declarations fails on Windows

- **Date**: 2026-08-28
- **Prepared by**: Claude (session with project lead)
- **Status**: workaround in place (build green); seeking a real solution for the original UX
- **Goal**: restore top-level `#eval` of library reports (`report`, `effectReport`) in `STC/Examples/*` without breaking the mathlib-style module system adopted for `STC/`.

## Environment

- Windows 10 Pro (10.0.19045), Lean 4.33.0 (commit `d8b18978322de05a8f3dba51ef03cf5461676c17`), Lake 5.0.0-src+d8b1897, mathlib `v4.33.0` (rev `db584cd6d46c92f209a44c0f1c829460d327499d`)
- Project: DeepSeek-STC (`lakefile.toml`: `lean_lib "STC"`, `leanOptions: autoImplicit = false, pp.unicode.fun = true`)
- All `STC/` production modules now follow `module` + `public import` + `@[expose] public section` (per `AGENTS.md`, mathlib style).

## The original error

`lake build` fails on `STC/Examples/Effect.lean` at the `#eval effectReport` line:

```text
STC/Examples/Effect.lean:254:0: Could not find native implementation of external
declaration 'STC.seqRun._redArg' (symbols
'lp_DeepSeek_x2dSTC_STC_seqRun___redArg___boxed' or
'lp_DeepSeek_x2dSTC_STC_seqRun___redArg').
For declarations from `Init`, `Std`, or `Lean`, you need to set
`supportInterpreter := true` in the relevant `lean_exe` statement in your `lakefile.lean`.
```

`STC/Examples/RelationResult.lean`'s `#eval report` **does not fail** — its eval path only touches `decide`-based Bool checks and never calls an `@[expose]`d STC declaration.

## Established root-cause chain

1. **Module-system export rule.** Lean 4.33: an exported (public) theorem may only *unfold* definitions that are themselves exposed. With a plain `public section` (no `@[expose]`), every `rfl`/`change`/`simp [def]` proof over a public declaration fails with `Not a definitional equality: the left-hand side`. Minimal repro (a `module` file, `public section`, `def track …`, `theorem t1 : (track t ctx).1 = t.1 := rfl`) reproduces the error; adding `@[expose]` fixes it. Hence `STC` uses `@[expose] public section`, exactly as mathlib does.
2. **`@[expose]` extern-izes declarations.** Exposed declarations become `@[extern]`-like for the interpreter; evaluating any code path that calls them requires their compiled native symbols. `#eval effectReport` calls `seqRun` → symbol `STC.seqRun._redArg` is demanded and not linked → the error above.
3. **`supportInterpreter` does not exist for `lean_lib`.** The error hint mentions `lean_exe` only. Verified from Lake source (`src/lake/Lake/Build/Executable.lean` contains `supportInterpreter`; `LeanLibConfig` has no such field). Setting `supportInterpreter = true` under `[[lean_lib]]` in `lakefile.toml` is silently ignored.
4. **`defaultFacets` naming.** Per Lake source `src/lake/Lake/Config/LeanLibConfig.lean`: `defaultFacets : Array Name := #[LeanLib.leanArtsFacet]`; the shared-library facet is `LeanLib.sharedFacet` (not `sharedLib`). Building it pulls `Module.oFacet`/`Module.oExportFacet` objects into a shared library.
5. **`precompileModules = true` is documented but infeasible here.** `LeanLibConfig.precompileModules`: "compile each of the library's modules into a native shared library that is loaded whenever the module is imported. … enables the interpreter to run functions marked `@[extern]`." Setting it made the workspace build request `Mathlib:shared` (the *dependency's* shared lib) and that link fails on Windows:
   ```text
   ld.lld: error: too many exported symbols (got 203521, max 65535)
   ```
   Windows DLLs cap at 65,535 exported symbols; mathlib exports ~203k, so mathlib cannot ship as a Windows shared library at all. This is why mathlib never builds one. `precompileModules` was reverted.
6. **Current workaround.** The two `#eval` lines were removed; each report is still executed and pinned by `example report = { … } := by decide` at elaboration time. `lake build` is green. `AGENTS.md` now records: no top-level `#eval` over exposed declarations; no `precompileModules`/shared facets.

## Open questions for prolonged debugging

1. **Evaluate exposed decls without a package shared library.** Is there a Lake/Lean mechanism that compiles per-module native code and makes it available to the interpreter during `#eval` in the *same* library, without inducing the dependency's shared-library link (`Mathlib:shared`)? E.g. a module-level `precompileModules`-like flag, or a `lean_exe` test runner for `STC/Examples` with `supportInterpreter := true` that links only STC modules' object files against mathlib's objects?
2. **Selective exposure.** The export rule needs the definitions *unfolded by exported theorem proofs* to be exposed. Are `seqRun`/`setTo`/`effectReport` (the eval path) necessarily exposed? Could only the unfolded defs be `@[expose]`d while the evaluated path stays plain `public` (not extern), or does any public-theorem-unfolding transitively extern-ize the whole call graph?
3. **Attribute-level alternatives.** Does Lean have a way to satisfy the export/unfold rule without extern-izing for the evaluator (e.g. expose-to-theorem-checker but not to the C code generator; an `@[extern]`-free exposure; `@[csimp]`-style pairing)?
4. **Windows symbol-limit workarounds.** Any linker/PE trick (explicit export lists, `/LTCG`, lld flags) that would let a mathlib-sized shared library link on Windows? Note any solution must not require `Mathlib:shared` — mathlib upstream does not support it.
5. **Alternative evaluation commands.** Can the report UX be restored via elaboration-time reduction instead of the native interpreter — `#reduce`, `run_fun`, `native_decide`-style printing — without extern symbols?

## Reference files

- `STC/Core/Effect.lean` — `seqRun` (failing symbol), all `@[expose] public section`
- `STC/Examples/Effect.lean`, `STC/Examples/RelationResult.lean` — the two reports
- `lakefile.toml` — current minimal config (all attempted flags reverted)
- `AGENTS.md` — module-format rules, including the two constraints added from this incident
- Lake sources (fetched from `leanprover/lean4` v4.33.0): `src/lake/Lake/Config/LeanLibConfig.lean`, `src/lake/Lake/Build/Executable.lean`, `src/lake/Lake/Build/Targets/LeanLib.lean`

## Constraints

- Keep `module` + `public import` + `@[expose] public section` (repo convention, mathlib-aligned).
- Must work on Windows; no `Mathlib:shared`.
- Do not regress the green `lake build`; `scripts/scan_lean.py STC` must stay clean (exit 1).
