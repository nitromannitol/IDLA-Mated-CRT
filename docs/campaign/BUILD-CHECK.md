# Default build check: `lake build` of lean_lib MatedCRT after archive rule R2

## Run

- HEAD built: 0f68392d (2026-11-11 12:17:19 UTC). HEAD when this file was written: 3659c3ca (12:44 UTC); commits after 0f68392d were not built.
- Command: `lb MatedCRT`, which runs `lake build MatedCRT` under the shared lake lock (lakefile.lean:15-16 globs `andSubmodules MatedCRT`).
- Library target: the build ran 12285 jobs and reported 545 `MatedCRT` modules built, so the library closure was built, not only `MatedCRT.lean`.
- Result: **BUILD FAILED** (rc=1). Log: `/home/nitro/paper-fleets/mcrt/logs/lb/121719-3455814.log` (sandbox).
- Unbuilt before the run: tracked `MatedCRT/**/*.lean` and `MatedCRT.lean` are 1823 files; 3 had an `.olean` that was missing or older than the `.lean` (by modification time, no lock): 1 missing (`MatedCRT/FirstPass/S1c/Composition.lean`), 2 stale (`MatedCRT/FirstPass/S2g/GoodSetMoments.lean`, `MatedCRT/Steps/SecA/DiscreteObstacle.lean`). List: `notes/z8-unbuilt.txt`.
- Waiting: `reports/z5.md` read `TASK: p2-archive-batches-2`, `STATUS: DONE` before the run.

## Result by class

- **Class (b), inside the closure of the archive roots (real breakage): none.** All 29 failed modules are outside the closure. The closure was recomputed here from the root classes of `docs/campaign/ARCHIVE-RECHECK.md`: 236 root files (z5 counted 242, so the recomputed closure is an approximation), forward closure 1821 files.
- **Class (a), outside the closure:**
  - One tracked module: `MatedCRT/FirstPass/S1c/Composition.lean`. It stayed under `MatedCRT/` by rule R2 condition (b): named in `tasks/li.md`, which was modified 2026-11-11 12:18:37 UTC. It has no uncommitted edit; its last commit is 1b0a302f (2026-11-10). It declares `MatedCRT.firstPass_1_4`, which is also declared in `MatedCRT/FirstPass/S1d.lean:38` (in the closure). This is a real break of the default build on a clean clone: it is the only tracked module that fails.
  - Twenty-eight untracked files (not R2 candidates, which cover tracked files only). They were present in the working tree at build time. Seventeen were later moved to `archive/untracked-20261111/` by someone other than me, and eleven imported modules that have no file (see the table).
- Tracked files that import any of the 29 failed modules: none (exact-name grep over `git ls-files`). The untracked failures therefore do not reach the tracked tree.

## Failed modules

| # | module | file | tracked | in closure | class | first error (one line) |
|---|---|---|---|---|---|---|
| 1 | MatedCRT.FirstPass.S1c.Composition | MatedCRT/FirstPass/S1c/Composition.lean | yes | no | (a), R2 (b) | 17:8 `MatedCRT.firstPass_1_4` has already been declared (also S1d.lean:38) |
| 2 | MatedCRT.FirstPass.S4d.AxProbe42 | MatedCRT/FirstPass/S4d/AxProbe42.lean | no | no | (a), untracked | no error line captured |
| 3 | MatedCRT.Audit.RefutationsProbe | MatedCRT/Audit/RefutationsProbe.lean | no | no | (a), untracked | no error line captured |
| 4 | MatedCRT.Proofs.Field.ConeProbe | MatedCRT/Proofs/Field/ConeProbe.lean | no | no | (a), untracked | no error line captured |
| 5 | MatedCRT.Proofs.LBM.DirichletDiscProbe | MatedCRT/Proofs/LBM/DirichletDiscProbe.lean | no | no | (a), untracked | build failed (dependency) |
| 6 | MatedCRT.Proofs.IDLA.NamesY2 | MatedCRT/Proofs/IDLA/NamesY2.lean | no | no | (a), untracked | not attributed (log lines of parallel jobs interleave) |
| 7 | MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.NameCheck | MatedCRT/Proofs/Sec6/ConstantOrderLowerBound/NameCheck.lean | no | no | (a), untracked | not attributed |
| 8 | MatedCRT.Proofs.WalkPotential.Scratch | MatedCRT/Proofs/WalkPotential/Scratch.lean | no | no | (a), untracked | summary only: "some modules have bad imports or could not be read" |
| 9 | MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.Decomposition | MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/Decomposition.lean | no | no | (a), untracked | 40:53 Unknown identifier `srwLaw_nonadjacent_null` |
| 10 | MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExternalConeScalePositivity | MatedCRT/Proofs/Sec4/ConvergenceDivisible/ExternalConeScalePositivity.lean | no | no | (a), untracked | 94:37 Invalid field `measurableSet_eq` (`Function.measurableSet_eq` not in the environment) |
| 11-18 | MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.{ApproxClockAxiomsY5, DirichletGMCAxiomsY5, EnergyAxiomsY5, GMCExpectationAxiomsY5, GMCVersionL1AxiomsY5, JointL1AxiomsY5, OccupationMassLimitAxiomsY5, WholePlaneClockAxiomsY5} | same directory, `.lean` | no | no | (a), untracked; 17 of the 28 untracked modules now under `archive/untracked-20261111/` | bad import of a module with no file (names in the log) |
| 19-29 | MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.{ClockGMCNormalization, ConditionalMassBound, DirichletCircleMeasurable, DirichletGMCExpectation, GMCExpectation, GMCVersionComparison, JointL1Convergence, OccupationMassExpectation, PathOccupationEnergy, PlanarBrownianIncrement, WholePlaneClockExpectation} | no file ever tracked | no | no | (a), phantom import | no such file or directory (error code 2) |

Rows 11-18 fail with "bad import" of the phantom modules of rows 19-29, which have no file.

## Notes for the lead

- The break that matters for a clean clone is row 1: `MatedCRT/FirstPass/S1c/Composition.lean` duplicates `MatedCRT.firstPass_1_4` (also `MatedCRT/FirstPass/S1d.lean:38`, which is in the closure). Its only importer is `archive/MatedCRT/FirstPass/S1c/FinalAxioms.lean`. The file is in the active work of z1 (commit 1b0a302f) and is named in `tasks/li.md`; not fixed here.
- Rows 2-29 are untracked files that were in the working tree of the build. A clean clone does not contain them. Predicted clone result: `lake build` fails at row 1 only. Not verified: a clone build needs a separate checkout, not run here (one `lb` run).
- Not run: a second build at HEAD 3659c3ca.
