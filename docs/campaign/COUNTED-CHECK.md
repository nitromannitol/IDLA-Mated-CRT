# COUNTED.md declaration check

Checks every row of the Table in `docs/campaign/COUNTED.md` (lines 197–264, including the LP forms, the audit rows m1 and B6, and the `_noSup` counted forms), the Appendix B rows (lines 265–277), and every declaration that COUNTED.md names only in its prose (lines 1–196; first match under `MatedCRT/`).

Checked at HEAD 00098347 (2026-11-11 14:37 UTC). Declarations, tracking and hashes are read at that HEAD (the sandbox working tree, which has no uncommitted edit in any file of the 53 row files). The last commit to COUNTED.md is 10d46a40 (2026-11-11 13:29:59 UTC), before this check.

**Axioms are not a clean-HEAD result.** They come from the work-comp build `llb MatedCRT.Audit.CountedAxioms` (log `lb-143151-1415935.log` in the work-comp mirror), which synced the sandbox working tree at about 14:45 UTC. That tree has 76 uncommitted modified `.lean` files in the import closure of `CountedAxioms.lean`: 9 in `MatedCRT/` (including `MatedCRT/Audit/CountedAxioms.lean` itself, which is committed with this file) and 67 in `Harmonic-Balls-LQG/HarmonicBalls/`. None of the 53 row files is among them. The axiom column therefore describes the working tree at build time. A clean-HEAD axiom check is open (see Notes).

## Method

1. Declaration: the file named in the row is searched for the declaration keyword line (theorem, lemma, def, abbrev, structure, class, instance); the actual line is compared with the stated line. Prose-only names are searched under `MatedCRT/` (first match) and carry no stated line. The fully qualified name uses the namespace in force at the declaration.
2. Tracking: `git ls-files --error-unmatch`. Hashes: each 7–40-hex token in the row is checked with `git cat-file -t` and must be a commit.
3. Axioms: one `#print axioms` per distinct declaration in `MatedCRT/Audit/CountedAxioms.lean` (tracked; 53 imports; 116 print lines, one per distinct declaration), built with `llb` on work-comp (see the header). "std" means exactly `propext, Classical.choice, Quot.sound`. The log lines are wrapped by Lake; they were joined before the check (`scratch-z8/buildlog-ax.txt`).

Fleet scripts (scratch, not committed): `/home/nitro/paper-fleets/mcrt/scratch-z8/` (`gen_raw.sh` builds the row list, `check_rows.sh` runs steps 1–2, `mk.sh` joins step 3 and writes the table).

## Summary

- Rows checked: 128 = Table 60, Appendix B 4, prose-only names 64. Of the Table rows, 13 name a `_noSup` declaration (rows 1.4, 1.4n, 1.6, 1.6n, 5.1, 5.1lp, 6.1, 6.1lp, 8.1, 8.1lp, B6 ×2, m1).
- Distinct declarations: 116. Found: 128 of 128 rows. Missing: 0. Tracked by git: 128 of 128. Wrong line: 0.
- Axioms: 116 of 116 distinct declarations report exactly `propext, Classical.choice, Quot.sound` on the working tree described above. Non-standard: 0. sorryAx: 0.
- `_noSup` declarations: 8, all in `MatedCRT/FirstPass/Closure/LssDerived.lean` (lines 54, 95, 136, 193, 257, 295, 353, 396), all std.
- Commit hashes cited: 31; all are commits; unknown: 0.
- Rows OK: 128 of 128. Mismatches: 0.

## Mismatches for z1 (COUNTED.md line numbers)

None at HEAD 00098347.

## Changes since the previous check (3cd8222b; axioms at 689539f8)

- The Table moved to COUNTED.md lines 197–264 (was 193–260); Appendix B to lines 265–276.
- The counted forms switched to the `_noSup` wrappers (z1 ledger switch, 89ec667d; the declarations were committed in 3588558d): 13 rows now name `closed_1_4_lp_noSC_noSup`, `closed_1_6_lp_noSC_noSup`, `firstPassMain_1_4_full_noSup`, `firstPassMain_1_6_full_noSup`, `closed_5_1_lp_noSup`, `closed_6_1_lp_noSup`, `closed_8_1_lp_noSup` and `closed_5_1_cellRewire_noSup`.
- `MatedCRT/Audit/CountedAxioms.lean`: one import added (`MatedCRT.FirstPass.Closure.LssDerived`; 53 imports, was 52) and eight `#print axioms` lines added for the `_noSup` declarations (116 distinct, was 108). Every earlier line is kept.
- Rows 120 → 128; distinct declarations 108 → 116.
- Prose-only names: the earlier list of 56 cannot be reproduced from the current text. This run re-derives it: backticked names containing `_` or `.` in lines 1–196 that the Table does not name, first match under `MatedCRT/`. The result is 64 names.
- Two prose names are not rows, because no declaration keyword line exists under `MatedCRT/`. Both were checked by hand. `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling` is a module path; the file exists in the Lattice-Probability checkout (`LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/IsMatingOfTreesCoupling.lean`). `MatedCRTEnv.IsValid` is a structure at `MatedCRT/Defs/Setting.lean:142`; COUNTED.md's prose cites `:141`, the docstring line above it. Neither is axiom-checked.

## Notes

- Working tree versus HEAD (axioms only). At the build, the uncommitted `.lean` files in the closure were: `MatedCRT/Audit/CountedAxioms.lean` (this run's edit), `MatedCRT/FirstPass/LPBridge/LateralGaussian.lean`, `MatedCRT/FirstPass/LPBridge/WholePlaneGFFLateral.lean`, `MatedCRT/FirstPass/S1c/TestLocal.lean`, `MatedCRT/FirstPass/S2g/AllDisks.lean`, `MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/LaplacianTranslation.lean`, `MatedCRT/Proofs/Sec3/UniformConvergenceGreenKernel/HarmonicTranslation.lean`, `MatedCRT/Proofs/Sec4/ObstacleSpecialization.lean`, `MatedCRT/Proofs/Sec5/SupersolutionBorelCode.lean`, and 67 `HarmonicBalls/` files (Defs, Proofs/Potential, Proofs/Sec11, and others; list reproducible with `scratch-z8/closure_dirty.sh`). Their owners are not this check's. A clean-HEAD axiom run needs those files committed or a clean-clone build (operator decision).
- The line `#print axioms for every declaration counted in ...` (`CountedAxioms.lean:56`) is inside a comment; it is not a command.
- Prose-only names are declaration-like names in lines 1–196 that the Table does not name. The check reports whether each exists and is axiom-clean; it does not decide whether a prose name is a counted declaration. Some are superseded forms, for example `closed_1_4_full` and `closed_1_6_full`, which the Table no longer uses; both exist.

## Full table

| COUNTED.md line | Row | Declaration | file | declared at | stated line | tracked | commit hashes (type) | #print axioms | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 204 | 1.4 | `closed_1_4_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 54 | 54 | yes | - | std | OK |
| 205 | 1.4n | `closed_1_4_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 54 | 54 | yes | 17ca4173 (commit) | std | OK |
| 206 | 1.6 | `closed_1_6_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 95 | 95 | yes | - | std | OK |
| 207 | 1.6n | `closed_1_6_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 95 | 95 | yes | 17ca4173 (commit) | std | OK |
| 208 | 2.3 | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 37 | 37 | yes | - | std | OK |
| 209 | 2.3n | `closed_2_3_lit_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean | 166 | 166 | yes | - | std | OK |
| 210 | 2.4 | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 77 | 77 | yes | - | std | OK |
| 211 | 2.5 | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 99 | 99 | yes | - | std | OK |
| 212 | 2.6 | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 122 | 122 | yes | - | std | OK |
| 213 | 2.3lp | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 37 | 37 | yes | 8a716fde (commit) | std | OK |
| 214 | 2.4lp | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 77 | 77 | yes | 8a716fde (commit) | std | OK |
| 215 | 2.5lp | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 99 | 99 | yes | 8a716fde (commit) | std | OK |
| 216 | 2.6lp | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 122 | 122 | yes | 8a716fde (commit) | std | OK |
| 217 | 2.13 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 21 | 21 | yes | - | std | OK |
| 218 | 2.17 | `firstPass_2_17_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 85 | 85 | yes | - | std | OK |
| 219 | 2.19 | `closed_2_19_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 39 | 39 | yes | - | std | OK |
| 220 | 3.1 | `firstPass_3_1_faithful` | MatedCRT/FirstPass/S3c.lean | 125 | 125 | yes | - | std | OK |
| 221 | 3.3 | `closed_3_3_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 45 | 45 | yes | - | std | OK |
| 222 | 3.4 | `closed_3_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 51 | 51 | yes | - | std | OK |
| 223 | 3.5 | `closed_3_5_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 45 | 45 | yes | - | std | OK |
| 224 | 3.6 | `closed_3_6_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 53 | 53 | yes | - | std | OK (superseded form; kept by name) |
| 224 | 3.6 | `closed_3_6_lp_uniform` | MatedCRT/FirstPass/Closure/CleanSec23LPUniform.lean | 30 | 30 | yes | 5953dbf2 (commit) | std | OK (axioms: working tree, lb log 172523-1146840.log; label "working tree") |
| 225 | 3.7 | `closed_3_7_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 61 | 61 | yes | - | std | OK |
| 226 | 4.1 | `closed_4_1_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 30 | 30 | yes | a4ac5fc6 (commit), e7a5833 (commit) | std | OK |
| 227 | 4.2 | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 47 | 47 | yes | - | std | OK |
| 228 | 4.3 | `closed_4_3` | MatedCRT/FirstPass/Closure/Section4.lean | 18 | 18 | yes | - | std | OK |
| 229 | 4.4 | `closed_4_4` | MatedCRT/FirstPass/Closure/Section4.lean | 22 | 22 | yes | - | std | OK |
| 230 | 4.5 | `closed_4_5` | MatedCRT/FirstPass/Closure/Section4.lean | 27 | 27 | yes | - | std | OK |
| 231 | 4.6 | `firstPass_4_6_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 74 | 74 | yes | e7a5833 (commit) | std | OK |
| 232 | 4.7 | `closed_4_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 65 | 65 | yes | - | std | OK |
| 233 | 4.8 | `closed_4_8_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 38 | 38 | yes | a4ac5fc6 (commit) | std | OK |
| 234 | 5.1 | `closed_5_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 353 | 353 | yes | a1339bd (commit) | std | OK |
| 235 | 5.2 | `closed_5_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 79 | 79 | yes | - | std | OK |
| 236 | 5.3 | `closed_5_3_clean` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 109 | 109 | yes | bb7e1297 (commit), ecfbc55 (commit) | std | OK |
| 237 | 5.4 | `closed_5_4_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean | 73 | 73 | yes | a1339bd (commit) | std | OK |
| 238 | 6.1 | `closed_6_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 257 | 257 | yes | 2fb105c (commit) | std | OK |
| 239 | 6.1lp | `closed_6_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 257 | 257 | yes | 7b19a40a (commit) | std | OK |
| 240 | 6.4 | `closed_6_4_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 45 | 45 | yes | a4ac5fc6 (commit) | std | OK |
| 241 | 6.5 | `firstPass_6_5_uniform` | MatedCRT/FirstPass/S6q.lean | 26 | 26 | yes | - | std | OK |
| 242 | 6.7 | `firstPass_6_7` | MatedCRT/FirstPass/LIClosed68Y.lean | 30 | 30 | yes | - | std | OK |
| 243 | 6.8 | `firstPass_6_8` | MatedCRT/FirstPass/LIClosed68Y.lean | 40 | 40 | yes | - | std | OK |
| 244 | 6.9 | `firstPass_6_9` | MatedCRT/FirstPass/LIClosed68Y.lean | 51 | 51 | yes | - | std | OK |
| 245 | 6.10 | `closed_6_10_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 52 | 52 | yes | a4ac5fc6 (commit) | std | OK |
| 246 | 7.1 | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 84 | 84 | yes | 84ed358 (commit) | std | OK |
| 247 | 7.1lp | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 84 | 84 | yes | 7b19a40a (commit) | std | OK |
| 248 | 7.2 | `closed_7_2` | MatedCRT/FirstPass/Closure/Section7.lean | 18 | 18 | yes | - | std | OK |
| 249 | 7.3 | `closed_7_3` | MatedCRT/FirstPass/Closure/Section7.lean | 23 | 23 | yes | - | std | OK |
| 250 | 8.1 | `closed_8_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 295 | 295 | yes | a9bd0055 (commit) | std | OK |
| 251 | 8.1lp | `closed_8_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 295 | 295 | yes | a04b0cb4 (commit) | std | OK |
| 252 | 4.2lp | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 47 | 47 | yes | e2d3bf22 (commit) | std | OK |
| 253 | 5.1lp | `closed_5_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 353 | 353 | yes | e2d3bf22 (commit) | std | OK |
| 254 | 5.3lp | `closed_5_3_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 108 | 108 | yes | e2d3bf22 (commit) | std | OK |
| 255 | 5.4lp | `closed_5_4_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 130 | 130 | yes | e2d3bf22 (commit) | std | OK |
| 256 | A.1 | `discreteDivergenceTheorem` | MatedCRT/Proofs/SecA/DiscreteDivergence.lean | 54 | 54 | yes | - | std | OK |
| 257 | A.2 | `discreteBasicPropertiesGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 62 | 62 | yes | - | std | OK |
| 258 | A.3 | `discreteLaplacianBoundGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 66 | 66 | yes | - | std | OK |
| 259 | A.4 | `discreteConservationOfMassGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 71 | 71 | yes | - | std | OK |
| 260 | B6 | `firstPassMain_1_4_full_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 136 | 136 | yes | - | std | OK |
| 261 | B6 | `firstPassMain_1_6_full_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 193 | 193 | yes | - | std | OK |
| 262 | m1 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 21 | 21 | yes | - | std | OK |
| 263 | m1 | `closed_5_1_cellRewire_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean | 396 | 396 | yes | - | std | OK |
| 271 | AppB | `frozenLBMGreenOccupationRescaled_closed` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure.lean | 35 | 35 | yes | 7a508a1 (commit) | std | OK |
| 272 | AppB | `frozenLBMGreenOccupationRescaled_closed2` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure2.lean | 32 | 32 | yes | 582e360 (commit), 6675b36 (commit) | std | OK |
| 273 | AppB | `frozenLBMGreenOccupationRescaled_closed3` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure3.lean | 68 | 68 | yes | 23f4c7e6 (commit) | std | OK |
| 274 | AppB | `frozenLBMGreenOccupationRescaled_closed4` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure4.lean | 76 | 76 | yes | d90cbe4e (commit) | std | OK |
| 275 | AppB | `frozenLBMGreenOccupationRescaled_closed5` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure5.lean | 19 | 19 | yes | d51a926b (commit) | std | OK |
| 0 | prose | `MatedCRT.GFFExistence.exists_harmonicBalls_isWholePlaneGFF` | MatedCRT/FirstPass/LPBridge/GFFExistence.lean | 22 | not stated | yes | - | std | OK |
| 0 | prose | `MatedCRT.S2VG.LitExistence` | MatedCRT/FirstPass/S2VG/Literature.lean | 44 | not stated | yes | - | std | OK |
| 0 | prose | `MatedCRT.ratPoint` | MatedCRT/FirstPass/S2g/LawCode.lean | 24 | not stated | yes | - | std | OK |
| 0 | prose | `MatedCRT.rationalGridPoint` | MatedCRT/Proofs/Sec4/SubsequentialProperties/CircleAverage.lean | 23 | not stated | yes | - | std | OK |
| 0 | prose | `closed_1_4_full` | MatedCRT/FirstPass/Closure/Final14Full.lean | 21 | not stated | yes | - | std | OK |
| 0 | prose | `closed_1_4_lp` | MatedCRT/FirstPass/Closure/Final14LP.lean | 35 | not stated | yes | - | std | OK |
| 0 | prose | `closed_1_4_lp_noSC` | MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean | 24 | not stated | yes | - | std | OK |
| 0 | prose | `closed_1_6_full` | MatedCRT/FirstPass/Closure/Final14Full.lean | 89 | not stated | yes | - | std | OK |
| 0 | prose | `closed_1_6_lp` | MatedCRT/FirstPass/Closure/Final14LP.lean | 89 | not stated | yes | - | std | OK |
| 0 | prose | `closed_1_6_lp_noSC` | MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean | 73 | not stated | yes | - | std | OK |
| 0 | prose | `closed_2_13` | MatedCRT/FirstPass/Closure/Section2.lean | 33 | not stated | yes | - | std | OK |
| 0 | prose | `closed_2_13_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 31 | not stated | yes | - | std | OK |
| 0 | prose | `closed_2_2_lit` | MatedCRT/FirstPass/Closure/Final22.lean | 37 | not stated | yes | - | std | OK |
| 0 | prose | `closed_2_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 116 | not stated | yes | - | std | OK |
| 0 | prose | `closed_2_3_lit` | MatedCRT/FirstPass/Closure/Final23.lean | 43 | not stated | yes | - | std | OK |
| 0 | prose | `closed_3_1` | MatedCRT/FirstPass/Closure/Section3.lean | 31 | not stated | yes | - | std | OK |
| 0 | prose | `closed_3_1_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 37 | not stated | yes | - | std | OK |
| 0 | prose | `closed_3_5` | MatedCRT/FirstPass/Closure/Section3.lean | 66 | not stated | yes | - | std | OK |
| 0 | prose | `closed_3_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 57 | not stated | yes | - | std | OK |
| 0 | prose | `closed_4_2_clean` | MatedCRT/FirstPass/Closure/Chain42ConeLaw.lean | 116 | not stated | yes | - | std | OK |
| 0 | prose | `closed_4_8_corrected_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 71 | not stated | yes | - | std | OK |
| 0 | prose | `closed_5_1` | MatedCRT/FirstPass/Closure/Prop51.lean | 44 | not stated | yes | - | std | OK |
| 0 | prose | `closed_5_1_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 30 | not stated | yes | - | std | OK |
| 0 | prose | `closed_5_1_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean | 40 | not stated | yes | - | std | OK |
| 0 | prose | `closed_5_1_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 79 | not stated | yes | - | std | OK |
| 0 | prose | `closed_6_10` | MatedCRT/FirstPass/Closure/Section6.lean | 30 | not stated | yes | - | std | OK |
| 0 | prose | `closed_6_10_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 123 | not stated | yes | - | std | OK |
| 0 | prose | `closed_6_1_clean` | MatedCRT/FirstPass/Closure/Clean61And81.lean | 31 | not stated | yes | - | std | OK |
| 0 | prose | `closed_6_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 43 | not stated | yes | - | std | OK |
| 0 | prose | `closed_7_1_clean` | MatedCRT/FirstPass/Closure/Clean71.lean | 42 | not stated | yes | - | std | OK |
| 0 | prose | `closed_8_1_full` | MatedCRT/FirstPass/Closure/Clean81Full.lean | 19 | not stated | yes | - | std | OK |
| 0 | prose | `closed_8_1_lp` | MatedCRT/FirstPass/Closure/Clean81LP.lean | 43 | not stated | yes | - | std | OK |
| 0 | prose | `coneGlobalFamilyFactor_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 41 | not stated | yes | - | std | OK |
| 0 | prose | `coneGlobalFamilyFactor_proved` | MatedCRT/FirstPass/S2i/GlobalFactor.lean | 519 | not stated | yes | - | std | OK |
| 0 | prose | `coneScaleInvarianceCoded_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 52 | not stated | yes | - | std | OK |
| 0 | prose | `firstPassMain_1_4` | MatedCRT/FirstPass/Main.lean | 50 | not stated | yes | - | std | OK |
| 0 | prose | `firstPassMain_1_4_full` | MatedCRT/FirstPass/Main.lean | 112 | not stated | yes | - | std | OK |
| 0 | prose | `firstPassMain_1_6` | MatedCRT/FirstPass/Main.lean | 80 | not stated | yes | - | std | OK |
| 0 | prose | `firstPassMain_1_6_full` | MatedCRT/FirstPass/Main.lean | 172 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_2_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 133 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_2_5_canonical_p2` | MatedCRT/FirstPass/Phase2Rewire.lean | 229 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_2_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 153 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_2_6_coded_of_globalFamilyFactor` | MatedCRT/FirstPass/S2g/LawCoded.lean | 33 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_2_6_corrected_p2` | MatedCRT/FirstPass/Phase2Rewire.lean | 264 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_2_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 174 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_3_1_countable` | MatedCRT/FirstPass/S3c/CountableFamilies.lean | 97 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_3_1_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 92 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_3_6_closed` | MatedCRT/FirstPass/S3i/LensClosed.lean | 31 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_3_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 197 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_3_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 103 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_1` | MatedCRT/FirstPass/S3S4.lean | 115 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_1_coneLaw_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 48 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_1_coneLaw_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 65 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_1_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 211 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_1_ownBinders_counted` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 62 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_1_ownBinders_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 36 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_2_final` | MatedCRT/FirstPass/S4d.lean | 146 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_2_final_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 217 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_4_6_corrected` | MatedCRT/FirstPass/S3S4.lean | 102 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_5_4` | MatedCRT/FirstPass/S5S6S7.lean | 42 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_6_1_corrected` | MatedCRT/FirstPass/S2g/Assembly2456.lean | 31 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_6_4_uniform` | MatedCRT/FirstPass/S6p.lean | 213 | not stated | yes | - | std | OK |
| 0 | prose | `firstPass_7_1` | MatedCRT/FirstPass/S5S6S7.lean | 98 | not stated | yes | - | std | OK |
| 0 | prose | `volumeGrowthStmt_of_berestyckiGwynne` | MatedCRT/Proofs/Sec3/ConeBallMass.lean | 17 | not stated | yes | - | std | OK |
