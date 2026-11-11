# LP staging sync check: MatedCRT/LPStaging against LatticeProb

> **Superseded 2026-11-11.** The in-repository copies were archived (HB 2478ebc4: `archive/HarmonicBalls/LPStage`; IDLA 741a5360:
> `archive/MatedCRT/LPStaging`). Both papers import `LatticeProb.*` from the pinned Lattice-Probability revision 8fcf846.
> The text below records the state before the archive move.


Task p2-lpstaging-sync-check (lead, 2026-11-11). Read-only on both trees: no Lean file edited, nothing built.

Snapshots checked on 2026-11-11:
- IDLA repository at HEAD a4c9710e. MatedCRT/LPStaging: 37 tracked files and 7 untracked probe files; no uncommitted change to a tracked LPStaging or LPBridge file.
- LP worktree /home/nitro/lean/LP-idla-phase2, branch idla/phase2, HEAD 8354077. LatticeProb/ is clean.
- IDLA pin: lake-manifest.json, `lattice-probability` inputRev 3912597a. Several staging headers cite 3912597 as their port source ("Port of LatticeProb.X (Lattice-Probability 3912597)").
- Mathlib rev 065356127b1d and toolchain leanprover/lean4:v4.35.0-rc2 are identical in the IDLA manifest, the LP worktree manifest and the pinned package.

## Verdict: BLOCKED (the switch is not ready)

- **B1 (pin; blocks the switch as it stands).** The pinned revision 3912597 lacks 10 modules that the IDLA tree imports through LPStaging: Analysis/DistributionalLaplacian, Analysis/PuncturedPlaneConnected, Analysis/SuperharmonicMinimumPrinciple, Gauss/GaussianProcessLawExt, Prob/AnalyticUniversalMeasurable, Prob/BrownianOutwardExcursion, Prob/CameronMartinEquivalence, Prob/FiniteMeasureStandardBorel, Prob/PlanarBrownianGermZeroOne, Prob/VagueLimitMeasurable. Twelve import lines in ten LPBridge files need them (part 3). Three further counterparts (Analysis/RotationalAverage, Prob/AeLimitLaw, Prob/BrownianFrequentPositivity) are absent at the pin but no IDLA file imports them. The 20 counterparts that the pin does contain are declaration-identical to the mirror. Lakefile line 11 already requires `lattice-probability`, so the fix is a manifest entry, not a new require. That edit is the operator's.
- **B2 (revision not on a remote, as far as the local clone shows).** LP 8354077 is contained in no remote-tracking ref of the LP clone; only the local branch idla/phase2 contains it. The origin is git@github.com:nitromannitol/Lattice-Probability.git. A manifest pin to 8354077 needs a push first (operator). The local refs may be stale because the clone has not been fetched.
- **B3 (bump content not verified).** 139 commits lie between 3912597 and 8354077. Only the 33 mirror counterparts were compared. The 38 distinct `LatticeProb.*` modules that MatedCRT imports today (mirror included) exist both at the pin and in the LP worktree, but their content at 8354077 was not compared. A bump needs an IDLA build (operator).

Not blockers:
- Four Bonanno mirror files are MISSING IN LP at the mirror path. None is imported by IDLA. In LP they moved to LatticeProb/Bonanno/LQGMetric/Field/ with identical declarations.
- Seven z8Probe files are untracked and MISSING IN LP. None is imported by IDLA.
- The 20 DIFFERS files were synced by the content task (see the sync record in part 1): IDENTICAL after the sync.

## Method

- Counterpart: MatedCRT/LPStaging/P.lean corresponds to LatticeProb/P.lean (same relative path) in the LP worktree. The four Bonanno files are the exception (part 1).
- IDENTICAL: `diff` after rewriting `MatedCRT.LPStaging.` to `LatticeProb.` shows no differing line.
- Declarations: for each file, every theorem, lemma, def, abbrev, instance, structure, class and inductive is keyed by name, with its header text (keyword up to `:=`, comments removed, whitespace normalized). "Same type" means identical header text, binders included. This is a textual check; a Lean build of the switch is the real check.
- Structural lines (open, variable, namespace, end, section, universe, set_option, attribute, notation, import, `@[`) do not differ in any file.
- Limit: anonymous instances are keyed by line number. None differs.

## 1. Per-file status (44 rows)

Status: IDENTICAL = no differing line after import rewrite. DIFFERS = proof or comment lines differ; declaration names and header text identical (N = differing lines). MISSING IN LP = no counterpart at the mirror path. "Pin" = file present in the pinned package at 3912597. "IDLA importers" = files outside MatedCRT/LPStaging that import the file; all of them are FirstPass/LPBridge/*.lean.

| # | Mirror file (MatedCRT/LPStaging/) | Tracked | LP counterpart | Status | Decls (same names and types) | IDLA importers (LPBridge) | Pin |
|---|---|---|---|---|---|---|---|
| 1 | Analysis/DistributionalLaplacian | yes | LatticeProb/Analysis/DistributionalLaplacian.lean | IDENTICAL | 48 | DistributionalLaplacian, MinimumPrinciples | MISSING |
| 2 | Analysis/PuncturedPlaneConnected | yes | LatticeProb/Analysis/PuncturedPlaneConnected.lean | IDENTICAL | 6 | PunctureConnected | MISSING |
| 3 | Analysis/RotationalAverage | yes | LatticeProb/Analysis/RotationalAverage.lean | IDENTICAL | 17 | none | MISSING |
| 4 | Analysis/SuperharmonicMinimumPrinciple | yes | LatticeProb/Analysis/SuperharmonicMinimumPrinciple.lean | IDENTICAL | 7 | MinimumPrinciples | MISSING |
| 5 | Analysis/z8ProbeAll | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 6 | Analysis/z8ProbeAxioms | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 7 | Analysis/z8ProbeB | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 8 | Analysis/z8ProbeC | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 9 | Analysis/z8ProbeF | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 10 | Analysis/z8ProbeLap | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 11 | Analysis/z8ProbeT | no | none (untracked probe) | MISSING IN LP | - | none | MISSING |
| 12 | Bonanno/CircleAvgVersion | yes | none at mirror path; moved to LatticeProb/Bonanno/LQGMetric/Field/CircleAvgVersion.lean | MISSING IN LP (moved, declarations identical) | 2 | none | MISSING |
| 13 | Bonanno/CircleParameter | yes | none at mirror path; moved to LatticeProb/Bonanno/LQGMetric/Field/CircleParameter.lean | MISSING IN LP (moved, declarations identical) | 2 | none | MISSING |
| 14 | Bonanno/LQGMeasureFieldMeasurable | yes | none at mirror path; moved to LatticeProb/Bonanno/LQGMetric/Field/LQGMeasureFieldMeasurable.lean | MISSING IN LP (moved, declarations identical) | 24 | none | MISSING |
| 15 | Bonanno/WholePlaneCov | yes | none at mirror path; moved to LatticeProb/Bonanno/LQGMetric/Field/WholePlaneCov.lean | MISSING IN LP (moved, declarations identical) | 9 | none | MISSING |
| 16 | Gauss/Brownian | yes | LatticeProb/Gauss/Brownian.lean | IDENTICAL | 9 | none | ok |
| 17 | Gauss/BrownianCont | yes | LatticeProb/Gauss/BrownianCont.lean | IDENTICAL | 11 | none | ok |
| 18 | Gauss/Coords | yes | LatticeProb/Gauss/Coords.lean | IDENTICAL | 6 | none | ok |
| 19 | Gauss/GaussianProcessLawExt | yes | LatticeProb/Gauss/GaussianProcessLawExt.lean | IDENTICAL | 6 | ConeMeanZeroRestrictionFinal | MISSING |
| 20 | Gauss/Isonormal | yes | LatticeProb/Gauss/Isonormal.lean | IDENTICAL | 17 | none | ok |
| 21 | Gauss/Limit | yes | LatticeProb/Gauss/Limit.lean | IDENTICAL | 1 | none | ok |
| 22 | Gauss/Process | yes | LatticeProb/Gauss/Process.lean | IDENTICAL | 10 | none | ok |
| 23 | Gauss/WhiteNoise | yes | LatticeProb/Gauss/WhiteNoise.lean | IDENTICAL | 28 | none | ok |
| 24 | Prob/AeLimitLaw | yes | LatticeProb/Prob/AeLimitLaw.lean | IDENTICAL | 3 | none | MISSING |
| 25 | Prob/AnalyticUniversalMeasurable | yes | LatticeProb/Prob/AnalyticUniversalMeasurable.lean | IDENTICAL | 5 | UniversalMeasurability | MISSING |
| 26 | Prob/BrownianContAll | yes | LatticeProb/Prob/BrownianContAll.lean | IDENTICAL | 6 | none | ok |
| 27 | Prob/BrownianExit | yes | LatticeProb/Prob/BrownianExit.lean | IDENTICAL | 12 | none | ok |
| 28 | Prob/BrownianFrequentPositivity | yes | LatticeProb/Prob/BrownianFrequentPositivity.lean | IDENTICAL | 16 | none | MISSING |
| 29 | Prob/BrownianGermZeroOne | yes | LatticeProb/Prob/BrownianGermZeroOne.lean | IDENTICAL | 14 | none | ok |
| 30 | Prob/BrownianMarkov | yes | LatticeProb/Prob/BrownianMarkov.lean | IDENTICAL | 9 | none | ok |
| 31 | Prob/BrownianMax | yes | LatticeProb/Prob/BrownianMax.lean | IDENTICAL | 9 | none | ok |
| 32 | Prob/BrownianOpenExitFinite | yes | LatticeProb/Prob/BrownianOpenExitFinite.lean | IDENTICAL | 10 | none | ok |
| 33 | Prob/BrownianOpenExitStopping | yes | LatticeProb/Prob/BrownianOpenExitStopping.lean | IDENTICAL | 9 | none | ok |
| 34 | Prob/BrownianOutwardExcursion | yes | LatticeProb/Prob/BrownianOutwardExcursion.lean | IDENTICAL | 35 | ExitRestartLimit, BrownianOutwardExcursion | MISSING |
| 35 | Prob/BrownianPathLaw | yes | LatticeProb/Prob/BrownianPathLaw.lean | IDENTICAL | 3 | ExitRestartCanonical | ok |
| 36 | Prob/BrownianStrongMarkov | yes | LatticeProb/Prob/BrownianStrongMarkov.lean | IDENTICAL | 12 | none | ok |
| 37 | Prob/BrownianTail | yes | LatticeProb/Prob/BrownianTail.lean | IDENTICAL | 1 | none | ok |
| 38 | Prob/CameronMartinEquivalence | yes | LatticeProb/Prob/CameronMartinEquivalence.lean | IDENTICAL | 2 | PairingLawIG4 | MISSING |
| 39 | Prob/FiniteMarginal | yes | LatticeProb/Prob/FiniteMarginal.lean | IDENTICAL | 6 | none | ok |
| 40 | Prob/FiniteMeasureStandardBorel | yes | LatticeProb/Prob/FiniteMeasureStandardBorel.lean | IDENTICAL | 31 | FiniteMeasureStandardBorel | MISSING |
| 41 | Prob/PlanarBrownianGermZeroOne | yes | LatticeProb/Prob/PlanarBrownianGermZeroOne.lean | IDENTICAL | 7 | BrownianOutwardExcursion | MISSING |
| 42 | Prob/TrivialSigma | yes | LatticeProb/Prob/TrivialSigma.lean | IDENTICAL | 9 | none | ok |
| 43 | Prob/TrivialSigmaJoin | yes | LatticeProb/Prob/TrivialSigmaJoin.lean | IDENTICAL | 9 | none | ok |
| 44 | Prob/VagueLimitMeasurable | yes | LatticeProb/Prob/VagueLimitMeasurable.lean | IDENTICAL | 2 | LQGTestIntegralMeasurable | MISSING |

Totals after the content sync (p2-lpstaging-sync-content): IDENTICAL 33; DIFFERS 0; MISSING IN LP 11 (4 tracked Bonanno files moved in LP, 7 untracked probes). Total 44.

Probe notes: the seven z8Probe files are untracked. Analysis/z8ProbeAxioms imports Analysis/DistributionalLaplacian, which is inside LPStaging. No file outside LPStaging imports any probe.

## 2. `_holds` concluders in MatedCRT/FirstPass/LPBridge (16 in 13 files)

"LP source" = the LatticeProb declaration named in the concluder's proof text (`LatticeProb.`-qualified, or a bare name that matches a mirror declaration). "Helper" = an IDLA declaration the proof calls, with the LP name it uses one hop further. Name and type checks: every LP name listed exists in the LP counterpart with an identical header (part 1). Pin = presence of the mirror file in the pinned package.

| # | Concluder (file:line) | In closed_8_1_lp | LP source(s) | LP same name and type | Pin | Note |
|---|---|---|---|---|---|---|
| 1 | frozenLQGTestIntegralMeasurable_holds (LQGTestIntegralMeasurable.lean:49) | hmeasT | aemeasurable_integral_of_vague_limit (Prob/VagueLimitMeasurable) | yes | MISSING | file imports the pin-missing module |
| 2 | lateralProcessAEMeasurable_holds (LateralProcessAEMeasurable.lean:18) | no | none; calls MatedCRT.CirclePairing.aemeasurable_lateralProcess (Proofs/Measurability/ConePairing.lean:263), not traced further | n/a | n/a | no LPStaging import in the file |
| 3 | frozenBrownianOutwardExcursionAtExit_holds (BrownianOutwardExcursion.lean:113) | hexc | none in the body; helper frozenBrownianOutwardExcursionAtExit_of_restart (:83) uses isTrivialSigma_iInf_bmPast (Prob/BrownianGermZeroOne) | yes (helper's LP name) | ok for that name; file imports Prob/BrownianOutwardExcursion and Prob/PlanarBrownianGermZeroOne, both MISSING | ExitRestart.exit_restart_planar is IDLA-internal |
| 4 | frozenLQGMeasureFieldMeasurable_holds (InRepoProofs.lean:35) | hμae | none; calls LQGMeasureField.lqgMeasureFieldMeasurableStep (Proofs/Measurability/LQGMeasureField.lean:75) | n/a | n/a | token exists_measurable_vagueLimit is IDLA's own (Proofs/Measurability/VagueMeasurable.lean:133), not Bonanno/LQGMeasureFieldMeasurable |
| 5 | fpLQGMeasureLocality_holds (InRepoProofs.lean:45) | hLoc | none; body is LQGMeasureLocalityFunctionalStep_proof (IDLA) | n/a | n/a | |
| 6 | frozenSuperharmonicMinimumPrinciple_holds (MinimumPrinciples.lean:22) | hmin | SuperMeanValueOn, SuperMeanValueOn.minimum_principle_of_frontier (Analysis/SuperharmonicMinimumPrinciple); superMeanValueOn_of_distribLaplacianLE (Analysis/DistributionalLaplacian); helper laplacianLE_iff_distribLaplacianLE (LPBridge/DistributionalLaplacian.lean:16) uses DistribLaplacianLE | yes | MISSING | |
| 7 | fpStrongMinimumPrinciple_holds (MinimumPrinciples.lean:30) | hsmp | SuperMeanValueOn, SuperMeanValueOn.strong_minimum_principle_of_nonneg (Analysis/SuperharmonicMinimumPrinciple); superMeanValueOn_of_distribLaplacianLE (Analysis/DistributionalLaplacian); helper uses DistribLaplacianLE | yes | MISSING | |
| 8 | frozenFiniteMeasureDiskStandardBorel_holds (FiniteMeasureStandardBorel.lean:18) | hSB | standardBorelSpace_concentrated, standardBorelSpace_finiteMeasure (Prob/FiniteMeasureStandardBorel) | yes | MISSING | |
| 9 | coneRadialAbsIntegrable_holds (ConeRadialAbsIntegrable.lean:274) | no | none in the body; unfolds IDLA def ConeRadialAbsIntegrable (ConeMeanZeroRestriction.lean:409), whose text contains IsTestFunction (Analysis/DistributionalLaplacian), not traced | n/a | n/a | no LPStaging import in the file |
| 10 | fpPairingLawIG4_holds (PairingLawIG4.lean:81) | hpair | gaussian_map_shift_absolutelyContinuous, map_absolutelyContinuous_of_absolutelyContinuous (Prob/CameronMartinEquivalence) | yes | MISSING | |
| 11 | gffRadialBrownian_holds (GFFRadialBrownian.lean:25) | no | none matched in the body | n/a | n/a | |
| 12 | lateralLawFinite_holds (ConeMeanZeroRestrictionFinal.lean:117) | no | map_eq_of_mean_cov_fin (Gauss/GaussianProcessLawExt) | yes | MISSING | file imports the pin-missing module |
| 13 | fpConeMeanZeroRestriction_holds (ConeMeanZeroRestrictionFinal.lean:144) | hR | none in the body (fpConeMeanZeroRestriction_of_radialLateralIndep gffRadialLateralIndep_holds); helper not traced | n/a | file imports Gauss/GaussianProcessLawExt, MISSING | used as ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds |
| 14 | frozenPunctureConnected_holds (PunctureConnected.lean:15) | hpc | IsOpen.isConnected_diff_singleton (Analysis/PuncturedPlaneConnected) | yes | MISSING | |
| 15 | gffRadialLateralIndep_holds (GFFRadialLateralIndep.lean:1029) | no | none in the body; calls gffRadialLateralIndep_aux (IDLA, :939), whose text contains the bare tokens IsTestFunction and pairing (not verified as LP uses) | n/a | n/a | |
| 16 | frozenUniversalMeasurabilityOfAnalytic_holds (UniversalMeasurability.lean:18) | hU | AnalyticSet.nullMeasurableSet (Prob/AnalyticUniversalMeasurable) | yes | MISSING | file imports the pin-missing module |

Cross-reference to closed_8_1_lp (MatedCRT/FirstPass/Closure/Clean81LP.lean:43): of its 11 concluder `_holds`, nine (hsmp, hmin, hU, hmeasT, hexc, hSB, hpc, hpair, hR) are in files that import a module MISSING at the pin, so closed_8_1_lp would not build against the pin once the import is switched. hμae and hLoc do not touch the mirror. Every LP name listed in the table is present in the LP worktree with an identical header.

## 3. Import replacements and blockers

Replacement for each line: `import MatedCRT.LPStaging.X` becomes `import LatticeProb.X`. The module path is the file path with `/` replaced by `.`. Mirror and LP files both use `namespace LatticeProb` (LP Prob/BrownianExit.lean:34, mirror :36). A sed of `s/^import MatedCRT\.LPStaging\./import LatticeProb./` on the 11 files below covers all 13 lines.

| # | IDLA file:line | Current import | Switch to | Target at pin 3912597 |
|---|---|---|---|---|
| 1 | FirstPass/LPBridge/LQGTestIntegralMeasurable.lean:2 | MatedCRT.LPStaging.Prob.VagueLimitMeasurable | LatticeProb.Prob.VagueLimitMeasurable | MISSING |
| 2 | FirstPass/LPBridge/ExitRestartLimit.lean:2 | MatedCRT.LPStaging.Prob.BrownianOutwardExcursion | LatticeProb.Prob.BrownianOutwardExcursion | MISSING |
| 3 | FirstPass/LPBridge/DistributionalLaplacian.lean:2 | MatedCRT.LPStaging.Analysis.DistributionalLaplacian | LatticeProb.Analysis.DistributionalLaplacian | MISSING |
| 4 | FirstPass/LPBridge/BrownianOutwardExcursion.lean:2 | MatedCRT.LPStaging.Prob.BrownianOutwardExcursion | LatticeProb.Prob.BrownianOutwardExcursion | MISSING |
| 5 | FirstPass/LPBridge/BrownianOutwardExcursion.lean:3 | MatedCRT.LPStaging.Prob.PlanarBrownianGermZeroOne | LatticeProb.Prob.PlanarBrownianGermZeroOne | MISSING |
| 6 | FirstPass/LPBridge/MinimumPrinciples.lean:4 | MatedCRT.LPStaging.Analysis.DistributionalLaplacian | LatticeProb.Analysis.DistributionalLaplacian | MISSING |
| 7 | FirstPass/LPBridge/MinimumPrinciples.lean:5 | MatedCRT.LPStaging.Analysis.SuperharmonicMinimumPrinciple | LatticeProb.Analysis.SuperharmonicMinimumPrinciple | MISSING |
| 8 | FirstPass/LPBridge/ExitRestartCanonical.lean:2 | MatedCRT.LPStaging.Prob.BrownianPathLaw | LatticeProb.Prob.BrownianPathLaw | present |
| 9 | FirstPass/LPBridge/FiniteMeasureStandardBorel.lean:2 | MatedCRT.LPStaging.Prob.FiniteMeasureStandardBorel | LatticeProb.Prob.FiniteMeasureStandardBorel | MISSING |
| 10 | FirstPass/LPBridge/PairingLawIG4.lean:2 | MatedCRT.LPStaging.Prob.CameronMartinEquivalence | LatticeProb.Prob.CameronMartinEquivalence | MISSING |
| 11 | FirstPass/LPBridge/ConeMeanZeroRestrictionFinal.lean:3 | MatedCRT.LPStaging.Gauss.GaussianProcessLawExt | LatticeProb.Gauss.GaussianProcessLawExt | MISSING |
| 12 | FirstPass/LPBridge/PunctureConnected.lean:2 | MatedCRT.LPStaging.Analysis.PuncturedPlaneConnected | LatticeProb.Analysis.PuncturedPlaneConnected | MISSING |
| 13 | FirstPass/LPBridge/UniversalMeasurability.lean:2 | MatedCRT.LPStaging.Prob.AnalyticUniversalMeasurable | LatticeProb.Prob.AnalyticUniversalMeasurable | MISSING |

Under MatedCRT/, these 13 lines are the only imports of LPStaging from outside LPStaging, all in FirstPass/LPBridge.

Blockers (named):
- **B1** Pin 3912597 lacks ten imported modules (part 3 lines 1-7, 9-13). Fix: operator bumps the lattice-probability entry in lake-manifest.json to a revision that has LatticeProb/<those modules>.
- **B2** LP 8354077 is not on a remote-tracking ref of the LP clone (origin git@github.com:nitromannitol/Lattice-Probability.git). Fix: operator pushes idla/phase2 (or another revision with the modules) before the pin moves.
- **B3** Content of the bump is unverified: 139 commits between 3912597 and 8354077. Fix: an IDLA build after the bump (operator).

Not blockers: the 4 Bonanno files and the 7 probes (no importer). The former DIFFERS files are now IDENTICAL (content sync, part 5).

## 4. Flags

- The 7 z8Probe files in MatedCRT/LPStaging/Analysis are untracked working-tree files (about 78 declarations in total). They are not imported. Any removal of the LPStaging directory would delete them, and the operator should decide that. Not deleted here.
- scratch-z11/AxAL.lean mentions LPStaging. It is outside the MatedCRT library root and was not examined further.
- The LP worktree carries an untracked LatticeProbAudit/IDLAMirrorCheck.lean. It is outside LatticeProb/ and was not read.

## 5. Content sync (p2-lpstaging-sync-content)

Rule: for each of the 20 DIFFERS files, the copy with the later last commit on its side is canonical; the other side takes its content, with only the import module paths differing. Declaration names and statements were not changed (checked before the sync: names and header text identical in all 20).

- IDLA-canonical (later commit on the IDLA side): Gauss/Brownian, Gauss/WhiteNoise, Prob/BrownianExit, Prob/BrownianGermZeroOne, Prob/BrownianMax, Prob/BrownianOpenExitFinite, Prob/BrownianOpenExitStopping, Prob/TrivialSigmaJoin.
- LP-canonical (later commit on the LP side): Gauss/BrownianCont, Gauss/Coords, Gauss/Isonormal, Gauss/Limit, Gauss/Process, Prob/BrownianContAll, Prob/BrownianMarkov, Prob/BrownianPathLaw, Prob/BrownianStrongMarkov, Prob/BrownianTail, Prob/FiniteMarginal, Prob/TrivialSigma.
- Proof-text differences (LP side takes the IDLA version, LP commit 0a02cd6): Gauss/Brownian, Gauss/WhiteNoise, Prob/BrownianGermZeroOne, Prob/BrownianMax, Prob/BrownianOpenExitFinite, Prob/BrownianOpenExitStopping. The LP version used Mathlib spellings `mem_setOf_eq`, `have`, `let`, `split_ifs`; the mirror used `mem_ofPred_eq`, `haveI`, `letI`, `dif_pos`. Both compile in the same Mathlib.
- Provenance-only differences (the "Port of LatticeProb.X (Lattice-Probability 3912597) to Mathlib v4.35.0-rc2" line, with its blank separator, removed from the IDLA copy): the 14 remaining files. Reason: the line is development metacommentary about the port, and it is self-referential inside the LP repository. The "Source: BouRabeeGwynne/..." lines are kept on both sides (provenance of the source file, identical on both sides before the sync).

Verification:
- lc strict (warnings as errors) OK on all 20 IDLA copies.
- lb OK (IDLA commit ab755b1c): the 20 modules and MatedCRT.FirstPass.LPBridge.ExitRestartCanonical.
- LP lake build OK for the six changed modules (LP commit 0a02cd6; build log /tmp/z12w/lp-build.log on the sandbox, rc 0).
- Normalized hash (import prefix rewritten to LatticeProb) equals the LP file hash for all 20 files.

| file | IDLA raw sha256 (12) | common content sha256 (12) | LP sha256 (12) |
|---|---|---|---|
| Gauss/Brownian | 9033a185defc | 449bd11d2842 | 449bd11d2842 |
| Gauss/BrownianCont | 86a41e8e439e | f81166816e53 | f81166816e53 |
| Gauss/Coords | 05ac46ef8cde | 0584372f7113 | 0584372f7113 |
| Gauss/Isonormal | 05c37094b61c | b88c6422ff9c | b88c6422ff9c |
| Gauss/Limit | b8fea98a59ce | b8fea98a59ce | b8fea98a59ce |
| Gauss/Process | 60ad5e05d493 | 07f9a1f88be8 | 07f9a1f88be8 |
| Gauss/WhiteNoise | 90a75541c24d | 57d65ea0c19f | 57d65ea0c19f |
| Prob/BrownianContAll | b8559836c377 | a32ac6cedefa | a32ac6cedefa |
| Prob/BrownianExit | ba4c925e772b | d5d173fbe5ed | d5d173fbe5ed |
| Prob/BrownianGermZeroOne | 491c880cb850 | 6ee3ee5da112 | 6ee3ee5da112 |
| Prob/BrownianMarkov | 94bacb3c2a1e | 6ec1606577a0 | 6ec1606577a0 |
| Prob/BrownianMax | ea13ba418799 | 8015d66481a5 | 8015d66481a5 |
| Prob/BrownianOpenExitFinite | bf5d2ba12019 | f4147fa40693 | f4147fa40693 |
| Prob/BrownianOpenExitStopping | adc68301fef9 | a1eb374056a8 | a1eb374056a8 |
| Prob/BrownianPathLaw | 33a1dba695d9 | e521f4f90bee | e521f4f90bee |
| Prob/BrownianStrongMarkov | 1e59995ff24c | f71d762edbe4 | f71d762edbe4 |
| Prob/BrownianTail | a55e038350b7 | a55e038350b7 | a55e038350b7 |
| Prob/FiniteMarginal | 12e4cdad96ca | 12e4cdad96ca | 12e4cdad96ca |
| Prob/TrivialSigma | 43681e5adf5b | 43681e5adf5b | 43681e5adf5b |
| Prob/TrivialSigmaJoin | c07522371523 | ca7de2069b19 | ca7de2069b19 |

Commits: IDLA ab755b1c (20 LPStaging files); LP idla/phase2 0a02cd6 (6 LatticeProb files). Counts after the sync: IDENTICAL 33, DIFFERS 0, MISSING IN LP 11. Blockers B1-B3 of part 3 are unchanged: the pin is not moved by this task.
