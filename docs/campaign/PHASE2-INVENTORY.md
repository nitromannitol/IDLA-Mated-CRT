# Phase 2 inventory: classification of the inputs of the counted IDLA theorems

Task p2-inventory-classify (worker z12, 2026-11-10). Final document of phase 2, step A.

## Sources and pins
- IDLA repository: this repository, branch main (lake-manifest.json:21-26: mathlib rev 065356127b1dc0016f66b7283ce0ce2c4055aa55).
- LP (Lattice-Probability): /home/nitro/lean/Lattice-Probability-v435, branch lean-v4.35, pin 3912597 (lakefile.lean:11-12).
- HB (Harmonic-Balls-LQG): /home/nitro/lean/Harmonic-Balls-LQG, HEAD 2019e520 (the catalog of 2026-11-10 recorded 6724661c; HEAD has moved since).
- Inputs: notes/phase2-inv-a.tsv (z11, 84 distinct inputs, DONE), notes/phase2-inv-b.tsv (z1, 51 distinct inputs), notes/phase2-lp-hb-catalog.md (z12, LP and HB catalog).
- notes/phase2-hb-rewire.tsv (z1) did not exist when this file was written. Every HB evidence entry below is PROVISIONAL (direct grep of HB) until the rewire file is checked against it.
- Verdict-note file names in the truth column carry an external-model prefix in the fleet notes; the prefix is dropped here and the stem is kept (the fleet directory has the full names).

## Scope and counts
- Union of both inventories: 91 distinct props. 20 are kind DraftStmt (results of this paper, proved and chained) and are excluded, as the task requires.
- Distinct props classified: 71. Each row lists the def file:line and the results (IDLA numbers) that use it; n = number of binder rows.
- kind is normalised: HB Stmt = defined in HB (path HB:...). The inventories label some HB props "External" (inv-a) or "Other" (inv-b); the normalised kind is used here.

## Class key
- (a) an HB result already proved in HB; evidence = HB theorem name file:line. If the HB proof is conditional on named binders, they are listed.
- (a?) candidate HB match (same content, identity or proof not yet confirmed).
- (b) general background reusable by other papers (GFF, LQG measure or metric, Cameron-Martin, Green and potential theory, random walk, Brownian motion, ergodic, measurability, point-set topology); evidence = LP, Mathlib or .lake/packages location, or "none found" plus a proposed LP module.
- (b?) borderline general background (for example a general LQG-measure fact in the literature); reason given.
- (c) paper-specific literature (a specific theorem of a specific LQG, SLE or mated-CRT paper about its own objects) that stays a cited hypothesis; evidence = the citation.
- (c?) borderline: model-specification property, paper-owned step, or cited statement with a derived or restated form; reason given. The lead decides.

## Counts per class (71 props)
- (a) 12; (a?) 10; (b) 3; (b?) 15; (c) 14; (c?) 17. Total 71.

## Table (one row per distinct non-DraftStmt input)
Columns: # | prop | def file:line | kind | used by (results; n) | source (docstring) | truth (tsv) | class | evidence.

### (a) HB results proved in HB
| # | prop | def | kind | used by | source | truth | class | evidence |
|---|---|---|---|---|---|---|---|---|
| 11 | GreenFunctionBallStmt | HB:HarmonicBalls/Draft/Section2.lean:68 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Prop 2.3 | none found (cited HB result) | a | firstPass_2_3 FirstPass/S2S3S4S9SA.lean:41 (also Probe.lean:41); binder-free |
| 20 | ClusterOpenLaplacianStmt | HB:HarmonicBalls/Draft/Section3.lean:66 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Lemma 3.2 | none found (cited HB result) | a | firstPass_3_2 FirstPass/S2S3S4S9SA.lean:66; binder-free |
| 21 | LeastSupersolutionMemStmt | HB:HarmonicBalls/Draft/Section3.lean:47 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Lemma 3.1 | none found (cited HB result) | a | firstPass_3_1 FirstPass/S2S3S4S9SA.lean:62; binder-free |
| 22 | ClusterConservationOfMassStmt | HB:HarmonicBalls/Draft/Section3.lean:102 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Lemma 3.4 | none found (cited HB result) | a | firstPass_3_4 FirstPass/S2S3S4S9SA.lean:74; binder-free |
| 23 | ClusterMonotoneStmt | HB:HarmonicBalls/Draft/Section3.lean:89 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Lemma 3.3 | none found (cited HB result) | a | firstPass_3_3 FirstPass/S2S3S4S9SA.lean:70; binder-free |
| 24 | ClusterCompatibilityStmt | HB:HarmonicBalls/Draft/Section3.lean:119 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Lemma 3.5 | none found (cited HB result) | a | firstPass_3_5 FirstPass/S2S3S4S9SA.lean:78; binder-free |
| 25 | ClusterBoundaryMeasureZeroStmt | HB:HarmonicBalls/Draft/Section5.lean:155 | HB Stmt | 4.2,2.4,2.5,2.6 (4) | HB22 Prop 5.3 | none found (cited HB result) | a | clusterBoundaryMeasureZero_of_steps Steps/Sec5/ClusterBounds.lean:39; binder h81 : BoundaryMeasureZeroOfCompactClusterStmt (HB status not checked) |
| 26 | ExistenceHarmonicBallsStmt | HB:HarmonicBalls/Draft/Section5.lean:192 | HB Stmt | 4.2,2.4,2.5,2.6 (4) | HB22 Thm 5.5 | none found (cited HB result) | a | section5_5_of_staged_inputs Proofs/Sec5/StagedInputAssembly.lean:189; binder hTyp : TypicalPointManyGoodScalesStmt (HB Lemma 8.2; open in the HB first pass) |
| 27 | ExistenceUniquenessHarmonicBallsStmt | HB:HarmonicBalls/Draft/Section1.lean:94 | HB Stmt | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB22 Thm 1.1 | none found (cited HB result) | a | firstPassMain_1_1 FirstPass/Main.lean:33; binders hDG, hCC, hE (external) and hTyp (open, 8.2) |
| 28 | UniquenessHarmonicBallsStmt | HB:HarmonicBalls/Draft/Section5.lean:206 | HB Stmt | 4.2,2.4,2.5,2.6 (4) | HB22 Prop 5.6 | none found (cited HB result) | a | section5_6_of_staged_inputs Proofs/Sec5/StagedInputAssembly.lean:146; via volumeGrowthI2_of_staged_inputs hDG hCC hE |
| 31 | HarmonicBallLocalSetStmt | HB:HarmonicBalls/Draft/Section1.lean:151 | HB Stmt | 4.2,2.4,2.5,2.6 (4) | HB22 Prop 1.3 | none found (cited HB result) | a | firstPassMain_1_3 FirstPass/Main.lean:104; binders hI2, hDG, hCC, hE, hmeasure (external), hTyp (open) |
| 32 | ClusterStrongCompatibilityStmt | HB:HarmonicBalls/Draft/Section5.lean:246 | HB Stmt | 4.2,2.4,2.5,2.6 (4) | HB22 Lemma 5.8 | none found (cited HB result) | a | section5_8_of_staged_inputs Proofs/Sec5/StagedInputAssembly.lean:153; via volumeGrowthI2_of_staged_inputs hDG hCC hE |

### (a?) candidate HB matches, to be confirmed against the rewire file
| # | prop | def | kind | used by | source | truth | class | evidence |
|---|---|---|---|---|---|---|---|---|
| 15 | FrozenGreenDiscPole | MatedCRT/FirstPass/Frozen/S2g.lean:36 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | Green function of a disc, Prop 2.3 | TRUE (idla-frozen-batch.md:11) | a? | candidate firstPass_2_3_withPole FirstPass/S2S3S4S9SA/GreenPole.lean:35 (conclusion GreenFunctionBallWithPoleStmt, def :29); binder-free beyond firstPass_2_3 |
| 19 | FrozenGreenBallCentre | MatedCRT/FirstPass/Frozen/S2g.lean:45 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | Green function of centred disc, Prop 2.3 | TRUE (idla-frozen-batch.md:12) | a? | candidate firstPass_2_3 S2S3S4S9SA.lean:41; identity of the two statements not checked |
| 51 | FrozenDiskGreenNonnegCont | MatedCRT/FirstPass/Frozen/S1c.lean:70 | Frozen | 1.4,1.6 (2) | disc Green function with pole at the centre, G_{B_R}(0,·) = greenFunction (ball 0 R) | TRUE (idla-frozen-batch.md) | a? | candidate firstPass_2_3 / _withPole; identity of greenFunction (HB Defs/Green.lean:70) not checked |
| 61 | FrozenVeryGoodAnnulusHarnackType | MatedCRT/FirstPass/Frozen/S5Cited.lean:67 | Frozen | 1.4,1.6 (2) | HB arXiv:2208.11795 Lemma 6.11 | none found (named in lead-li-requests.md) | a? | candidate firstPass_6_11 FirstPass/S6.lean:75 (conclusion VeryGoodAnnulusHarnackTypeStmt); binders hDG, hCC, hE |
| 29 | FrozenHBInitialConfinement | MatedCRT/FirstPass/Frozen/S2g.lean:61 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | HB Props 5.1-5.2 | TRUE as written (q1-frozen-truth.md:5) | a? | HB name not located |
| 64 | FrozenClusterBoundaryMeasureZero | MatedCRT/FirstPass/Frozen/S5Cited.lean:80 | Frozen | 1.4,1.6 (2) | HB Prop 5.3 | none found (named in lead-li-requests.md) | a? | duplicate of #25 (identity to confirm) |
| 65 | FrozenExistenceHarmonicBalls | MatedCRT/FirstPass/Frozen/S5Cited.lean:87 | Frozen | 1.4,1.6 (2) | HB Thm 5.5 | none found (named in lead-li-requests.md) | a? | duplicate of #26 (identity to confirm) |
| 66 | FrozenUniquenessHarmonicBalls | MatedCRT/FirstPass/Frozen/S5Cited.lean:93 | Frozen | 1.4,1.6 (2) | HB Prop 5.6 | none found (named in lead-li-requests.md) | a? | duplicate of #28 (identity to confirm) |
| 67 | FrozenHarmonicBallLocalSet | MatedCRT/FirstPass/Frozen/S5Cited.lean:100 | Frozen | 1.4,1.6 (2) | HB Prop 1.3 | none found (named in lead-li-requests.md) | a? | duplicate of #31 (identity to confirm) |
| 68 | FrozenClusterStrongCompatibility | MatedCRT/FirstPass/Frozen/S5Cited.lean:107 | Frozen | 1.4,1.6 (2) | HB Lemma 5.8 | none found (named in 213-idla-cone-hlim-hL-hM-PRO.md) | a? | duplicate of #32 (identity to confirm) |

### (b) general background
| # | prop | def | kind | used by | source | truth | class | evidence |
|---|---|---|---|---|---|---|---|---|
| 14 | FrozenSuperharmonicMinimumPrinciple | MatedCRT/FirstPass/Frozen/S2g.lean:25 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | classical minimum principle | TRUE (idla-frozen-batch.md:10) | b | continuum: no minimum-principle theorem found by grep in Mathlib or elliptic_regularity (elliptic_regularity mentions superharmonic functions in Ch4Statements/ExpansionSmall.lean, not read); discrete analogue LP Network/Dirichlet.lean:131 superharmonic_minimum_principle; proposed LatticeProb/Analysis/SuperharmonicMinimumPrinciple.lean |
| 16 | FrozenUniversalMeasurabilityOfAnalytic | MatedCRT/FirstPass/Frozen/S1c.lean:44 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | Kechris Thm 21.10 | TRUE (idla-frozen-batch.md:4) | b | Mathlib: AnalyticSet and MeasurableSet.analyticSet (.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:317); universal measurability: none found; proposed LatticeProb/Prob/AnalyticUniversalMeasurable.lean |
| 13 | FPStrongMinimumPrinciple | MatedCRT/FirstPass/Frozen/S5c.lean:48 | Frozen | 4.2,1.4,1.6 (3) | Axler-Bourdon-Ramey Thm 11.2, p. 224 | TRUE (idla-new-frozen-truth-2306.md:14) | b | continuum: no strong minimum principle found by grep in Mathlib or elliptic_regularity; LP Analysis/HeatStrongMinimum.lean:114 is the parabolic analogue; proposed LatticeProb/Analysis/StrongMinimumPrinciple.lean |

### (b?) borderline general LQG-measure or Brownian or Cameron-Martin facts
| # | prop | def | kind | used by | source | truth | class | evidence |
|---|---|---|---|---|---|---|---|---|
| 30 | LQGVolumeGrowthAllScalesStmt | HB:HarmonicBalls/Draft/Section2.lean:122 | HB Stmt | 4.2,2.4,2.5,2.6 (4) | HB22 Lemma 2.4 and scaling | none found | b? | HB input I2, used as hI2 in firstPassMain_1_2 and _1_3 (not proved in HB first pass); general LQG volume growth; none in LP; proposed LatticeProb/LQG/VolumeGrowthAllScales.lean |
| 33 | FrozenInsertionCoordinateRule | MatedCRT/FirstPass/Frozen/S2k.lean:43 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | DS11 Prop 2.1; Prop 4.2 plateau argument | TRUE (idla-frozen-batch.md:16) | b? | general LQG coordinate change (DS11 Prop 2.1); none in LP; proposed LatticeProb/LQG/CoordinateChangeInsertion.lean |
| 34 | FrozenLQGMeasureExistenceInsertion | MatedCRT/FirstPass/Frozen/S2m.lean:29 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | Gwynne HB22; DS11 | none found | b? | general LQG measure existence (HB input hE in firstPassMain); none in LP; proposed LatticeProb/LQG/MeasureExistence.lean |
| 17 | FrozenLQGTestIntegralMeasurable | MatedCRT/FirstPass/Frozen/S1c.lean:58 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | DS11 Prop 1.1 | TRUE (idla-frozen-batch.md:5) | b? | LP Gauss/Process.lean:28 measurable_isoProc (GFF level only); LQG measure: none; proposed LatticeProb/LQG/TestIntegralMeasurable.lean |
| 12 | FrozenPunctureConnected | MatedCRT/FirstPass/Frozen/S4d.lean:24 | Frozen | 4.2,1.4,1.6 (3) | none (definition: punctured connected open planar set stays connected) | TRUE (frozen-truth-S4d-S11g.md:3) | b? | Mathlib: no theorem found for connectedness of U \ {z} (grep diff_singleton in Topology/Connected: none); proposed LatticeProb/Analysis/PuncturedPlaneConnected.lean |
| 53 | FrozenBrownianOutwardExcursionAtExit | MatedCRT/FirstPass/Frozen/S3S4.lean:30 | Frozen | 1.4,1.6,3.5,3.6,3.7 (5) | regular exit of planar Brownian motion from a disk | TRUE (TRUTH-CHECK-2.md) | b? | partial: LP Prob/BrownianExitPosition.lean:34 ae_openExitTime_eq_continuousExitTime; no exact excursion statement found; proposed LatticeProb/Prob/BrownianOutwardExcursion.lean |
| 59 | FPPairingLawIG4 | MatedCRT/FirstPass/Frozen/S4S5b.lean:22 | Frozen | 1.4,1.6 (2) | mutual absolute continuity of whole-plane pairing laws under a smooth test-function shift | TRUE (TRUTH-CHECK-2.md) | b? | partial: LP Prob/CameronMartin.lean:382 abs_measureReal_shift_sub_le (total variation bound, not absolute continuity); proposed LatticeProb/Prob/CameronMartinEquivalence.lean |
| 46 | FPWholePlaneLQGExistence | MatedCRT/FirstPass/Frozen/S5S6S7.lean:17 | Frozen | 1.4,1.6 (2) | Sheffield 2007 Sec. 2; DS11 | TRUE (TRUTH-CHECK-2.md) | b? | partial: LP Bonanno/LQGMetric/Field/ExistGFF.lean:59 exists_wholePlaneGFF (GFF only); LQG measure: none; proposed LatticeProb/LQG/WholePlaneExistence.lean |
| 57 | FPWholePlaneLQGModel | MatedCRT/FirstPass/Frozen/S4S5b.lean:36 | Frozen | 1.4,1.6 (2) | whole-plane GFF with gamma-LQG measure | TRUE (TRUTH-CHECK-2.md) | b? | as #46; proposed LatticeProb/LQG/WholePlaneModel.lean |
| 47 | FPWholePlaneLQGCoordinateChange | MatedCRT/FirstPass/Frozen/S5S6S7.lean:31 | Frozen | 1.4,1.6 (2) | scale and translation invariance of the LQG measure (DS11) | TRUE (TRUTH-CHECK-2.md) | b? | general LQG coordinate change; none in LP; proposed LatticeProb/LQG/CoordinateChange.lean |
| 48 | FPWholePlaneUpperVolumeTail | MatedCRT/FirstPass/Frozen/S5S6S7.lean:38 | Frozen | 1.4,1.6 (2) | uniform upper volume bound for the LQG measure | TRUE (TRUTH-CHECK-2.md) | b? | general LQG measure fact; none in LP; proposed LatticeProb/LQG/UpperVolumeTail.lean |
| 54 | FrozenLQGMeasureFieldMeasurable | MatedCRT/FirstPass/Frozen/S4S6c.lean:44 | Frozen | 1.4,1.6 (2) | LQG measure is a measurable functional of the field | TRUE (frozen-truth-2030.md) | b? | none found in LP; proposed LatticeProb/LQG/MeasureFieldMeasurable.lean |
| 55 | FrozenFiniteMeasureDiskStandardBorel | MatedCRT/FirstPass/Frozen/S5k.lean:42 | Frozen | 1.4,1.6 (2) | finite measures on a closed disk form a standard Borel space | TRUE (z10-S5k-frozen.md) | b? | general measure theory; LP files mention StandardBorel (Prob/CondCopies.lean, Prob/ConditionalMeasure.lean) but no statement for finite measures found; proposed LatticeProb/Prob/FiniteMeasureStandardBorel.lean |
| 58 | FPLQGMeasureLocality | MatedCRT/FirstPass/Frozen/S4S5b.lean:52 | Frozen | 1.4,1.6 (2) | locality of the gamma-LQG measure | TRUE (TRUTH-CHECK-2.md) | b? | general LQG measure fact; none in LP; proposed LatticeProb/LQG/MeasureLocality.lean |
| 63 | FrozenLQGVolumeGrowthAllScales | MatedCRT/FirstPass/Frozen/S5Cited.lean:61 | Frozen | 1.4,1.6 (2) | HB arXiv:2208.11795 input I2 (Appendix A) | none found (named in lead-li-requests.md) | b? | duplicate of #30 (identity to confirm) |

### (c) paper-specific literature cited as hypotheses
| # | prop | def | kind | used by | source | truth | class | evidence |
|---|---|---|---|---|---|---|---|---|
| 1 | MepsScalingInput | MatedCRT/External/SLE.lean:63 | External | 4.1,4.2,4.6,4.7,4.8,1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (16) | BG20 eq. (1.8) | TRUE as external certificate (idla-frozen-SLERef-BG20-PRO.md:7) | c | citation BG20 (Berestycki-Gwynne) as in External/SLE.lean:63 |
| 3 | FrozenConeScalingLaw | MatedCRT/FirstPass/Frozen/S4S6c.lean:27 | Frozen | 4.1,1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (12) | DMS14 cone scaling in law | none found (named as repaired replacement: idla-4-audit.md:91) | c | citation DMS14 (Duplantier-Miller-Sheffield, mating of trees) |
| 4 | ConeEnvironmentScalingUnderSLE | MatedCRT/FirstPass/Frozen/S1d.lean:38 | Frozen | 4.2,1.4,1.6 (3) | DMS14 mating of trees, quantum cone environment | CONFLICT: TRUE as conditional implication (idla-sle-frozen-7.md:4); UNCLEAR as exact Lean statement | c | citation DMS14 |
| 8 | FrozenLBMGreenOccupationRescaled | MatedCRT/FirstPass/Frozen/S3S4b.lean:83 | Frozen | 4.2,1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (12) | BG20 Theorem 2.7(1) restated | none found (replacement of a RETIRED prop: lead-li-requests.md:130) | c | citation BG20 |
| 9 | FrozenTruncatedQuenchedLawsFixedTime | MatedCRT/FirstPass/Frozen/S3S4b.lean:102 | Frozen | 4.2,1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (10) | BG20 theorem (restated TruncatedDetFixedTimeStep) | UNRESOLVED for unrestricted model; TRUE with certified reference-law hypothesis (idla-sle-frozen-7.md:6) | c | citation BG20 |
| 10 | ConeRescaledMeasureIsConeFieldInput | MatedCRT/FirstPass/Frozen/S4d2.lean:27 | Frozen | 4.2 (1) | DMS14 Proposition | none found | c | citation DMS14 |
| 35 | FPConeWholePlaneFieldLaw | MatedCRT/FirstPass/Frozen/S4S5b.lean:43 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | DS11; DMS14 Def 4.10 | TRUE (TRUTH-CHECK-2.md:13) | c | citation DMS14 Def 4.10 |
| 36 | ConeCircleLawUniqueStep | MatedCRT/FirstPass/Frozen/S2i.lean:30 | Frozen | 4.2,1.4,1.6,2.5,2.6 (5) | DMS14 cone circle law | TRUE (idla-frozen-batch.md:13) | c | citation DMS14 |
| 37 | ConeReferenceExistsStep | MatedCRT/FirstPass/Frozen/S2i.lean:55 | Frozen | 4.2,1.4,1.6,2.5,2.6 (5) | DMS14 arXiv:1409.7055v4 | TRUE (idla-frozen-batch.md:14) | c | citation DMS14 |
| 38 | QuantumConeScalingInput | MatedCRT/External/QuantumCone.lean:19 | External | 4.2,1.4,1.6,2.3,2.5,2.6 (6) | DMS14 Prop 4.13(i), eq:quantum-cone-scaling | TRUE literature input (idla-1-4-1-6-audit.md:27) | c | citation DMS14 Prop 4.13(i) |
| 39 | BG20Prop51 | MatedCRT/FirstPass/Frozen/S3c.lean:38 | Frozen | 4.8,1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (12) | BG20 Prop 5.1, eq. (5.1) | TRUE exactly as typed (idla-frozen-SLERef-BG20-PRO.md:28) | c | citation BG20 Prop 5.1 |
| 42 | DegreeBoundInput | MatedCRT/External/SLE.lean:70 | External | 1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (11) | GMS19 Lemma 2.6 (as quoted in Lemma 7.4 proof), eq:degree-bound | none found | c | citation GMS19 Lemma 2.6 |
| 45 | FrozenBerestyckiGwynneConeBallMass | MatedCRT/FirstPass/Frozen/S5Cited.lean:35 | Frozen | 1.4,1.6 (2) | Berestycki-Gwynne, random walks on mated-CRT planar maps and Liouville Brownian motion | TRUE (idla-new-frozen-GMS331-BG56.md) | c | citation Berestycki-Gwynne |
| 62 | FrozenTypicalPointManyGoodScales | MatedCRT/FirstPass/Frozen/S5Cited.lean:73 | Frozen | 1.4,1.6 (2) | HB arXiv:2208.11795 Lemma 8.2 | none found (named in lead-li-requests.md) | c | HB Lemma 8.2 is open in the HB first pass (hTyp, FIRST-PASS-INPUTS.md:30-37); proof status in HB not checked |

### (c?) borderline: model properties, paper-owned steps, restated citations
| # | prop | def | kind | used by | source | truth | class | evidence |
|---|---|---|---|---|---|---|---|---|
| 2 | FrozenDiscreteHolderContinuityCorrected | MatedCRT/FirstPass/Frozen/S3S4.lean:22 | Frozen | 4.1,4.2,4.6,4.8,1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (15) | paper Lemma 3.2 (corrected form); GMS19 Thm 3.9 | TRUE; CONFLICT: UNRESOLVED for unrestricted model (TRUTH-CHECK-2.md:19; idla-sle-frozen-7.md:5) | c? | paper-owned lemma restated, with a GMS19 citation; discrete harmonic Hölder continuity is general but the cited form is the paper's |
| 5 | SLEScaleInvarianceInput | MatedCRT/External/SLE.lean:37 | External | 4.2,1.4,1.6 (3) | none (no locator in docstring) | none found | c? | model property of the space-filling SLE (IsSLE predicate); no citation |
| 6 | SLEReparametrizationInput | MatedCRT/External/SLE.lean:46 | External | 4.2,1.4,1.6 (3) | none (no locator in docstring) | none found | c? | as #5 (reparametrization) |
| 7 | SLEIndepMonoInput | MatedCRT/External/SLE.lean:56 | External | 4.2,1.4,1.6 (3) | none (no locator in docstring) | none found | c? | as #5 (independence and monotonicity) |
| 18 | FrozenConeLogLocalCodeLawStd | MatedCRT/FirstPass/Frozen/S2g.lean:79 | Frozen | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | DS11 Invent. Math. arXiv:0808.1560; DMS14 | TRUE (q1-frozen-truth.md:6); older label PENDING | c? | cone-specific local code law; could be (b?) |
| 40 | HasNormalizedSLELaw | MatedCRT/FirstPass/SLERef/Code.lean:53 | Other | 1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (9) | normalized law of the whole-plane space-filling SLE (a definition, not an input) | none found | c? | definition of the paper's SLE model |
| 41 | SLEModelClosureInput | MatedCRT/FirstPass/SLERef/Extended.lean:40 | Other | 1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (9) | closure clause for the model (scale invariance, reparametrization, independence) | TRUE (idla-frozen-SLERef-BG20-PRO.md) | c? | packages #5-#7 for the model |
| 43 | HasReferenceEnvironments | MatedCRT/FirstPass/SLERef/Reference.lean:42 | Other | 1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (9) | model realised by valid environments for every gamma in (0,2) | TRUE (idla-frozen-SLERef-BG20-PRO.md) | c? | model property |
| 44 | FPSimilarityTransferCorrected | MatedCRT/FirstPass/SLERef/Similarity.lean:33 | Frozen | 1.4,1.6,2.19,3.1,3.3,3.4,3.5,3.6,3.7 (9) | corrected similarity transfer for a space-filling SLE model (a proposition) | none found (named in fpsimilarity-truth.md) | c? | proposition about the paper's model; not a literature citation |
| 49 | FPConeMeanZeroRestriction | MatedCRT/FirstPass/Frozen/S5S6S7.lean:44 | Frozen | 1.4,1.6 (2) | restriction of eq:gff to mean-zero pairings on circles (input of IR-c4-5, Lemma 6.6) | TRUE (TRUTH-CHECK-2.md) | c? | paper-internal input (its own Lemma 6.6); could be (b?) |
| 50 | FrozenConeRadialDivergenceCorrected | MatedCRT/FirstPass/Frozen/S1cDivergence.lean:30 | Frozen | 1.4,1.6 (2) | radial divergence of the conditioned Brownian motion on the cone carrier | TRUE (S2m-S1cDiv.md) | c? | paper-specific cone object |
| 52 | FrozenAdjacentCellsMeetAe | MatedCRT/FirstPass/Frozen/S1S2S8SA.lean:22 | Frozen | 1.4,1.6,2.13 (3) | adjacent vertices of the map of Definition 1.1 have intersecting cells, a.s. | TRUE (TRUTH-CHECK-2.md) | c? | the paper's own map (Definition 1.1); not a literature citation |
| 56 | FrozenLeastSupersolutionMemCone | MatedCRT/FirstPass/Frozen/S5k.lean:28 | Frozen | 1.4,1.6 (2) | least-supersolution membership for the LQG measure of a mated-CRT environment | TRUE (z10-S5k-frozen.md) | c? | paper-specific cone analogue of HB Lemma 3.1 (LeastSupersolutionMemStmt, #21) |
| 60 | FrozenGreenFunctionCrudeBound | MatedCRT/FirstPass/Frozen/S5Cited.lean:48 | Frozen | 1.4,1.6 (2) | derived consequence: Lemma 2.15 of this paper, not verbatim BG20 | TRUE (idla-new-frozen-GMS331-BG56.md) | c? | paper's own lemma with a BG20 origin; derived, not a citation |
| 69 | StrictGapFixedTimeUnionStep | MatedCRT/FirstPass/S4d/StrictGapReduction.lean:36 | Other | 1.4,1.6 (2) | fixed-time union step (eq. (26) of the internal sections note) | none found (named in idla-main-1-4-1-6-PRO.md) | c? | open step about cone harmonic-ball families; not a literature citation |
| 70 | ConeCanonicalHalfBallStep | MatedCRT/FirstPass/S2g.lean:82 | Other | 1.4,1.6 (2) | OPEN NEW step: pathwise canonical stopped family (neither proved nor frozen) | TRUE (q1-open-steps.md) | c? | open step of this paper; not a literature citation |
| 71 | ConeHalfBallClosureInsideStep | MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18 | Other | 1.4,1.6 (2) | closure containment before the stopping time | none found (named in closure-inside-cycle.md) | c? | open step of this paper; not a literature citation |

## Section: (a) rewire list (provisional, to be checked against phase2-hb-rewire.tsv)
Props proved in HB, with the HB theorem and binders:
- GreenFunctionBallStmt <- firstPass_2_3 (FirstPass/S2S3S4S9SA.lean:41), no binders.
- ClusterOpenLaplacianStmt <- firstPass_3_2 (FirstPass/S2S3S4S9SA.lean:66), no binders.
- LeastSupersolutionMemStmt <- firstPass_3_1 (FirstPass/S2S3S4S9SA.lean:62), no binders.
- ClusterMonotoneStmt <- firstPass_3_3 (FirstPass/S2S3S4S9SA.lean:70), no binders.
- ClusterConservationOfMassStmt <- firstPass_3_4 (FirstPass/S2S3S4S9SA.lean:74), no binders.
- ClusterCompatibilityStmt <- firstPass_3_5 (FirstPass/S2S3S4S9SA.lean:78), no binders.
- ClusterBoundaryMeasureZeroStmt <- clusterBoundaryMeasureZero_of_steps (Steps/Sec5/ClusterBounds.lean:39), binder h81 : BoundaryMeasureZeroOfCompactClusterStmt.
- ExistenceHarmonicBallsStmt <- section5_5_of_staged_inputs (Proofs/Sec5/StagedInputAssembly.lean:189), binder hTyp : TypicalPointManyGoodScalesStmt.
- ExistenceUniquenessHarmonicBallsStmt <- firstPassMain_1_1 (FirstPass/Main.lean:33), binders hDG, hCC, hE, hTyp.
- UniquenessHarmonicBallsStmt <- section5_6_of_staged_inputs (Proofs/Sec5/StagedInputAssembly.lean:146), via hDG, hCC, hE.
- HarmonicBallLocalSetStmt <- firstPassMain_1_3 (FirstPass/Main.lean:104), binders hI2, hDG, hCC, hE, hmeasure, hTyp.
- ClusterStrongCompatibilityStmt <- section5_8_of_staged_inputs (Proofs/Sec5/StagedInputAssembly.lean:153), via hDG, hCC, hE.
- Candidates (a?): FrozenVeryGoodAnnulusHarnackType <- firstPass_6_11 (FirstPass/S6.lean:75), binders hDG, hCC, hE; FrozenGreenDiscPole <- firstPass_2_3_withPole (FirstPass/S2S3S4S9SA/GreenPole.lean:35).
- The HB inputs open in the HB first pass (FIRST-PASS-INPUTS.md:30-37): hTyp (Lemma 8.2), h7 (Prop 11.7), h13 (Prop 11.13), I2 (volume growth, external). Their FROZEN copies are classed (c) or (b?) above.

## Section: (b) in order of use count
| prop | uses (n) | truth | proposed LP module |
|---|---|---|---|
| FrozenSuperharmonicMinimumPrinciple | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | TRUE (idla-frozen-batch.md:10) | LatticeProb/Analysis/SuperharmonicMinimumPrinciple.lean |
| FrozenUniversalMeasurabilityOfAnalytic | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | TRUE (idla-frozen-batch.md:4) | LatticeProb/Prob/AnalyticUniversalMeasurable.lean |
| FPStrongMinimumPrinciple | 4.2,1.4,1.6 (3) | TRUE (idla-new-frozen-truth-2306.md:14) | LatticeProb/Analysis/StrongMinimumPrinciple.lean |

## Section: (b?) in order of use count
| prop | uses (n) | truth | proposed LP module |
|---|---|---|---|
| FrozenLQGTestIntegralMeasurable | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | TRUE (idla-frozen-batch.md:5) | LatticeProb/LQG/TestIntegralMeasurable.lean |
| FrozenInsertionCoordinateRule | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | TRUE (idla-frozen-batch.md:16) | LatticeProb/LQG/CoordinateChangeInsertion.lean |
| FrozenLQGMeasureExistenceInsertion | 4.2,1.4,1.6,2.4,2.5,2.6 (6) | none found | LatticeProb/LQG/MeasureExistence.lean |
| LQGVolumeGrowthAllScalesStmt | 4.2,2.4,2.5,2.6 (4) | none found | LatticeProb/LQG/VolumeGrowthAllScales.lean |
| FrozenBrownianOutwardExcursionAtExit | 1.4,1.6,3.5,3.6,3.7 (5) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/Prob/BrownianOutwardExcursion.lean |
| FrozenPunctureConnected | 4.2,1.4,1.6 (3) | TRUE (frozen-truth-S4d-S11g.md:3) | LatticeProb/Analysis/PuncturedPlaneConnected.lean |
| FPWholePlaneLQGExistence | 1.4,1.6 (2) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/LQG/WholePlaneExistence.lean |
| FPWholePlaneLQGModel | 1.4,1.6 (2) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/LQG/WholePlaneModel.lean |
| FPWholePlaneLQGCoordinateChange | 1.4,1.6 (2) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/LQG/CoordinateChange.lean |
| FPWholePlaneUpperVolumeTail | 1.4,1.6 (2) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/LQG/UpperVolumeTail.lean |
| FrozenLQGMeasureFieldMeasurable | 1.4,1.6 (2) | TRUE (frozen-truth-2030.md) | LatticeProb/LQG/MeasureFieldMeasurable.lean |
| FrozenFiniteMeasureDiskStandardBorel | 1.4,1.6 (2) | TRUE (z10-S5k-frozen.md) | LatticeProb/Prob/FiniteMeasureStandardBorel.lean |
| FPLQGMeasureLocality | 1.4,1.6 (2) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/LQG/MeasureLocality.lean |
| FPPairingLawIG4 | 1.4,1.6 (2) | TRUE (TRUTH-CHECK-2.md) | LatticeProb/Prob/CameronMartinEquivalence.lean |
| FrozenLQGVolumeGrowthAllScales | 1.4,1.6 (2) | none found (named in lead-li-requests.md) | duplicate of LQGVolumeGrowthAllScalesStmt |

## Open questions for the lead
1. Rewire file: (a) and (a?) rows are provisional until phase2-hb-rewire.tsv exists. Confirm: identity of each Frozen duplicate with its HB Stmt (#64-#68, #63); and that FrozenGreenDiscPole, FrozenGreenBallCentre, FrozenDiskGreenNonnegCont, FrozenHBInitialConfinement map to HB theorems.
2. Conditional HB proofs. Six of the twelve (a) rows (#25, #26, #27, #28, #31, #32) are proved in HB only from named binders (hDG, hCC, hE external; hTyp open in the first pass; h81 unverified). Decide whether these count as class (a) or stay cited; the table counts them as (a) with the binders listed.
3. Lemma 3.2 and Thm 5.5 identity: the Draft Lemma 3.2 Prop is still not located in HB Draft Section3.lean (docstring :56; def at :66 is ClusterOpenLaplacianStmt). Thm 5.5 is ExistenceHarmonicBallsStmt (Section5.lean:192), proved at StagedInputAssembly.lean:189.
4. LQG measure: LP has no LQG-measure declaration (LatticeProb/LQG/ is absent; LatticeProb/LQG.lean is an aggregator). The (b?) LQG rows need a new LP area LatticeProb/LQG/; decide whether they are background (b) or paper-specific (c).
5. Paper-owned steps: #69, #70, #71 and #52 are not literature citations; #2 and #49-#50 restate paper lemmas. Decide their class.
6. Duplicate definitions: #63 and #30 are the same HB input (I2); #64-#68 duplicate #25, #26, #28, #31, #32. Keep one row per content after the rewire check.
7. Verdicts marked PENDING or "none found" in the truth column are copied, not judged.
