# Internal DLA on mated-CRT maps

Lean 4 formalization of the numbered results of A. Bou-Rabee and E. Gwynne, *Internal DLA on mated-CRT maps*, arXiv:2211.04891.

Each numbered result is stated in Lean (`MatedCRT/Draft` and `MatedCRT/Steps`). The statements follow a corrected version of the paper, included in [`paper/`](paper/).

The two main theorems, Theorems 1.4 and 1.6, are proved at the canonical space-filling SLE model `ProbeMi.canonicalSLEModel ν` (the curve modulo increasing reparametrization) from three premises, the fields of `CanonicalHypotheses ν` (`MatedCRT/Assembly/Canonical.lean`: `convergenceOfIDLA_canonical`, `convergenceOfDivSandpile_canonical`):

* a mating-of-trees coupling for every `0 < γ < 2` whose Lebesgue-parametrized curve has code law `ν (16 / γ²)` (Duplantier–Miller–Sheffield, arXiv:1409.7055, Theorem 1.9; the record `IsMatingOfTreesCoupling` of Lattice-Probability);
* the comparison of the stopped curves of the walk and of the space-filling SLE from every selected start, in Lévy–Prokhorov distance (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1);
* the chart forms of Berestycki–Gwynne, arXiv:2003.10320, Lemmas 7.20 (the coordinate change of Liouville Brownian motion, Berestycki, arXiv:1301.3356, Theorem 1.3) and 7.21 (`BG20ChartFieldInput`).

Every other input of this route is proved in this repository, in Harmonic-Balls-LQG or in Lattice-Probability; docs/campaign/COUNTED.md records the chain. For an arbitrary space-filling SLE model `𝒮`, Theorems 1.4 and 1.6 are also proved from the 42 fields of the structure `MainHypotheses 𝒮` (`MatedCRT/Assembly/Hypotheses.lean`, `MatedCRT/Assembly/Main.lean`: `convergenceOfIDLA_conditional`, `convergenceOfDivSandpile_conditional`); each numbered result is either a field of that structure or a theorem of that route.

## Main results

The table gives, for each numbered result, its Lean statement and the declaration or `MainHypotheses` field that carries it in the main route. A field of `MainHypotheses` is a hypothesis of the route, not a declaration. The statement column names the statement as its Draft or Steps file defines it; where the route uses a corrected input, the route column names that input. Paths are relative to `MatedCRT/`. The First-pass closure column gives, for each numbered result, the declaration that closes it with every literature input as an explicit hypothesis; the full binder classes are in docs/campaign/COUNTED.md.

| Result | Lean statement | Declaration or hypothesis field in the main route | First-pass closure |
|---|---|---|---|
| Theorem 1.4 | `ConvergenceOfIDLAStmt` (Draft/Section1.lean:44) | `convergenceOfIDLA_conditional` (Assembly/Main.lean:354); at the canonical model from `CanonicalHypotheses`, `convergenceOfIDLA_canonical` (Assembly/Canonical.lean:64) | `closed_1_4_lp_noSC_noSup` (FirstPass/Closure/LssDerived.lean:54; applies `closed_1_4_lp_noSC`, Clean14And16LPNoSC.lean:24); at the canonical model `closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField` (FirstPass/Derived/CanonicalCountedFormsOfCouplingClock.lean:54) |
| Theorem 1.6 | `ConvergenceOfDivSandpileStmt` (Draft/Section1.lean:55) | `convergenceOfDivSandpile_conditional` (Assembly/Main.lean:361); at the canonical model from `CanonicalHypotheses`, `convergenceOfDivSandpile_canonical` (Assembly/Canonical.lean:71) | `closed_1_6_lp_noSC_noSup` (FirstPass/Closure/LssDerived.lean:95; applies `closed_1_6_lp_noSC`, Clean14And16LPNoSC.lean:73); at the canonical model `closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField` (FirstPass/Derived/CanonicalCountedFormsOfCouplingClock.lean:79) |
| Fact 2.2 | `LQGMeasurePropertiesStmt` (Draft/Section2.lean:39) | hypothesis `lqgMeasureProperties` (Assembly/Hypotheses.lean:65) | not counted (cited result) |
| Theorem 2.3 | `ConeHarmonicBallsStmt` (Draft/Section2.lean:56) | `coneHarmonicBalls` (Assembly/Main.lean:124) | `closed_2_3_lp` (FirstPass/Closure/Clean2xLP.lean:37) |
| Lemma 2.4 | `ConeHarmonicBallsUpToFixedTimeStmt` (Draft/Section2.lean:66) | `coneHarmonicBallsUpToFixedTime` (Assembly/Main.lean:109) | `closed_2_4_lp` (FirstPass/Closure/Clean2xLP.lean:77) |
| Lemma 2.5 | `ConeScaleInvarianceUpToFixedTimeStmt` (Draft/Section2.lean:88) | `coneScaleInvarianceUpToFixedTime` (Assembly/Main.lean:114) | `closed_2_5_lp` (FirstPass/Closure/Clean2xLP.lean:99) |
| Lemma 2.6 | `ConeScaleInvarianceStmt` (Draft/Section2.lean:108) | none in Assembly/Main.lean | `closed_2_6_lp` (FirstPass/Closure/Clean2xLP.lean:122) |
| Lemma 2.7 | `VolumeGrowthStmt` (Draft/Section2.lean:121) | hypothesis `volumeGrowth` (Assembly/Hypotheses.lean:67) | not counted (cited result) |
| Lemma 2.8 | `CellSizeEstimateStmt` (Draft/Section2.lean:131) | hypothesis `cellSizeEstimate` (Assembly/Hypotheses.lean:69) | not counted (cited result) |
| Lemma 2.9 | `CountingMeasureConvergenceStmt` (Draft/Section2.lean:143) | hypothesis `countingMeasureConvergence` (Assembly/Hypotheses.lean:71) | not counted (cited result) |
| Lemma 2.10 | `DegreeMeasureConvergenceStmt` (Draft/Section2.lean:157) | hypothesis `degreeMeasureConvergence` (Assembly/Hypotheses.lean:73) | not counted (cited result) |
| Theorem 2.11 | `RandomWalkToLBMStmt` (Draft/Section2.lean:169) | hypothesis `randomWalkToLBM` (Assembly/Hypotheses.lean:75) | not counted (cited result) |
| Lemma 2.13 | `MaximumPrincipleStmt` (Draft/Section2.lean:183) | `maximumPrinciple` (Assembly/Main.lean:129) | `closed_2_13_cellRewire` (FirstPass/Closure/CellRewire.lean:21) |
| Lemma 2.14 | `GreenKernelUpperBoundStmt` (Draft/Section2.lean:191) | hypothesis `greenKernelUpperBound` (Assembly/Hypotheses.lean:77) | not counted (cited result) |
| Lemma 2.15 | `GreenFunctionCrudeBoundStmt` (Draft/Section2.lean:201) | hypothesis `greenFunctionCrudeBound` (Assembly/Hypotheses.lean:79) | not counted (cited result) |
| Lemma 2.16 | `GreenKernelLowerBoundStmt` (Draft/Section2.lean:212) | hypothesis `greenKernelLowerBound` (Assembly/Hypotheses.lean:81) | not counted (cited result) |
| Lemma 2.17 | `BoundedExitTimeRVStmt` (Draft/Section2.lean:227) | `boundedExitTimeRV` (Assembly/Main.lean:133) | `firstPass_2_17_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean:85) |
| Lemma 2.18 | `ExitTimeUpperBoundStmt` (Draft/Section2.lean:239) | hypothesis `exitTimeUpperBound` (Assembly/Hypotheses.lean:83) | not counted (cited result) |
| Lemma 2.19 | `ExpectedExitTimeExplicitBoundStmt` (Draft/Section2.lean:260) | `expectedExitTimeExplicitBound` (Assembly/Main.lean:137) | `closed_2_19_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean:39) |
| Lemma 3.1 (corrected) | `DiscretePotentialTightnessCorrectedStmt` (Steps/Sec3/DiscretePotentialTightness.lean:102) | `discretePotentialTightnessCorrected` (Assembly/Main.lean:143) | `firstPass_3_1_faithful` (FirstPass/S3c.lean:125); open DRAFT binders: h27, h218 |
| Lemma 3.2 | `DiscreteHolderContinuityStmt` (Draft/Section3.lean:71) | hypothesis `discreteHolderContinuityCorrected` (Assembly/Hypotheses.lean:165) | not counted (cited result) |
| Lemma 3.3 | `UniformConvergenceGreenKernelStmt` (Draft/Section3.lean:93) | `uniformConvergenceGreenKernel` (Assembly/Main.lean:161) | `closed_3_3_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean:45) |
| Lemma 3.4 | `IntegralConvergenceGreenFunctionStmt` (Draft/Section3.lean:109) | hypothesis `integralConvergenceGreenFunction` (Assembly/Hypotheses.lean:169) | `closed_3_4_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean:51) |
| Lemma 3.5 | `DiscreteDirichletProblemStmt` (Draft/Section3.lean:132) | `discreteDirichletProblem` (Assembly/Main.lean:167) | `closed_3_5_lp` (FirstPass/Closure/CleanSec23LP.lean:45) |
| Lemma 3.6 | `ConvergenceHarmonicFunctionsStmt` (Draft/Section3.lean:157) | `convergenceHarmonicFunctions` (Assembly/Main.lean:155) | `closed_3_6_lp_uniform` (FirstPass/Closure/CleanSec23LPUniform.lean:30); conditional on `FrozenOneSidedBoundaryContinuityFlooredUniform` (FirstPass/S3i/LensFloored.lean:68) |
| Lemma 3.7 | `ConvergenceNormalizedExitTimeStmt` (Draft/Section3.lean:173) | `convergenceNormalizedExitTime` (Assembly/Main.lean:175) | `closed_3_7_lp` (FirstPass/Closure/CleanSec23LP.lean:61) |
| Theorem 4.1 | `ConvergenceDivisibleStmt` (Draft/Section4.lean:38) | `convergenceDivisible` (Assembly/Main.lean:206) | `closed_4_1_lp` (FirstPass/Closure/CleanSec456LP.lean:30) |
| Proposition 4.2 | `DivSandpileLowerBoundStmt` (Draft/Section4.lean:49) | `divSandpileLowerBound` (Assembly/Main.lean:212) | `closed_4_2_lp` (FirstPass/Closure/Clean42And5LP.lean:47) |
| Lemma 4.3 | `DiscreteBasicPropertiesStmt` (Draft/Section4.lean:60) | `discreteBasicProperties` (Proofs/Sec4/ObstacleSpecialization/Final.lean:28) | `closed_4_3` (FirstPass/Closure/Section4.lean:18) |
| Lemma 4.4 (corrected) | `DiscreteLaplacianBoundCorrectedStmt` (Draft/Section4.lean:161) | `discreteLaplacianBoundCorrected` (Proofs/Sec4/ObstacleSpecialization/Final.lean:33) | `closed_4_4` (FirstPass/Closure/Section4.lean:22) |
| Lemma 4.5 | `DiscreteConservationOfMassStmt` (Draft/Section4.lean:93) | `discreteConservationOfMassCorrected` (Proofs/Sec4/ObstacleSpecialization/Final.lean:38); not referenced in Assembly/Main.lean | `closed_4_5` (FirstPass/Closure/Section4.lean:27) |
| Lemma 4.6 | `SubsequentialConvergenceStmt` (Draft/Section4.lean:109) | `subsequentialConvergence` (Assembly/Main.lean:186) | `firstPass_4_6_h35c` (FirstPass/Closure/H35CorrectedRewire.lean:74); open DRAFT binders: h27, h218, h28, h35c, h37 |
| Lemma 4.7 | `EquiboundedStmt` (Draft/Section4.lean:126) | `equibounded` (Assembly/Main.lean:170) | `closed_4_7_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean:65) |
| Lemma 4.8 | `SubsequentialPropertiesStmt` (Draft/Section4.lean:144) | `subsequentialProperties` (Assembly/Main.lean:193) | `closed_4_8_lp` (FirstPass/Closure/CleanSec456LP.lean:38) |
| Proposition 5.1 | `IDLALowerBoundStmt` (Draft/Section5.lean:27) | `iDLALowerBound` (Assembly/Main.lean:264) | `closed_5_1_lp_noSup` (FirstPass/Closure/LssDerived.lean:353; applies `closed_5_1_lp`, Clean42And5LP.lean:79) |
| Lemma 5.2 | `GeneralIDLALowerBoundStmt` (Draft/Section5.lean:47) | none in Assembly/Main.lean | `closed_5_2_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean:79) |
| Lemma 5.3 | `MeanValueInequalityStmt` (Draft/Section5.lean:67) | `meanValueInequality` (Assembly/Main.lean:225) | `closed_5_3_clean` (FirstPass/Closure/HLsRewire53.lean:109) |
| Lemma 5.4 | `LLowerBoundStmt` (Draft/Section5.lean:85) | `lLowerBound` (Assembly/Main.lean:235) | `closed_5_4_clean` (FirstPass/Closure/Clean51And54.lean:73) |
| Proposition 6.1 | `IDLAUpperBoundStmt` (Draft/Section6.lean:31) | `iDLAUpperBound` (Assembly/Main.lean:316) | `closed_6_1_lp_noSup` (FirstPass/Closure/LssDerived.lean:257; applies `closed_6_1_lp`, Clean61And71LP.lean:43) |
| Lemma 6.3 | `AbelianIDLAStmt` (Draft/Section6.lean:46) | none in Assembly/Main.lean | not counted (cited result) |
| Lemma 6.4 | `GoodAnnulusPrevalenceStmt` (Draft/Section6.lean:60) | `goodAnnulusPrevalence` (Assembly/Main.lean:280) | `closed_6_4_lp` (FirstPass/Closure/CleanSec456LP.lean:45) |
| Lemma 6.5 | `AnnulusHitStmt` (Draft/Section6.lean:72) | `annulusHit` (Assembly/Main.lean:275) | `firstPass_6_5_uniform` (FirstPass/S6q.lean:26) |
| Lemma 6.6 | `AnnulusIterateStmt` (Draft/Section6.lean:88) | `annulusIterate` (Proofs/Field/LawTransferComplete.lean:71) | not counted (cited result) |
| Lemma 6.7 | `ConstantOrderLowerBoundLogStmt` (Steps/Sec6/ConstantOrderLowerBound.lean:33) | `constantOrderLowerBoundLog` (Assembly/Main.lean:291) | `firstPass_6_7` (FirstPass/LIClosed68Y.lean:30); binders to examine: hLit, hBM, hCC, hμ |
| Lemma 6.8 | `ConstantOrderLowerBoundDivLogStmt` (Steps/Sec6/ConstantOrderLowerBoundDiv.lean:32) | `constantOrderLowerBoundDivLog` (Assembly/Main.lean:285) | `firstPass_6_8` (FirstPass/LIClosed68Y.lean:40); binders to examine: hLit, hBM, hCC, hμ |
| Lemma 6.9 | `ChanceOfBeingAbsorbedLogLossStmt` (Steps/Sec6/IterativeBound.lean:73) | `chanceOfBeingAbsorbedLogLoss` (Assembly/Main.lean:300) | `firstPass_6_9` (FirstPass/LIClosed68Y.lean:51); binders to examine: hLit, hBM, hCC, hμ |
| Lemma 6.10 | `IterativeBoundStmt` (Draft/Section6.lean:162) | `iterativeBound` (Assembly/Main.lean:306) | `closed_6_10_lp` (FirstPass/Closure/CleanSec456LP.lean:52) |
| Proposition 7.1 | `DivSandpileUpperBoundStmt` (Draft/Section7.lean:22) | `divSandpileUpperBound` (Assembly/Main.lean:338) | `closed_7_1_lp` (FirstPass/Closure/Clean61And71LP.lean:84) |
| Lemma 7.2 | `MassBoundOdometerAboveScaleStmt` (Draft/Section7.lean:77) | `massBoundOdometerAboveScale` (Assembly/Main.lean:324) | `closed_7_2` (FirstPass/Closure/Section7.lean:18) |
| Lemma 7.3 | `OdometerBoundMassStmt` (Draft/Section7.lean:46) | `odometerBoundMass` (Assembly/Main.lean:329) | `closed_7_3` (FirstPass/Closure/Section7.lean:23) |
| Lemma 7.4 | `CrudeUpperBoundStmt` (Draft/Section7.lean:67) | `crudeUpperBound` (Assembly/Main.lean:333) | not counted (cited result) |
| Proposition 8.1 | `IDLAConstrainedConvergenceStmt` (Draft/Section8.lean:20) | `iDLAConstrainedConvergence` (Assembly/Main.lean:346) | `closed_8_1_lp_noSup` (FirstPass/Closure/LssDerived.lean:295; applies `closed_8_1_lp`, Clean81LP.lean:43); open DRAFT binders: h210, h34, h214, h28, h35c, h218, h23, h33, h27 (MQ-li-4 switch) |
| Lemma A.1 | `DiscreteDivergenceTheoremStmt` (Draft/SectionA.lean:25) | `discreteDivergenceTheorem` (Proofs/SecA/DiscreteDivergence.lean:54) | `discreteDivergenceTheorem` (Proofs/SecA/DiscreteDivergence.lean:54) |
| Lemma A.2 | `DiscreteBasicPropertiesGeneralStmt` (Draft/SectionA.lean:32) | `discreteBasicPropertiesGeneral` (Proofs/SecA/Statements.lean:62) | `discreteBasicPropertiesGeneral` (Proofs/SecA/Statements.lean:62) |
| Lemma A.3 | `DiscreteLaplacianBoundGeneralStmt` (Draft/SectionA.lean:43) | `discreteLaplacianBoundGeneral` (Proofs/SecA/Statements.lean:66) | `discreteLaplacianBoundGeneral` (Proofs/SecA/Statements.lean:66) |
| Lemma A.4 | `DiscreteConservationOfMassGeneralStmt` (Draft/SectionA.lean:54) | `discreteConservationOfMassGeneral` (Proofs/SecA/Statements.lean:71) | `discreteConservationOfMassGeneral` (Proofs/SecA/Statements.lean:71) |

## Verification

`lake build` checks every module. The modules of `MatedCRT/Audit/` print the axioms of the main declarations: `CanonicalAxioms.lean` those of `convergenceOfIDLA_canonical` and `convergenceOfDivSandpile_canonical`, `CountedAxioms.lean`, `DerivedCountedAxioms.lean` and `MinimalCountedAxioms.lean` those of the counted forms of docs/campaign/COUNTED.md, `AppendixBAxioms.lean` those of Appendix B. Running `lake build MatedCRT.Audit.CanonicalAxioms` (and likewise for the others) prints them; the axioms should be `propext`, `Classical.choice` and `Quot.sound`. `Refutations.lean` and `CorrectedForms.lean` record in Lean how the Draft Lemmas 3.1, 4.4 and 4.5 relate to the corrected forms that the route uses (docs/campaign/CORRECTIONS.md).

## Size

From the repository root:

```text
git ls-files -- '*.lean' | wc -l                      # tracked Lean files
git ls-files -z -- '*.lean' | xargs -0 wc -l | tail -1   # their lines
```

At commit b092d4f8 these give 2270 files and 309,012 lines.

## Building

1. Install the Lean toolchain named in `lean-toolchain` (`leanprover/lean4:v4.35.0-rc2`) with `elan`.
2. Place a clone of Harmonic-Balls-LQG next to this repository, in `../Harmonic-Balls-LQG`: `lakefile.lean` requires it from that path. Lattice-Probability is fetched from GitHub at the commit given in `lakefile.lean`. Mathlib is pinned in `lake-manifest.json`.
3. Run `lake exe cache get` to download the Mathlib build cache, then `lake build`.

## Repository layout

```text
MatedCRT.lean              Root module
MatedCRT/Basic.lean        Module header
MatedCRT/Defs/             Setting, map, Gaussian free field, LQG measure, random walks, sandpiles
MatedCRT/External/         Literature inputs as Prop-valued definitions
MatedCRT/Proposed/         Cited and proposed external statements, one module per reference
MatedCRT/Draft/            Statements of the numbered results
MatedCRT/Steps/            Reduction of each result to its inputs, by section
MatedCRT/Proofs/           Proofs of the lemmas used by the reductions, by section
MatedCRT/FirstPass/        Earlier proofs; Frozen/ holds input statements, Closure/ closed results
MatedCRT/Assembly/         CanonicalHypotheses, MainHypotheses and the main theorems
MatedCRT/Audit/            Axiom reports and refuted statements
MatedCRT/LPStaging/        General lemmas staged for Lattice-Probability
docs/                      Inventories, corrections and audits of the formalization
paper/                     Corrected paper, arXiv source, figures
```

## How this was built

The development used AI-assisted proof writing under human direction.

## Authors and citation

The Lean formalization is by Ahmed Bou-Rabee. The mathematics is due to the authors of the paper, A. Bou-Rabee and E. Gwynne.

Cite the paper: A. Bou-Rabee and E. Gwynne, *Internal DLA on mated-CRT maps*, arXiv:2211.04891.

## License

Copyright 2026 Ahmed Bou-Rabee. Licensed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

## Acknowledgements

The mated-CRT map, its random walk, Green function and harmonic-extension definitions, and several cited results are taken from
Leonardo Bonanno's [`lean-formalizations`](https://github.com/leobon12/lean-formalizations) (formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps*, and related papers), through the copies in the `lean-v4.35` line of
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb/Bonanno/`), which name their source modules.
The harmonic-balls definitions come from [Harmonic-Balls-LQG](https://github.com/nitromannitol/Harmonic-Balls-LQG).
