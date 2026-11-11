# Internal DLA on mated-CRT maps

Lean 4 formalization of the numbered results of A. Bou-Rabee and E. Gwynne, *Internal DLA on mated-CRT maps*, arXiv:2211.04891.

Each numbered result is stated in Lean (`MatedCRT/Draft` and `MatedCRT/Steps`). Each one is either a field of the structure `MainHypotheses` (`MatedCRT/Assembly/Hypotheses.lean`) or a theorem of the main route (`MatedCRT/Assembly/Main.lean`, and the proofs it names). The two main theorems, Theorems 1.4 and 1.6, are proved from `MainHypotheses`; they are not proved without its fields. The statements follow a corrected version of the paper, included in [`paper/`](paper/).

## Main results

The table gives, for each numbered result, its Lean statement and the declaration or `MainHypotheses` field that carries it in the main route. A field of `MainHypotheses` is a hypothesis of the route, not a declaration. The statement column names the statement as its Draft or Steps file defines it; where the route uses a corrected input, the route column names that input. Paths are relative to `MatedCRT/`.

| Result | Lean statement | Declaration or hypothesis field in the main route |
|---|---|---|
| Theorem 1.4 | `ConvergenceOfIDLAStmt` (Draft/Section1.lean:45) | `convergenceOfIDLA_conditional` (Assembly/Main.lean:343) |
| Theorem 1.6 | `ConvergenceOfDivSandpileStmt` (Draft/Section1.lean:56) | `convergenceOfDivSandpile_conditional` (Assembly/Main.lean:350) |
| Fact 2.2 | `LQGMeasurePropertiesStmt` (Draft/Section2.lean:39) | hypothesis `lqgMeasureProperties` (Assembly/Hypotheses.lean:67) |
| Theorem 2.3 | `ConeHarmonicBallsStmt` (Draft/Section2.lean:56) | `coneHarmonicBalls` (Assembly/Main.lean:113) |
| Lemma 2.4 | `ConeHarmonicBallsUpToFixedTimeStmt` (Draft/Section2.lean:66) | `coneHarmonicBallsUpToFixedTime` (Assembly/Main.lean:98) |
| Lemma 2.5 | `ConeScaleInvarianceUpToFixedTimeStmt` (Draft/Section2.lean:88) | `coneScaleInvarianceUpToFixedTime` (Assembly/Main.lean:103) |
| Lemma 2.6 | `ConeScaleInvarianceStmt` (Draft/Section2.lean:108) | none in Assembly/Main.lean |
| Lemma 2.7 | `VolumeGrowthStmt` (Draft/Section2.lean:121) | hypothesis `volumeGrowth` (Assembly/Hypotheses.lean:69) |
| Lemma 2.8 | `CellSizeEstimateStmt` (Draft/Section2.lean:131) | hypothesis `cellSizeEstimate` (Assembly/Hypotheses.lean:71) |
| Lemma 2.9 | `CountingMeasureConvergenceStmt` (Draft/Section2.lean:143) | hypothesis `countingMeasureConvergence` (Assembly/Hypotheses.lean:73) |
| Lemma 2.10 | `DegreeMeasureConvergenceStmt` (Draft/Section2.lean:157) | hypothesis `degreeMeasureConvergence` (Assembly/Hypotheses.lean:75) |
| Theorem 2.11 | `RandomWalkToLBMStmt` (Draft/Section2.lean:169) | hypothesis `randomWalkToLBM` (Assembly/Hypotheses.lean:77) |
| Lemma 2.13 | `MaximumPrincipleStmt` (Draft/Section2.lean:183) | `maximumPrinciple` (Assembly/Main.lean:118) |
| Lemma 2.14 | `GreenKernelUpperBoundStmt` (Draft/Section2.lean:191) | hypothesis `greenKernelUpperBound` (Assembly/Hypotheses.lean:79) |
| Lemma 2.15 | `GreenFunctionCrudeBoundStmt` (Draft/Section2.lean:201) | hypothesis `greenFunctionCrudeBound` (Assembly/Hypotheses.lean:81) |
| Lemma 2.16 | `GreenKernelLowerBoundStmt` (Draft/Section2.lean:212) | hypothesis `greenKernelLowerBound` (Assembly/Hypotheses.lean:83) |
| Lemma 2.17 | `BoundedExitTimeRVStmt` (Draft/Section2.lean:227) | `boundedExitTimeRV` (Assembly/Main.lean:122) |
| Lemma 2.18 | `ExitTimeUpperBoundStmt` (Draft/Section2.lean:239) | hypothesis `exitTimeUpperBound` (Assembly/Hypotheses.lean:85) |
| Lemma 2.19 | `ExpectedExitTimeExplicitBoundStmt` (Draft/Section2.lean:260) | `expectedExitTimeExplicitBound` (Assembly/Main.lean:126) |
| Lemma 3.1 (corrected) | `DiscretePotentialTightnessCorrectedStmt` (Steps/Sec3/DiscretePotentialTightness.lean:102) | `discretePotentialTightnessCorrected` (Assembly/Main.lean:132) |
| Lemma 3.2 | `DiscreteHolderContinuityStmt` (Draft/Section3.lean:71) | hypothesis `discreteHolderContinuityCorrected` (Assembly/Hypotheses.lean:172) |
| Lemma 3.3 | `UniformConvergenceGreenKernelStmt` (Draft/Section3.lean:93) | `uniformConvergenceGreenKernel` (Assembly/Main.lean:150) |
| Lemma 3.4 | `IntegralConvergenceGreenFunctionStmt` (Draft/Section3.lean:109) | hypothesis `integralConvergenceGreenFunction` (Assembly/Hypotheses.lean:177) |
| Lemma 3.5 | `DiscreteDirichletProblemStmt` (Draft/Section3.lean:132) | `discreteDirichletProblem` (Assembly/Main.lean:156) |
| Lemma 3.6 | `ConvergenceHarmonicFunctionsStmt` (Draft/Section3.lean:157) | `convergenceHarmonicFunctions` (Assembly/Main.lean:144) |
| Lemma 3.7 | `ConvergenceNormalizedExitTimeStmt` (Draft/Section3.lean:173) | `convergenceNormalizedExitTime` (Assembly/Main.lean:164) |
| Theorem 4.1 | `ConvergenceDivisibleStmt` (Draft/Section4.lean:39) | `convergenceDivisible` (Assembly/Main.lean:195) |
| Proposition 4.2 | `DivSandpileLowerBoundStmt` (Draft/Section4.lean:50) | `divSandpileLowerBound` (Assembly/Main.lean:201) |
| Lemma 4.3 | `DiscreteBasicPropertiesStmt` (Draft/Section4.lean:61) | `discreteBasicProperties` (Proofs/Sec4/ObstacleSpecialization/Final.lean:28) |
| Lemma 4.4 (corrected) | `DiscreteLaplacianBoundCorrectedStmt` (Draft/Section4.lean:162) | `discreteLaplacianBoundCorrected` (Proofs/Sec4/ObstacleSpecialization/Final.lean:33) |
| Lemma 4.5 | `DiscreteConservationOfMassStmt` (Draft/Section4.lean:94) | `discreteConservationOfMassCorrected` (Proofs/Sec4/ObstacleSpecialization/Final.lean:38); not referenced in Assembly/Main.lean |
| Lemma 4.6 | `SubsequentialConvergenceStmt` (Draft/Section4.lean:110) | `subsequentialConvergence` (Assembly/Main.lean:175) |
| Lemma 4.7 | `EquiboundedStmt` (Draft/Section4.lean:127) | `equibounded` (Assembly/Main.lean:171) |
| Lemma 4.8 | `SubsequentialPropertiesStmt` (Draft/Section4.lean:145) | `subsequentialProperties` (Assembly/Main.lean:182) |
| Proposition 5.1 | `IDLALowerBoundStmt` (Draft/Section5.lean:27) | `iDLALowerBound` (Assembly/Main.lean:253) |
| Lemma 5.2 | `GeneralIDLALowerBoundStmt` (Draft/Section5.lean:47) | none in Assembly/Main.lean |
| Lemma 5.3 | `MeanValueInequalityStmt` (Draft/Section5.lean:67) | `meanValueInequality` (Assembly/Main.lean:214) |
| Lemma 5.4 | `LLowerBoundStmt` (Draft/Section5.lean:85) | `lLowerBound` (Assembly/Main.lean:224) |
| Proposition 6.1 | `IDLAUpperBoundStmt` (Draft/Section6.lean:31) | `iDLAUpperBound` (Assembly/Main.lean:305) |
| Lemma 6.3 | `AbelianIDLAStmt` (Draft/Section6.lean:46) | none in Assembly/Main.lean |
| Lemma 6.4 | `GoodAnnulusPrevalenceStmt` (Draft/Section6.lean:60) | `goodAnnulusPrevalence` (Assembly/Main.lean:269) |
| Lemma 6.5 | `AnnulusHitStmt` (Draft/Section6.lean:72) | `annulusHit` (Assembly/Main.lean:264) |
| Lemma 6.6 | `AnnulusIterateStmt` (Draft/Section6.lean:88) | `annulusIterate` (Proofs/Field/LawTransferComplete.lean:71) |
| Lemma 6.7 | `ConstantOrderLowerBoundLogStmt` (Steps/Sec6/ConstantOrderLowerBound.lean:34) | `constantOrderLowerBoundLog` (Assembly/Main.lean:280) |
| Lemma 6.8 | `ConstantOrderLowerBoundDivLogStmt` (Steps/Sec6/ConstantOrderLowerBoundDiv.lean:32) | `constantOrderLowerBoundDivLog` (Assembly/Main.lean:274) |
| Lemma 6.9 | `ChanceOfBeingAbsorbedLogLossStmt` (Steps/Sec6/IterativeBound.lean:73) | `chanceOfBeingAbsorbedLogLoss` (Assembly/Main.lean:289) |
| Lemma 6.10 | `IterativeBoundStmt` (Draft/Section6.lean:162) | `iterativeBound` (Assembly/Main.lean:295) |
| Proposition 7.1 | `DivSandpileUpperBoundStmt` (Draft/Section7.lean:22) | `divSandpileUpperBound` (Assembly/Main.lean:327) |
| Lemma 7.2 | `MassBoundOdometerAboveScaleStmt` (Draft/Section7.lean:77) | `massBoundOdometerAboveScale` (Assembly/Main.lean:313) |
| Lemma 7.3 | `OdometerBoundMassStmt` (Draft/Section7.lean:46) | `odometerBoundMass` (Assembly/Main.lean:318) |
| Lemma 7.4 | `CrudeUpperBoundStmt` (Draft/Section7.lean:67) | `crudeUpperBound` (Assembly/Main.lean:322) |
| Proposition 8.1 | `IDLAConstrainedConvergenceStmt` (Draft/Section8.lean:20) | `iDLAConstrainedConvergence` (Assembly/Main.lean:335) |
| Lemma A.1 | `DiscreteDivergenceTheoremStmt` (Draft/SectionA.lean:25) | `discreteDivergenceTheorem` (Proofs/SecA/DiscreteDivergence.lean:54) |
| Lemma A.2 | `DiscreteBasicPropertiesGeneralStmt` (Draft/SectionA.lean:32) | `discreteBasicPropertiesGeneral` (Proofs/SecA/Statements.lean:62) |
| Lemma A.3 | `DiscreteLaplacianBoundGeneralStmt` (Draft/SectionA.lean:43) | `discreteLaplacianBoundGeneral` (Proofs/SecA/Statements.lean:66) |
| Lemma A.4 | `DiscreteConservationOfMassGeneralStmt` (Draft/SectionA.lean:54) | `discreteConservationOfMassGeneral` (Proofs/SecA/Statements.lean:71) |

## Verification

`lake build` checks every module. `MatedCRT/Audit/Main.lean` contains `#print axioms` commands for `convergenceOfIDLA_conditional`, `convergenceOfDivSandpile_conditional` and `discretePotentialTightnessAe`; running `lake build MatedCRT.Audit.Main` prints them. The axioms should be `propext`, `Classical.choice` and `Quot.sound`. The same file asserts that each numbered result on the main line is routed through its reduction (`assert_uses`), and that no field of `MainHypotheses` is a statement refuted in Lean (`assert_no_refuted_field`).

## Size

From the repository root:

```text
git ls-files -- '*.lean' | wc -l                      # tracked Lean files
git ls-files -z -- '*.lean' | xargs -0 wc -l | tail -1   # their lines
```

At this commit these give 2153 files and 281,012 lines.

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
MatedCRT/Assembly/         MainHypotheses and the main theorems
MatedCRT/Audit/            Axiom reports, routing checks, refuted statements
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
