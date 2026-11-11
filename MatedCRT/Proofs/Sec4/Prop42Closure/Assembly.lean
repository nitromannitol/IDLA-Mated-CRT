import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final

/-! # Proposition 4.2, assembled (written argument, draft lines 306-410)

The two forms of Proposition 4.2 in the names used by the consumers (Proposition 5.1 and `Assembly/Main.lean`):

* `divSandpileLowerBound_prop42`: `DivSandpileLowerBoundStmt` (`Draft/Section4.lean`, the printed Proposition 4.2);
* `discreteClusterInnerBound_prop42`: `DiscreteClusterInnerBoundStep` (the `Λ^ε_t` form used by Proposition 5.1).

Their proofs are those of `Final.lean`. The only hypothesis specific to Proposition 4.2 is `HarmonicBallStrictObstacleGapStep`
(`Final.lean:32`, the fixed-time strict obstacle gap of draft lines 18-228). The other hypotheses
are numbered results of the paper, Theorem 4.1 (`ConvergenceDivisibleStmt`), Theorem 2.3 (`ConeHarmonicBallsStmt`), Lemma 2.4
(`ConeHarmonicBallsUpToFixedTimeStmt`), Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.8 (`CellSizeEstimateStmt`), Lemma 3.3
(`UniformConvergenceGreenKernelStmt`), and the Section 2 measurability step `ConeFamilyAEMeasurableStep`. The closure step
`ConeHalfBallClosureInsideStep` is not among them: no declaration of the chain refers to it. -/

namespace MatedCRT

/-- **Proposition 4.2** (`DivSandpileLowerBoundStmt`, `Draft/Section4.lean:50`), from the fixed-time strict obstacle gap
`HarmonicBallStrictObstacleGapStep` and the numbered results listed in the module docstring. -/
theorem divSandpileLowerBound_prop42 (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) (hgap : HarmonicBallStrictObstacleGapStep 𝒮) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_final 𝒮 h41 h23 h24 h27 h28 h33 hfam hgap

/-- **Proposition 4.2, `Λ^ε_t` form** (`DiscreteClusterInnerBoundStep`, used by Proposition 5.1), with the same hypotheses
as `divSandpileLowerBound_prop42`. -/
theorem discreteClusterInnerBound_prop42 (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) (hgap : HarmonicBallStrictObstacleGapStep 𝒮) :
    DiscreteClusterInnerBoundStep 𝒮 :=
  discreteClusterInnerBound_final 𝒮 h41 h23 h24 h27 h28 h33 hfam hgap

end MatedCRT
