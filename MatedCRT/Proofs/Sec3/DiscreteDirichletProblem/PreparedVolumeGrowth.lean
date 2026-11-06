import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedInteriorModuli
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ContinuumModulus

/-! Lemma 3.5 with the continuum modulus supplied by volume growth. -/

namespace MatedCRT

/-- The prepared interior convergence follows from pointwise convergence, the
prepared discrete modulus, and the volume-growth estimate of Lemma 2.7. -/
theorem dirichletInteriorPreparedStep_of_volumeGrowth (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (hP : DirichletPointwiseStep 𝒮)
    (hM : DirichletDiscreteModulusPreparedStep 𝒮) : DirichletInteriorPreparedStep 𝒮 :=
  dirichletInteriorPreparedStep_of_moduli 𝒮 hP hM
    (dirichletLimitModulusStep_of_volumeGrowth 𝒮 h27)

/-- Lemma 3.5 from the prepared discrete obligations and the cited continuum
volume-growth estimate. -/
theorem discreteDirichletProblem_of_prepared_volumeGrowth (𝒮 : SpaceFillingSLEModel)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0}) (h27 : VolumeGrowthStmt)
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hlimit : DirichletLimitStep 𝒮)
    (hP : DirichletPointwiseStep 𝒮) (hM : DirichletDiscreteModulusPreparedStep 𝒮)
    (hboundary : DirichletBoundaryPreparedStep 𝒮) : DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_prepared_moduli 𝒮 hGP h36 h34 h31 h213 h219 h28 hlimit
    hP hM (dirichletLimitModulusStep_of_volumeGrowth 𝒮 h27) hboundary

end MatedCRT
