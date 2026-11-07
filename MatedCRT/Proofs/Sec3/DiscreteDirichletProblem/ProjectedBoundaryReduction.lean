import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedContinuum

/-! The prepared boundary barrier applies to projected boundary data. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Radial extension reduces the projected boundary-layer estimate to the
prepared boundary barrier for data defined on a neighbourhood of the disk.
The barrier and its numbered inputs remain explicit hypotheses. -/
theorem projectedDirichletBoundaryStep_of_prepared_boundary
    (𝒮 : SpaceFillingSLEModel) (hboundary : DirichletBoundaryPreparedStep 𝒮)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) : ProjectedDirichletBoundaryStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ F hdata δ hδ e he
  obtain ⟨hψb, hψh, hφ, hF⟩ := hdata
  have hφ' : ∃ s : ℝ, 0 < s ∧
      IsHolderContinuousOn (fun x => φ (ballRetraction z r x)) (closedBall z (r + s)) :=
    ⟨1, by norm_num, holder_ballRetraction hr (by linarith) z hφ⟩
  exact hboundary hGP h36 h34 h31 h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z hr hball ψ (fun x => φ (ballRetraction z r x)) hψb hψh hφ' F hF δ hδ e he

end MatedCRT

#print axioms MatedCRT.projectedDirichletBoundaryStep_of_prepared_boundary
