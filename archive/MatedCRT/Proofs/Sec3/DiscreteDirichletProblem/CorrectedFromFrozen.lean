import MatedCRT.Draft.Section3DirichletCorrected
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RetractionEstimate

/-! The projected Dirichlet statement follows from the frozen neighborhood-data
statement by extending the boundary data through radial retraction. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

/-- The frozen Dirichlet statement implies the projected boundary-data form
of corrected Lemma 3.5 (paper lines 1392–1402). -/
theorem discreteDirichletProblemCorrected_of_frozen (𝒮 : SpaceFillingSLEModel)
    (h : DiscreteDirichletProblemStmt 𝒮) : DiscreteDirichletProblemCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
  obtain ⟨fbar, hfbar, hconv⟩ := h γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ
    (fun x => φ (ballRetraction z r x)) hψb hψh
    ⟨1, by norm_num, holder_ballRetraction hr (by linarith) z hφ⟩ F hF
  refine ⟨fbar, ?_, hconv⟩
  filter_upwards [hfbar] with ω hω
  refine ⟨hω.1, hω.2.1, ?_, hω.2.2.2⟩
  intro x hx
  simpa only [ballRetraction_of_mem z hr (sphere_subset_closedBall hx)] using hω.2.2.1 x hx

end MatedCRT

#print axioms MatedCRT.discreteDirichletProblemCorrected_of_frozen
