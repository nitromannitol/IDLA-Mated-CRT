import MatedCRT.FirstPass.Derived.InducedWalkInteriorKernel
import MatedCRT.FirstPass.Derived.InducedTrajectoryLegality
import MatedCRT.FirstPass.Derived.StoppedInterpCoupledLaws

/-!
# Stopped laws of induced and ambient walks

A coupling of the trajectory measures through the inner boundary gives equal
stopped interpolation laws for the corresponding simple random walks.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MatedCRTHarmonic.Markov
open MatedCRT.ExitCouplingGlue

namespace MatedCRT

open Classical in
/-- A common-boundary-hit coupling identifies the stopped interpolation laws. -/
theorem induced_stoppedInterp_law_eq_of_trajectory_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (P Q : Ω → ℕ → ℤ) (hP : Measurable P) (hQ : Measurable Q)
    (hPlaw : μ.map P = Kernel.trajMeasure (Measure.dirac a)
      (srwHistoryKernel (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0)))
    (hQlaw : μ.map Q = Kernel.trajMeasure (Measure.dirac a) (srwHistoryKernel m))
    (hcouple : ∀ᵐ ω ∂μ,
      hitTime (LatticeProb.Graph.innerBoundary (adjGraph m) A) (P ω) =
        hitTime (LatticeProb.Graph.innerBoundary (adjGraph m) A) (Q ω) ∧
      ∀ n : ℕ, (n : ℕ∞) ≤ hitTime (LatticeProb.Graph.innerBoundary (adjGraph m) A) (P ω) →
        P ω n = Q ω n)
    (v : ℤ → ℂ) (speed : ℝ≥0) :
    (srwLaw (fun u w => if u ∈ A ∧ w ∈ A then m u w else 0) a).map
        (stoppedInterp v speed (LatticeProb.Graph.innerBoundary (adjGraph m) A)ᶜ) =
      (srwLaw m a).map
        (stoppedInterp v speed (LatticeProb.Graph.innerBoundary (adjGraph m) A)ᶜ) := by
  have h := stoppedInterp_law_eq_of_hitTime_coupling μ P Q hP hQ
    (LatticeProb.Graph.innerBoundary (adjGraph m) A) v speed hcouple
  rw [hPlaw, hQlaw, ← srwLaw_eq_trajMeasure, ← srwLaw_eq_trajMeasure] at h
  exact h

end MatedCRT
