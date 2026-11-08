import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapDiscShiftLaw
import HarmonicBalls.Proofs.Sec5.InteriorClusterBoundary

/-! # Whole-plane frontier nullity and regularization -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

universe u

/-- For a whole-plane LQG measure, the interior boundary-nullity theorem
supplies the enclosing-disc input to the fixed-time regularization argument. -/
theorem ae_no_regularization_defect_wholePlane_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : AEMeasurable μ P)
    {r t γ α : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hz : z ∈ ball 0 r)
    (hvolume : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) r βm βp)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hpair : ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          P.map (localModConstPairings α hC univ) ∧
        P.map (localModConstPairings α hC univ) ≪
          P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      interior (closure (cluster (μ ω) r z t)) = cluster (μ ω) r z t := by
  have hz1 : z ∈ ball (0 : ℂ) 1 := (ball_subset_ball (le_of_lt hr1)) hz
  have hfront : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      μ ω (frontier (cluster (μ ω) 1 z s) ∩ ball 0 1) = 0 := by
    filter_upwards [ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      h32 h611 h82 γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
    intro s hs
    exact hω s hs z hz1
  exact ae_no_regularization_defect_of_enclosing_frontier_and_restricted_law
    P μ hμm hr (le_of_lt hr1) ht (ne_of_gt hγ) hz hvolume hfront
    (disc_restricted_lqg_shiftLaw_of_pairingLaws hGFF hμ hμm hr hr1 hpair)

end MatedCRT
