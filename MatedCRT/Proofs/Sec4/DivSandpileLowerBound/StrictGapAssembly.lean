import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapTransferred
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapReduction

/-! # Fixed-time obstacle inclusion from the whole-plane law -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric _root_.HarmonicBalls

universe u

/-- A harmonic-ball family has the strict obstacle inclusion before its
exit time when its measure has the same unit-disc law as a whole-plane LQG
measure with equivalent smooth pairing shifts. -/
theorem ae_harmonicBall_subset_cluster_of_wholePlane_identDistrib
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [SFinite Q]
    (μ : Ω → Measure ℂ) (ν : Ω' → Measure ℂ) (hνm : AEMeasurable ν Q)
    {ρ t γ α : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hμvol : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (μ ω) ρ βm βp)
    (hνvol : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (ν ω) ρ βm βp)
    (hident : IdentDistrib (fun ω => (μ ω).restrict (ball 0 1))
      (fun ω => (ν ω).restrict (ball 0 1)) P Q)
    {hC : Ω' → (ℂ → ℝ) → ℝ} {hcirc : Ω' → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF Q hC hcirc)
    (hν : IsLQGMeasureOfField Q γ α hcirc ν)
    (hpair : ∀ g : ℂ → ℝ, IsTestFunction univ g →
      Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          Q.map (localModConstPairings α hC univ) ∧
        Q.map (localModConstPairings α hC univ) ≪
          Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ))
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) :
    ∀ᵐ ω ∂P, t < clusterExitTime (Λ ω) ρ → Λ ω t ⊆ cluster (μ ω) ρ 0 t := by
  have hz : (0 : ℂ) ∈ ball 0 ρ := mem_ball_self hρ
  have hdefect := ae_no_regularization_defect_of_wholePlane_identDistrib h32 h611 h82
    P Q μ ν hνm hρ hρ1 ht hγ hγ2 hα hz hμvol hνvol hident hGFF hν hpair
  filter_upwards [hμvol, hΛ, hdefect] with ω hvol hfamily hdefect hT
  obtain ⟨hfinite, βm, βp, hV⟩ := hvol
  have hopen : IsOpen (cluster (μ ω) ρ 0 t) :=
    (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hfinite hρ hV hz ht).1
  exact coneFamily_subset_cluster_of_no_regularization_defect hfamily hρ ht hT hopen hdefect

end MatedCRT
