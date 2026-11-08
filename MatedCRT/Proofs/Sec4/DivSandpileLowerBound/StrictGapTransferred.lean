import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapWholePlane
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapDefectLawTransfer

/-! # Transfer from the whole-plane field -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric HarmonicBalls

universe u

/-- A model with the same restricted measure law as a whole-plane LQG
measure inherits its fixed-time regularization property. -/
theorem ae_no_regularization_defect_of_wholePlane_identDistrib
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [SFinite Q]
    (μ : Ω → Measure ℂ) (ν : Ω' → Measure ℂ) (hνm : AEMeasurable ν Q)
    {r t γ α : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) (hz : z ∈ ball 0 r)
    (hμvol : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (μ ω) r βm βp)
    (hνvol : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp : ℝ, VolumeGrowth (ν ω) r βm βp)
    (hident : IdentDistrib (fun ω => (μ ω).restrict (ball 0 1))
      (fun ω => (ν ω).restrict (ball 0 1)) P Q)
    {hC : Ω' → (ℂ → ℝ) → ℝ} {hcirc : Ω' → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF Q hC hcirc)
    (hν : IsLQGMeasureOfField Q γ α hcirc ν)
    (hpair : ∀ g : ℂ → ℝ, IsTestFunction univ g →
      Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          Q.map (localModConstPairings α hC univ) ∧
        Q.map (localModConstPairings α hC univ) ≪
          Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      interior (closure (cluster (μ ω) r z t)) = cluster (μ ω) r z t := by
  have hνvol' : ∀ᵐ ω ∂Q, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (ν ω) ∧
      VolumeGrowth (ν ω) r βm βp := by
    filter_upwards [hνvol] with ω ⟨hfinite, βm, βp, hvol⟩
    exact ⟨βm, βp, hfinite, hvol⟩
  have hwhole := ae_no_regularization_defect_wholePlane_of_steps h32 h611 h82
    Q ν hνm hr hr1 ht hγ hγ2 hα hz hνvol' hGFF hν hpair
  have hident' : IdentDistrib (fun ω => (μ ω).restrict (ball 0 r))
      (fun ω => (ν ω).restrict (ball 0 r)) P Q := by
    simpa only [one_smul] using identDistrib_smul_restrict_of_enclosing
      measurableSet_ball measurableSet_ball (ball_subset_ball (le_of_lt hr1)) hident 1
  exact ae_no_regularization_defect_of_identDistrib hr ht hz hμvol hνvol hident' hwhole

end MatedCRT
