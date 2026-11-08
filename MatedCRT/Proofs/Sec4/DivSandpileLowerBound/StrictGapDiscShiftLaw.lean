import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapShiftLawFromPairings
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapPinnedCutoff
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRestrictedLawTransfer

/-! # Mass shifts on an interior disc -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- Smooth pairing-shift equivalence entails equivalence of the laws of the
LQG measure restricted to an interior disc and its exponential mass shifts. -/
theorem disc_restricted_lqg_shiftLaw_of_pairingLaws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α γ r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμm : AEMeasurable μ P)
    (hr : 0 < r) (hr1 : r < 1)
    (hpair : ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          P.map (localModConstPairings α hC univ) ∧
        P.map (localModConstPairings α hC univ) ≪
          P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)) :
    ∀ c : ℝ,
      P.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) • (μ ω).restrict (ball 0 r)) ≪
        P.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 r)) := by
  intro c
  obtain ⟨g, hg, hpin, hgc⟩ := exists_pinned_smooth_shift hr hr1 c
  have hbuffer : ∀ n z, z ∈ ball (0 : ℂ) r →
      closedBall z (dyadicScale n) ⊆ ball 0 (r + 2) := by
    intro n z hz w hw
    have hn : dyadicScale n ≤ 1 := by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hdist : dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
    simp only [mem_closedBall] at hw
    simp only [mem_ball] at hz ⊢
    linarith
  have h := restricted_lqg_shiftLaw_of_pairingLaw hGFF hμ hμm (ball 0 r)
    isOpen_ball hbuffer g hg.1.continuous hpin hgc (hpair g hg)
  simpa using h.2

/-- The fixed-time regularization has no defect when the enclosing disc law
agrees with a whole-plane LQG measure whose smooth pairing shifts are equivalent. -/
theorem ae_no_regularization_defect_of_wholePlane_pairingLaws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [SFinite P] (Q : Measure Ω')
    (μ : Ω → Measure ℂ) (ν : Ω' → Measure ℂ) (hμm : AEMeasurable μ P)
    {r R t γ α : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (hrR : r ≤ R) (ht : 0 < t)
    (hγ : γ ≠ 0) (hz : z ∈ ball 0 r)
    (hvolume : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) r βm βp)
    (hfront : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      μ ω (frontier (cluster (μ ω) R z s) ∩ ball 0 R) = 0)
    (hident : IdentDistrib (fun ω => (μ ω).restrict (ball 0 R))
      (fun ω => (ν ω).restrict (ball 0 R)) P Q)
    {hC : Ω' → (ℂ → ℝ) → ℝ} {hcirc : Ω' → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF Q hC hcirc)
    (hν : IsLQGMeasureOfField Q γ α hcirc ν) (hνm : AEMeasurable ν Q)
    (hpair : ∀ g : ℂ → ℝ, IsTestFunction univ g →
      Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          Q.map (localModConstPairings α hC univ) ∧
        Q.map (localModConstPairings α hC univ) ≪
          Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      interior (closure (cluster (μ ω) r z t)) = cluster (μ ω) r z t := by
  exact ae_no_regularization_defect_of_enclosing_identDistrib P Q μ ν hμm
    hr hrR ht hγ hz hvolume hfront hident
    (disc_restricted_lqg_shiftLaw_of_pairingLaws hGFF hν hνm hr hr1 hpair)

end MatedCRT
