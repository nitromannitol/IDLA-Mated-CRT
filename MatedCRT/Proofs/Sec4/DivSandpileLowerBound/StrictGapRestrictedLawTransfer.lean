import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRestrictedComparison
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapFrontierLocality
import Mathlib.Probability.IdentDistrib

/-! # Transfer of restricted mass-shift laws -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

/-- Equality in law on an enclosing set also gives equality in law after
    restriction to a smaller set and multiplication by a fixed scalar. -/
theorem identDistrib_smul_restrict_of_enclosing
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {μ : Ω → Measure ℂ} {ν : Ω' → Measure ℂ}
    {A B : Set ℂ} (hA : MeasurableSet A) (_hB : MeasurableSet B) (hAB : A ⊆ B)
    (h : IdentDistrib (fun ω => (μ ω).restrict B) (fun ω => (ν ω).restrict B) P Q)
    (a : ℝ≥0∞) :
    IdentDistrib (fun ω => a • (μ ω).restrict A) (fun ω => a • (ν ω).restrict A) P Q := by
  have hm : Measurable (fun m : Measure ℂ => a • m.restrict A) :=
    (measurable_restricted_smul_measure A hA).comp (measurable_const.prodMk measurable_id)
  have hi := h.comp hm
  simpa only [Function.comp_def, Measure.restrict_restrict hA, inter_eq_self_of_subset_left hAB] using hi

/-- A shift-law domination transfers between models whose enclosing restricted
    measures have the same law. -/
theorem restricted_shiftLaw_of_enclosing_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {μ : Ω → Measure ℂ} {ν : Ω' → Measure ℂ}
    {A B : Set ℂ} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (h : IdentDistrib (fun ω => (μ ω).restrict B) (fun ω => (ν ω).restrict B) P Q)
    (a b : ℝ≥0∞)
    (hshift : Q.map (fun ω => a • (ν ω).restrict A) ≪
      Q.map (fun ω => b • (ν ω).restrict A)) :
    P.map (fun ω => a • (μ ω).restrict A) ≪
      P.map (fun ω => b • (μ ω).restrict A) := by
  rw [(identDistrib_smul_restrict_of_enclosing hA hB hAB h a).map_eq,
    (identDistrib_smul_restrict_of_enclosing hA hB hAB h b).map_eq]
  exact hshift

/-- Fixed-time regularization follows from frontier nullity and a shifted
    law in any model with the same enclosing restricted measure law. -/
theorem ae_no_regularization_defect_of_enclosing_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [SFinite P] (Q : Measure Ω')
    (μ : Ω → Measure ℂ) (ν : Ω' → Measure ℂ) (hμm : AEMeasurable μ P)
    {r R t γ : ℝ} {z : ℂ}
    (hr : 0 < r) (hrR : r ≤ R) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 r)
    (hvolume : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      HarmonicBalls.VolumeGrowth (μ ω) r βm βp)
    (hfront : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      μ ω (frontier (HarmonicBalls.cluster (μ ω) R z s) ∩ ball 0 R) = 0)
    (hident : IdentDistrib (fun ω => (μ ω).restrict (ball 0 R))
      (fun ω => (ν ω).restrict (ball 0 R)) P Q)
    (hshift : ∀ c : ℝ,
      Q.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) • (ν ω).restrict (ball 0 r)) ≪
      Q.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) • (ν ω).restrict (ball 0 r))) :
    ∀ᵐ ω ∂P, closure (HarmonicBalls.cluster (μ ω) r z t) ⊆ ball 0 r →
      interior (closure (HarmonicBalls.cluster (μ ω) r z t)) =
        HarmonicBalls.cluster (μ ω) r z t := by
  apply ae_no_regularization_defect_of_enclosing_frontier_and_restricted_law
    P μ hμm hr hrR ht hγ hz hvolume hfront
  intro c
  exact restricted_shiftLaw_of_enclosing_identDistrib measurableSet_ball measurableSet_ball
    (ball_subset_ball hrR) hident _ _ (hshift c)

end MatedCRT
