import MatedCRT.Proofs.Field.Translation
import MatedCRT.Proofs.Field.WholePlaneGMCBridge
import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail

/-!
# Whole-plane GFF circle averages in the GMC interface

This bridge uses Leonardo Bonanno's `LQGDimension.IsGFFCircleAverage` interface
and his formula for its covariance (`Osc37.gffCircleCov_eq_circleAverage`).
The covariance kernels agree off the diagonal, which is invisible to a
nondegenerate circle average. A single null-set modification makes all sample
paths continuous in the centre, as required by Bonanno's interface.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls

theorem wholePlaneGFFCov_circle_eq_bonanno {r s : ℝ} (_hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    wholePlaneGFFCov (.circle r z) (.circle s w) = LQGDimension.gffCircleCov r z s w := by
  rw [LQGDimension.Osc37.gffCircleCov_eq_circleAverage]
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w s) z r = _
  congr 1
  funext x
  apply Real.circleAverage_congr_codiscreteWithin _ hs.ne'
  filter_upwards [compl_singleton_mem_codiscreteWithin (x := x) (s := sphere w |s|)] with y hy
  have hxy : x ≠ y := by simpa using Ne.symm hy
  rw [wholePlaneCov_eq hxy]
  simp only [LQGDimension.gffGreen, logMaxOne]
  ring

/-- An almost surely continuous modification satisfies Bonanno's circle-average
interface and agrees with all original circle averages on one event of probability one. -/
theorem IsWholePlaneGFF.exists_bonanno_circle_version {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H P ∧
      ∀ᵐ ω ∂P, ∀ r z, H r z ω = hcirc ω r z := by
  classical
  obtain ⟨bad, hsub, hbad, hzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp h.ae_continuousOn_circle)
  let H : ℝ → ℂ → Ω → ℝ := fun r z ω => if ω ∈ bad then 0 else hcirc ω r z
  have hae : ∀ᵐ ω ∂P, ∀ r z, H r z ω = hcirc ω r z := by
    have hn : ∀ᵐ ω ∂P, ω ∉ bad := by rw [ae_iff]; simpa using hzero
    filter_upwards [hn] with ω hω r z
    simp [H, hω]
  have heq (r : ℝ) (z : ℂ) : H r z =ᵐ[P] (fun ω => hcirc ω r z) := by
    filter_upwards [hae] with ω hω
    exact hω r z
  refine ⟨H, ⟨h.isProbabilityMeasure, ?_, ?_, ?_, ?_⟩, hae⟩
  · let f : Set.Ioi (0 : ℝ) × ℂ → GFFObservable.Admissible :=
      fun p => ⟨.circle p.1 p.2, p.1.2⟩
    exact (h.isGaussianProcess.comp_right f).congr (fun p => (heq p.1 p.2).symm)
  · intro r hr z
    rw [integral_congr_ae (heq r z)]
    exact h.integral_eq_zero (.circle r z) hr
  · intro r hr s hs z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (heq r z) (heq s w)]
    have hc := h.covariance_eq (.circle r z) (.circle s w) hr hs
    change cov[fun ω => hcirc ω r z, fun ω => hcirc ω s w; P] = _ at hc
    rw [hc]
    exact wholePlaneGFFCov_circle_eq_bonanno hr hs z w
  · intro r hr ω
    by_cases hω : ω ∈ bad
    · simpa [H, hω] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))
    · have hh : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
        by_contra hn
        exact hω (hsub hn)
      have hc : Continuous (fun z => hcirc ω r z) := by
        apply continuousOn_univ.mp
        apply hh.comp (continuous_const.prodMk continuous_id).continuousOn
        intro z _
        exact ⟨hr, mem_univ z⟩
      simpa [H, hω] using hc

/-- Bonanno's circle-average version carries the same LQG measure. -/
theorem IsWholePlaneGFF.exists_bonanno_gmc_version {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasure P γ hcirc μ) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H P ∧
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P ∧
      ∀ᵐ ω ∂P, ∀ r z, H r z ω = hcirc ω r z := by
  obtain ⟨H, hH, hae⟩ := IsWholePlaneGFF.exists_bonanno_circle_version h
  refine ⟨H, hH, ?_, hae⟩
  have hμ' := (isLQGMeasure_iff_isLQGAreaOf P γ hcirc μ).mp hμ
  filter_upwards [hae, hμ'] with ω hω hμω
  refine ⟨hμω.1, fun f hf hs => ?_⟩
  have heq (k : ℕ) : MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω =
      MatedCRTHarmonic.GMSLemma27.lqgApprox γ (fun r z ω => hcirc ω r z) k ω := by
    simp [MatedCRTHarmonic.GMSLemma27.lqgApprox, hω]
  simpa only [heq] using hμω.2 f hf hs

/-- The lower-tail estimate of Gwynne, Holden and Miller, proved by Bonanno,
applies to the Harmonic Balls whole-plane GFF and its LQG measure. -/
theorem wholePlane_gmc_lower_tail {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (s c : ℝ) (hc : 0 < c) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ z : ℂ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      (P {ω | μ ω (ball z ε) <
        ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))}).toReal ≤ c * δ ^ s := by
  obtain ⟨H, hH, harea, hae⟩ := IsWholePlaneGFF.exists_bonanno_gmc_version h hμ
  obtain ⟨δ₀, hδ₀, hbound⟩ :=
    MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2 Ω P H μ hH harea s c hc
  refine ⟨δ₀, hδ₀, fun δ hδ z ε hε => ?_⟩
  have hevent : {ω | μ ω (ball z ε) <
      ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))} =ᵐ[P]
      {ω | μ ω (ball z ε) <
      ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H ε z ω))} := by
    filter_upwards [hae] with ω hω
    simp [hω ε z]
  rw [measure_congr hevent]
  exact hbound δ hδ z ε hε

end MatedCRT.Field
