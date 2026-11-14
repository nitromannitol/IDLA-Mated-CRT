import MatedCRT.FirstPass.Derived.RevuzFormula

/-!
# Positivity of the Revuz measure of a good clock

For a positive continuous additive functional with a good clock (almost surely strictly increasing and unbounded) of
a family of path laws that start at their starting point, the Revuz measure with respect to Lebesgue measure charges
every nonempty open set:

* for a continuous strictly increasing clock `a` and a path `ω` with `ω 0 ∈ U`, `U` open, the occupation measure
  `∫_{(0,1]} 1_U(ω_s) da_s` is positive (`occupationMeasure_pos_of_start`), because `ω` stays in `U` on a short
  interval `[0, δ)` and `a` increases on it;
* integrating over the starting points in `U` gives `0 < revuz W A U` (`revuz_pos_of_goodClock`), in particular
  `revuz W A ≠ 0` (`revuz_ne_zero_of_goodClock`).

For planar Brownian motion the hypotheses on the laws hold (`measurable_planarLaw`, `planarLaw_ne_zero`,
`ae_planarLaw_eval_zero`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The Stieltjes function of a continuous nondecreasing clock is the clock itself. -/
theorem stieltjesOfNNReal_apply_of_continuous {a : ℝ≥0 → ℝ≥0} (hm : Monotone a) (hc : Continuous a) (x : ℝ) :
    stieltjesOfNNReal a x = (a x.toNNReal : ℝ) := by
  have hf : Monotone (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) :=
    fun x y hxy => by exact_mod_cast hm (Real.toNNReal_mono hxy)
  have hcont : Continuous (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (hc.comp continuous_real_toNNReal)
  unfold stieltjesOfNNReal
  simp only [hm, ↓reduceDIte]
  rw [Monotone.stieltjesFunction_eq]
  exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 hcont.continuousWithinAt

/-- The Stieltjes measure of an interval is the increment of a continuous nondecreasing clock. -/
theorem stieltjesOfNNReal_measure_Ioc {a : ℝ≥0 → ℝ≥0} (hm : Monotone a) (hc : Continuous a) (x y : ℝ) :
    (stieltjesOfNNReal a).measure (Ioc x y) = ENNReal.ofReal ((a y.toNNReal : ℝ) - a x.toNNReal) := by
  rw [StieltjesFunction.measure_Ioc, stieltjesOfNNReal_apply_of_continuous hm hc,
    stieltjesOfNNReal_apply_of_continuous hm hc]

/-- A path that starts in an open set `U` charges `U` with a positive occupation measure for a continuous strictly
increasing clock. -/
theorem occupationMeasure_pos_of_start {a : ℝ≥0 → ℝ≥0} (hc : Continuous a) (hs : StrictMono a)
    {ω : ContinuousPath ℂ} {U : Set ℂ} (hU : IsOpen U) (h0 : ω 0 ∈ U) :
    0 < occupationMeasure a ω U := by
  have hcm : Continuous fun s : ℝ => ω s.toNNReal := ω.continuous.comp continuous_real_toNNReal
  have hV : IsOpen ((fun s : ℝ => ω s.toNNReal) ⁻¹' U) := hU.preimage hcm
  have h0V : (0 : ℝ) ∈ (fun s : ℝ => ω s.toNNReal) ⁻¹' U := by simpa using h0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV 0 h0V
  have hmpos : 0 < min (ε / 2) 1 := lt_min (half_pos hε) one_pos
  have hsub : Ioc (0 : ℝ) (min (ε / 2) 1) ⊆ (fun s : ℝ => ω s.toNNReal) ⁻¹' U ∩ Ioc 0 1 := fun s hs' =>
    ⟨hball (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs'.1]
        exact lt_of_le_of_lt hs'.2 (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))),
      ⟨hs'.1, hs'.2.trans (min_le_right _ _)⟩⟩
  unfold occupationMeasure
  rw [Measure.map_apply hcm.measurable hU.measurableSet, Measure.restrict_apply hV.measurableSet]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [stieltjesOfNNReal_measure_Ioc hs.monotone hc]
  refine ENNReal.ofReal_pos.2 ?_
  have h1 : (0 : ℝ≥0) < (min (ε / 2) 1).toNNReal := Real.toNNReal_pos.2 hmpos
  have h2 := hs h1
  rw [Real.toNNReal_zero]
  exact sub_pos.2 (NNReal.coe_lt_coe.2 h2)

/-- **The Revuz measure of a good clock charges every nonempty open set**: if the laws `W z` are nonzero and start at
`z`, `A` is a positive continuous additive functional with a good clock, and its occupation kernel is measurable
(supplied by `measurable_occupationMeasure_regularize`), then `0 < revuz W A U` for every nonempty open `U`. -/
theorem revuz_pos_of_goodClock {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    (hW0 : ∀ z, W z ≠ 0) (hstart : ∀ z, ∀ᵐ ω ∂W z, ω 0 = z)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (hG : GoodClock W A)
    (hk : Measurable fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize A t ω) ω)
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) : 0 < revuz W A U := by
  rw [revuz_apply hW hk hU.measurableSet]
  have hfm : Measurable fun ω : ContinuousPath ℂ =>
      occupationMeasure (fun t => regularize A t ω) ω U := (Measure.measurable_coe hU.measurableSet).comp hk
  have hg : Measurable fun z => ∫⁻ ω, occupationMeasure (fun t => regularize A t ω) ω U ∂W z :=
    (Measure.measurable_lintegral hfm).comp hW
  have hpos : ∀ z ∈ U, 0 < ∫⁻ ω, occupationMeasure (fun t => regularize A t ω) ω U ∂W z := by
    intro z hz
    by_contra hle
    have h0 : ∫⁻ ω, occupationMeasure (fun t => regularize A t ω) ω U ∂W z = 0 :=
      nonpos_iff_eq_zero.1 (not_lt.1 hle)
    have hae := (lintegral_eq_zero_iff hfm).1 h0
    have hbad : ∀ᵐ ω ∂W z, False := by
      filter_upwards [hae, hstart z, hA.path z, hG z] with ω h1 h2 h3 h4
      have hpos' := occupationMeasure_pos_of_start (a := fun t => A t ω) h3.2.1 h4.1 hU
        (by rw [h2]; exact hz)
      simp only [Pi.zero_apply] at h1
      rw [occupationMeasure_regularize_eq_of_path h3.2.1 h3.2.2] at h1
      exact hpos'.ne' h1
    exact hW0 z (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hbad))
  by_contra hle
  have h0 : ∫⁻ z, ∫⁻ ω, occupationMeasure (fun t => regularize A t ω) ω U ∂W z ∂volume = 0 :=
    nonpos_iff_eq_zero.1 (not_lt.1 hle)
  have hae := (lintegral_eq_zero_iff hg).1 h0
  have hnull : volume {z : ℂ | ¬ (∫⁻ ω, occupationMeasure (fun t => regularize A t ω) ω U ∂W z) = 0} = 0 :=
    ae_iff.1 hae
  have hU0 : volume U = 0 := measure_mono_null (fun z hz h => (hpos z hz).ne' h) hnull
  exact (hU.measure_pos volume hne).ne' hU0

/-- The Revuz measure of a good clock is nonzero. -/
theorem revuz_ne_zero_of_goodClock {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    (hW0 : ∀ z, W z ≠ 0) (hstart : ∀ z, ∀ᵐ ω ∂W z, ω 0 = z)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (hG : GoodClock W A)
    (hk : Measurable fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize A t ω) ω) :
    revuz W A ≠ 0 := fun h => by
  have := revuz_pos_of_goodClock hW hW0 hstart hA hG hk isOpen_univ Set.univ_nonempty
  rw [h] at this
  simp at this

/-- The planar Brownian laws are a measurable family of measures. -/
theorem measurable_planarLaw : Measurable planarLaw := HarmonicBalls.planarBrownianMotion.measurable

/-- The planar Brownian laws are probability measures, in particular nonzero. -/
theorem planarLaw_ne_zero (z : ℂ) : planarLaw z ≠ 0 :=
  (inferInstance : IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion z)).ne_zero

/-- Planar Brownian motion started from `z` starts at `z` almost surely. -/
theorem ae_planarLaw_eval_zero (z : ℂ) : ∀ᵐ ω ∂planarLaw z, ω 0 = z :=
  HarmonicBalls.ae_planarBrownianMotion_eval_zero z

end MatedCRT
