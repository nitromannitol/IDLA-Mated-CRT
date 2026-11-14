import MatedCRT.FirstPass.Derived.RevuzPositive
import MatedCRT.FirstPass.Derived.RevuzFormula
import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar

/-!
# Upgrade from almost every starting point to every starting point for PCAFs of planar Brownian motion

Two positive continuous additive functionals of planar Brownian motion that are indistinguishable under the
law from Lebesgue-almost every starting point are indistinguishable under the law from every starting point.
The argument is the Markov property at a positive deterministic time `ε`, at which the path has a Gaussian law
(absolutely continuous with respect to Lebesgue measure), together with additivity and path continuity at `0`:
`A_{ε+q} = A_ε + A_q ∘ θ_ε`, so `A_{ε+q} - A'_{ε+q} = A_ε - A'_ε` almost surely, and `ε → 0`.

* `planarGaussian_absolutelyContinuous`: the planar Gaussian law of positive variance is absolutely continuous
  with respect to Lebesgue measure;
* `ae_shift_mem_of_ae_start`: a measurable path set that is almost surely hit from Lebesgue-almost every
  starting point is almost surely hit by the shifted path at a positive time, from every starting point;
* `eq_of_continuous_of_eq_nnrat`: continuous functions on `ℝ≥0` that agree on the nonnegative rationals agree;
* `ae_start_upgrade`: the upgrade.
-/

open MeasureTheory MarkovProcess Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

/-- The planar Gaussian law of positive variance is absolutely continuous with respect to Lebesgue measure. -/
theorem planarGaussian_absolutelyContinuous (z : ℂ) {t : ℝ≥0} (ht : t ≠ 0) :
    HarmonicBalls.planarGaussian z t ≪ (volume : Measure ℂ) := by
  have h1 : (ProbabilityTheory.gaussianReal z.re t).prod (ProbabilityTheory.gaussianReal z.im t) ≪
      (volume : Measure ℝ).prod volume :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous _ ht).prod
      (ProbabilityTheory.gaussianReal_absolutelyContinuous _ ht)
  have h2 : ((volume : Measure ℝ).prod volume).map Complex.measurableEquivRealProd.symm = volume :=
    (Complex.volume_preserving_equiv_real_prod.symm).map_eq
  have h3 := h1.map Complex.measurableEquivRealProd.symm.measurable
  rw [h2] at h3
  exact h3

/-- **A measurable path set that is almost surely hit from Lebesgue-almost every starting point is almost
surely hit by the path shifted by a positive deterministic time, from every starting point.** -/
theorem ae_shift_mem_of_ae_start {H : Set (ContinuousPath ℂ)} (hH : MeasurableSet H)
    (h : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ ω ∂planarLaw y, ω ∈ H) (z : ℂ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∀ᵐ ω ∂planarLaw z, LatticeProb.pathShift ω ε ∈ H := by
  have hmap : (planarLaw z).map (ContinuousPath.shift ε) =
      (HarmonicBalls.planarGaussian z ε).bind planarLaw :=
    MatedCRT.KilledOccupation.planarBrownianMotion_map_shift z ε
  have hcont : Measurable (ContinuousPath.shift ε : ContinuousPath ℂ → ContinuousPath ℂ) :=
    (ContinuousPath.continuous_shift_fixed ε).measurable
  have hy : ∀ᵐ y ∂(HarmonicBalls.planarGaussian z ε), planarLaw y Hᶜ = 0 :=
    (planarGaussian_absolutelyContinuous z hε).ae_le (by
      filter_upwards [h] with y hy
      exact ae_iff.1 hy)
  rw [ae_iff]
  have e : planarLaw z {ω | ¬ LatticeProb.pathShift ω ε ∈ H} = ((planarLaw z).map (ContinuousPath.shift ε)) Hᶜ := by
    rw [Measure.map_apply hcont hH.compl]
    rfl
  rw [e, hmap, Measure.bind_apply hH.compl measurable_planarLaw.aemeasurable, lintegral_congr_ae hy]
  simp

/-- Continuous functions on `ℝ≥0` that agree on the nonnegative rationals agree. -/
theorem eq_of_continuous_of_eq_nnrat {f g : ℝ≥0 → ℝ≥0} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : ℚ≥0, f q = g q) : f = g := by
  funext t
  have hd : t ∈ closure (Set.range ((↑) : ℚ≥0 → ℝ≥0)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal
      (show t < t + ε.toNNReal by simpa using Real.toNNReal_pos.2 hε)
    refine ⟨q, ⟨q, rfl⟩, ?_⟩
    have h1 : (t : ℝ) < q := by exact_mod_cast hq1
    have h2 : ((q : ℝ≥0) : ℝ) < t + ε := by
      have := NNReal.coe_lt_coe.2 hq2
      rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
    rw [NNReal.dist_eq, abs_of_neg (by linarith)]
    linarith
  exact closure_minimal (by rintro x ⟨q, rfl⟩; exact h q) (isClosed_eq hf hg) hd

/-- **Upgrade from almost every starting point to every starting point.**  If two PCAFs of planar Brownian
motion are indistinguishable under the law from Lebesgue-almost every starting point, they are
indistinguishable under the law from every starting point. -/
theorem ae_start_upgrade {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (hA' : IsPCAF planarLaw A')
    (h : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂planarLaw z, ∀ t, A t ω = A' t ω) (z : ℂ) :
    ∀ᵐ ω ∂planarLaw z, ∀ t, A t ω = A' t ω := by
  set H : Set (ContinuousPath ℂ) := {ω | ∀ q : ℚ≥0, A q ω = A' q ω} with hHdef
  have hH : MeasurableSet H := by
    simp only [hHdef, Set.ofPred_forall]
    exact MeasurableSet.iInter fun q => measurableSet_eq_fun (hA.meas _) (hA'.meas _)
  have hHy : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ ω ∂planarLaw y, ω ∈ H := by
    filter_upwards [h] with y hy
    filter_upwards [hy] with ω hω q using hω q
  -- the shifts `ε n = 1 / (n + 1)`
  set ε : ℕ → ℝ≥0 := fun n => Real.toNNReal (1 / ((n : ℝ) + 1)) with hεdef
  have hε0 : ∀ n, ε n ≠ 0 := fun n => (Real.toNNReal_pos.2 (by positivity)).ne'
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (continuous_real_toNNReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.toNNReal_zero] at this
    exact this
  have hn : ∀ᵐ ω ∂planarLaw z, ∀ n, LatticeProb.pathShift ω (ε n) ∈ H :=
    ae_all_iff.2 fun n => ae_shift_mem_of_ae_start hH hHy z (hε0 n)
  have hadd : ∀ᵐ ω ∂planarLaw z, ∀ (n : ℕ) (q : ℚ≥0),
      A (ε n + q) ω = A (ε n) ω + A q (LatticeProb.pathShift ω (ε n)) ∧
      A' (ε n + q) ω = A' (ε n) ω + A' q (LatticeProb.pathShift ω (ε n)) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun q => by
      filter_upwards [hA.add z q (ε n), hA'.add z q (ε n)] with ω h1 h2 using ⟨h1, h2⟩
  filter_upwards [hA.path z, hA'.path z, hn, hadd] with ω hp hp' hn hadd
  obtain ⟨h0, hc, -⟩ := hp
  obtain ⟨h0', hc', -⟩ := hp'
  have hrat : ∀ q : ℚ≥0, A q ω = A' q ω := by
    intro q
    have key : ∀ n, A (ε n + q) ω + A' (ε n) ω = A' (ε n + q) ω + A (ε n) ω := by
      intro n
      obtain ⟨e1, e2⟩ := hadd n q
      rw [e1, e2, hn n q]
      ring
    have t1 : Tendsto (fun n => A (ε n + q) ω + A' (ε n) ω) atTop (𝓝 (A q ω + A' 0 ω)) := by
      have a1 : Tendsto (fun n => A (ε n + q) ω) atTop (𝓝 (A (0 + q) ω)) :=
        (hc.tendsto _).comp (hεlim.add tendsto_const_nhds)
      have a2 : Tendsto (fun n => A' (ε n) ω) atTop (𝓝 (A' 0 ω)) := (hc'.tendsto _).comp hεlim
      simpa using a1.add a2
    have t2 : Tendsto (fun n => A' (ε n + q) ω + A (ε n) ω) atTop (𝓝 (A' q ω + A 0 ω)) := by
      have a1 : Tendsto (fun n => A' (ε n + q) ω) atTop (𝓝 (A' (0 + q) ω)) :=
        (hc'.tendsto _).comp (hεlim.add tendsto_const_nhds)
      have a2 : Tendsto (fun n => A (ε n) ω) atTop (𝓝 (A 0 ω)) := (hc.tendsto _).comp hεlim
      simpa using a1.add a2
    have := tendsto_nhds_unique (t1.congr key) t2
    simpa [h0, h0'] using this
  intro t
  exact congr_fun (eq_of_continuous_of_eq_nnrat hc hc' hrat) t

end MatedCRT
