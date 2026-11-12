import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureScaling
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureLipschitz
import MatedCRT.Proofs.Sec1.EnvironmentScalingRadius
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScalingPositivity
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma

/-!
# Convergence of the degree-weighted measure for test functions with arbitrary bounded support

The scaling step of BG20, Corollary A.6 (Lemma 2.10 of the paper): the convergence `∫ g dμ^ε_h → 6 ∫ g dμ_h` in
probability for test functions vanishing off `B_{1/2}`, holding for every valid environment and uniformly in the test
function (the test function may depend on `ω`), transfers to every bounded Lipschitz test function `f` vanishing off
an arbitrary ball `B_{R₀}`. For `b = n + 1` the rescaled environment `S'_n` of `ConeEnvironmentScalingStep` has
`∫ f dμ^ε_h - 6 ∫ f dμ_h = b (∫ f(R_b ·) dμ'^{ε/b} - 6 ∫ f(R_b ·) dμ')` almost surely
(`MatedCRTEnv.ae_integral_degreeWeightedMeasure_eq_rescale`); on the event `2 max(R₀, 1) < R_b ≤ M` the function
`f(R_b ·)` vanishes off `B_{1/2}` and is `L M`-Lipschitz. Since `R_{n+1} → ∞` almost surely
(`MatedCRTEnv.IsValid.ae_exists_lt_coneScaleRadius`, from the behaviour of the radial part of the quantum cone at `0`)
and each `R_{n+1}` has a measurable version, the events not covered by finitely many scales and a bound `M` have
small probability.

* `MatedCRTEnv.IsValid.ae_exists_lt_coneScaleRadius`: almost surely `R < R_{n+1}` for some `n`;
* `tendstoInProbability_degreeWeightedMeasure_of_scaling`: the transfer.
-/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology HarmonicBalls
open scoped ENNReal

/-- **Exhaustion by cone scale radii.** For a valid environment, almost surely the cone scale radii `R_{n+1}`
(eq:cone-scale-radius) exceed any given `R` for some `n`: the radial part `h_r(0) + Q log r` tends to `-∞` as `r → 0`
and is continuous, so it is bounded above on every `(0, M]`, while `R_{n+1} > 0` almost surely. -/
theorem MatedCRTEnv.IsValid.ae_exists_lt_coneScaleRadius {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hscale : QuantumConeScalingInput) (R : ℝ) :
    ∀ᵐ ω ∂S.P, ∃ n : ℕ, R < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := by
  have := hS.isProbabilityMeasure
  have hpositive (n : ℕ) : ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) :=
    Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone (by positivity)
  filter_upwards [hS.isQuantumCone.ae_radial_expression_tendsto_origin hγ hγ2,
    hS.isQuantumCone.ae_continuousOn_circle, ae_all_iff.mpr hpositive] with ω hzero hc hpos
  have hcircle : ContinuousOn (fun r : ℝ => S.hcirc ω r 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono (fun _ hr => ne_of_gt hr)
  have hcont : ContinuousOn (fun r : ℝ => S.hcirc ω r 0 + lqgQ γ * Real.log r) (Ioi 0) :=
    hcircle.add (continuousOn_const.mul hlog)
  have hlocal : ∀ M : ℝ, 0 < M →
      BddAbove ((fun r => S.hcirc ω r 0 + lqgQ γ * Real.log r) '' Ioc 0 M) :=
    fun M _ => bddAbove_image_Ioc_of_tendsto_atBot hcont hzero
  have ht := coneScaleRadius_tendsto_of_radial_bound hγ (S.hcirc ω) hlocal hpos
  obtain ⟨n, hn⟩ := ((tendsto_atTop.1 ht) (R + 1)).exists
  exact ⟨n, by linarith⟩

/-- `f(R ·)` when `2 R₁ < R ≤ M`, and `0` otherwise. -/
private noncomputable def truncatedDilation (f : ℂ → ℝ) (R₁ M R : ℝ) (x : ℂ) : ℝ :=
  if 2 * R₁ < R ∧ R ≤ M then f ((R : ℂ) * x) else 0

private theorem truncatedDilation_of_cond {f : ℂ → ℝ} {R₁ M R : ℝ} (h : 2 * R₁ < R ∧ R ≤ M) (x : ℂ) :
    truncatedDilation f R₁ M R x = f ((R : ℂ) * x) := by
  unfold truncatedDilation
  split_ifs with hc
  · rfl
  · exact absurd h hc

private theorem truncatedDilation_of_not_cond {f : ℂ → ℝ} {R₁ M R : ℝ} (h : ¬(2 * R₁ < R ∧ R ≤ M)) (x : ℂ) :
    truncatedDilation f R₁ M R x = 0 := by
  unfold truncatedDilation
  split_ifs with hc
  · exact absurd hc h
  · rfl

private theorem truncatedDilation_continuous {f : ℂ → ℝ} (hf : Continuous f) (R₁ M R : ℝ) :
    Continuous (truncatedDilation f R₁ M R) := by
  by_cases h : 2 * R₁ < R ∧ R ≤ M
  · rw [show truncatedDilation f R₁ M R = fun x => f ((R : ℂ) * x) from
      funext (truncatedDilation_of_cond h)]
    exact hf.comp (continuous_const.mul continuous_id)
  · rw [show truncatedDilation f R₁ M R = fun _ => 0 from funext (truncatedDilation_of_not_cond h)]
    exact continuous_const

private theorem abs_truncatedDilation_le {f : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hfK : ∀ x, |f x| ≤ K)
    (R₁ M R : ℝ) (x : ℂ) : |truncatedDilation f R₁ M R x| ≤ K := by
  by_cases h : 2 * R₁ < R ∧ R ≤ M
  · rw [truncatedDilation_of_cond h]
    exact hfK _
  · rw [truncatedDilation_of_not_cond h, abs_zero]
    exact hK

private theorem truncatedDilation_lipschitz {f : ℂ → ℝ} {L : ℝ} (hfL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    {R₁ : ℝ} (hR₁ : 0 < R₁) (M R : ℝ) (x y : ℂ) :
    |truncatedDilation f R₁ M R x - truncatedDilation f R₁ M R y| ≤ max L 0 * max M 0 * ‖x - y‖ := by
  by_cases h : 2 * R₁ < R ∧ R ≤ M
  · rw [truncatedDilation_of_cond h, truncatedDilation_of_cond h]
    have hR : 0 < R := by linarith [h.1]
    have hn : ‖(R : ℂ) * x - (R : ℂ) * y‖ = R * ‖x - y‖ := by
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    calc |f ((R : ℂ) * x) - f ((R : ℂ) * y)| ≤ L * ‖(R : ℂ) * x - (R : ℂ) * y‖ := hfL _ _
      _ ≤ max L 0 * ‖(R : ℂ) * x - (R : ℂ) * y‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ = max L 0 * (R * ‖x - y‖) := by rw [hn]
      _ ≤ max L 0 * (max M 0 * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (h.2.trans (le_max_left _ _)) (norm_nonneg _)) (le_max_right _ _)
      _ = max L 0 * max M 0 * ‖x - y‖ := by ring
  · rw [truncatedDilation_of_not_cond h, truncatedDilation_of_not_cond h, sub_self, abs_zero]
    have h1 : 0 ≤ max L 0 := le_max_right _ _
    have h2 : 0 ≤ max M 0 := le_max_right _ _
    positivity

private theorem truncatedDilation_eq_zero {f : ℂ → ℝ} {R₀ : ℝ} (hfR : ∀ x ∉ ball (0 : ℂ) R₀, f x = 0)
    {R₁ : ℝ} (hR₀ : R₀ ≤ R₁) (hR₁ : 0 < R₁) (M R : ℝ) (x : ℂ) (hx : x ∉ ball (0 : ℂ) (1 / 2)) :
    truncatedDilation f R₁ M R x = 0 := by
  by_cases h : 2 * R₁ < R ∧ R ≤ M
  · rw [truncatedDilation_of_cond h]
    refine hfR _ fun hmem => ?_
    have hR : 0 < R := by linarith [h.1]
    rw [mem_ball_zero_iff, not_lt] at hx
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le] at hmem
    nlinarith [h.1]
  · exact truncatedDilation_of_not_cond h x

private theorem tendsto_div_const_nhdsGT_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ε / b) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => div_pos hx hb⟩
  have h : Tendsto (fun ε : ℝ => ε / b) (𝓝 0) (𝓝 (0 / b)) := (continuous_id.div_const b).tendsto 0
  rw [zero_div] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Corollary A.6 for Lipschitz test functions with arbitrary bounded support, by scale invariance** (BG20, proof
of Corollary A.6; scale invariance of the `γ`-quantum cone, BG20 Lemma 2.3, in the form of
`ConeEnvironmentScalingStep`). Suppose that for every valid environment on `Ω` the convergence
`∫ g_ω dμ^ε_h → 6 ∫ g_ω dμ_h` in probability holds for all test functions `g_ω` (depending on `ω` arbitrarily) that are
continuous, bounded by `K`, `L`-Lipschitz and vanish off `B_{1/2}` (`tendstoInProbability_degreeWeightedMeasure_of_ball_random`).
Then for every continuous `f` with `|f| ≤ K`, `L`-Lipschitz and vanishing off some ball `B_{R₀}`,
`∫ f dμ^ε_h → 6 ∫ f dμ_h` in probability. -/
theorem tendstoInProbability_degreeWeightedMeasure_of_scaling {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hscale : QuantumConeScalingInput) (hEnv : ConeEnvironmentScalingStep 𝒮)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hball : ∀ S' : MatedCRTEnv Ω, S'.IsValid 𝒮 γ → ∀ (g : Ω → ℂ → ℝ) (K L : ℝ),
      (∀ ω, Continuous (g ω)) → (∀ ω x, |g ω x| ≤ K) → (∀ ω x y, |g ω x - g ω y| ≤ L * ‖x - y‖) →
      (∀ ω, ∀ x ∉ ball (0 : ℂ) (1 / 2), g ω x = 0) →
      TendstoInProbability S'.P
        (fun ε ω => ∫ x, g ω x ∂degreeWeightedMeasure (S'.mult ε ω) ε (S'.η ω) (S'.μ ω))
        (fun ω => 6 * ∫ x, g ω x ∂S'.μ ω))
    {f : ℂ → ℝ} (hf : Continuous f) {K L R₀ : ℝ} (hfK : ∀ x, |f x| ≤ K)
    (hfL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (hfR : ∀ x ∉ ball (0 : ℂ) R₀, f x = 0) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, f x ∂S.μ ω) := by
  have hP := hS.isProbabilityMeasure
  set R₁ : ℝ := max R₀ 1 with hR₁
  have hR₁0 : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR₀₁ : R₀ ≤ R₁ := le_max_left _ _
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hfK 0)
  have hb : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hS' : ∀ n : ℕ, ∃ S' : MatedCRTEnv Ω, S'.IsValid 𝒮 γ ∧ S'.P = S.P ∧
      (∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.η ω s =
        ((coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ * S.η ω (((n : ℝ) + 1) * s)) ∧
      (∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.bm ω s = (Real.sqrt ((n : ℝ) + 1))⁻¹ • S.bm ω (((n : ℝ) + 1) * s)) ∧
      (∀ᵐ ω ∂S.P, S'.μ ω =
        rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n => hEnv γ hγ hγ2 Ω S hS _ (hb n)
  choose S' hS'v hS'P hS'η hS'bm hS'μ using hS'
  have hpos : ∀ n : ℕ, ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := fun n =>
    Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone (hb n)
  have hver : ∀ n : ℕ, ∃ R' : Ω → ℝ, Measurable R' ∧
      R' =ᵐ[S.P] fun ω => coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := fun n => by
    obtain ⟨R', hm, he⟩ := Sec1.exists_fieldMeasurable_coneScaleRadius hscale hγ hγ2 hS (hb n)
    exact ⟨R', hm.mono (MatedCRTEnv.fieldSigma_le S hS) le_rfl, he⟩
  choose R' hR'm hR'e using hver
  have hexR' : ∀ᵐ ω ∂S.P, ∃ n : ℕ, 2 * R₁ < R' n ω := by
    filter_upwards [hS.ae_exists_lt_coneScaleRadius hγ hγ2 hscale (2 * R₁), ae_all_iff.2 hR'e]
      with ω hω he
    obtain ⟨n, hn⟩ := hω
    have hen : R' n ω = coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := he n
    exact ⟨n, by rw [hen]; exact hn⟩
  -- the event that no scale `n ≤ N` is large enough has small probability for large `N`
  have hA : Tendsto (fun N : ℕ => S.P {ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁}) atTop (𝓝 0) := by
    have hmeas : ∀ N : ℕ, MeasurableSet {ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁} := fun N => by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        measurableSet_le (hR'm n) measurable_const
    have hanti : Antitone fun N : ℕ => {ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁} :=
      fun N N' hNN' ω hω n hn => hω n (hn.trans hNN')
    have h := tendsto_measure_iInter_atTop (μ := S.P) (fun N => (hmeas N).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have h0 : S.P (⋂ N : ℕ, {ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁}) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hexR')
      rintro ω hω ⟨n, hn⟩
      exact absurd ((mem_iInter.1 hω n) n le_rfl) (not_le.2 hn)
    rw [h0] at h
    exact h
  -- the event that some scale `n ≤ N` exceeds `M` has small probability for large `M`
  have hBM : ∀ N : ℕ, Tendsto (fun M : ℝ => ∑ n ∈ Finset.range (N + 1), S.P {ω | M < R' n ω}) atTop (𝓝 0) :=
    fun N => by
      have h := tendsto_finsetSum (Finset.range (N + 1)) fun n _ =>
        Sec1.tendsto_measure_lt_atTop (P := S.P) (hR'm n).aemeasurable
      simpa using h
  intro δ hδ
  -- convergence on each rescaled environment
  have hconv : ∀ (n : ℕ) (M : ℝ), Tendsto (fun ε => S.P {ω | δ / ((n : ℝ) + 1) <
      |∫ x, truncatedDilation f R₁ M (R' n ω) x ∂degreeWeightedMeasure ((S' n).mult (ε / ((n : ℝ) + 1)) ω)
          (ε / ((n : ℝ) + 1)) ((S' n).η ω) ((S' n).μ ω) -
        6 * ∫ x, truncatedDilation f R₁ M (R' n ω) x ∂(S' n).μ ω|}) (𝓝[>] 0) (𝓝 0) := by
    intro n M
    have h := hball (S' n) (hS'v n) (fun ω => truncatedDilation f R₁ M (R' n ω)) K (max L 0 * max M 0)
      (fun ω => truncatedDilation_continuous hf _ _ _) (fun ω => abs_truncatedDilation_le hK0 hfK _ _ _)
      (fun ω => truncatedDilation_lipschitz hfL hR₁0 _ _) (fun ω => truncatedDilation_eq_zero hfR hR₀₁ hR₁0 _ _)
    rw [hS'P n] at h
    exact (h _ (div_pos hδ (hb n))).comp (tendsto_div_const_nhdsGT_zero (hb n))
  -- the deterministic inclusion, almost surely
  have hincl : ∀ᵐ ω ∂S.P, ∀ (N : ℕ) (M ε : ℝ),
      δ < |∫ x, f x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω) - 6 * ∫ x, f x ∂S.μ ω| →
      ω ∈ {ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁} ∪ (⋃ n ∈ Finset.range (N + 1), {ω | M < R' n ω}) ∪
        ⋃ n ∈ Finset.range (N + 1), {ω | δ / ((n : ℝ) + 1) <
          |∫ x, truncatedDilation f R₁ M (R' n ω) x ∂degreeWeightedMeasure ((S' n).mult (ε / ((n : ℝ) + 1)) ω)
              (ε / ((n : ℝ) + 1)) ((S' n).η ω) ((S' n).μ ω) -
            6 * ∫ x, truncatedDilation f R₁ M (R' n ω) x ∂(S' n).μ ω|} := by
    filter_upwards [ae_all_iff.2 hR'e, ae_all_iff.2 fun n =>
      MatedCRTEnv.ae_integral_degreeWeightedMeasure_eq_rescale S (S' n) γ (hb n) (hpos n) (hS'η n) (hS'bm n)
        (hS'μ n)] with ω hRe hId N M ε hδε
    by_cases h1 : ∀ n ≤ N, R' n ω ≤ 2 * R₁
    · exact Or.inl (Or.inl h1)
    simp only [not_forall, not_le] at h1
    obtain ⟨n, hnN, hn⟩ := h1
    have hnr : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hnN)
    by_cases h2 : M < R' n ω
    · exact Or.inl (Or.inr (mem_biUnion hnr h2))
    refine Or.inr (mem_biUnion hnr ?_)
    have hen : R' n ω = coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) := hRe n
    have hg : truncatedDilation f R₁ M (R' n ω) =
        fun x => f (((coneScaleRadius γ (S.hcirc ω) ((n : ℝ) + 1) : ℝ) : ℂ) * x) := by
      funext x
      rw [truncatedDilation_of_cond ⟨hn, not_lt.1 h2⟩, hen]
    rw [hId n ε f, abs_mul, abs_of_pos (hb n)] at hδε
    show δ / ((n : ℝ) + 1) < _
    rw [hg, div_lt_iff₀ (hb n)]
    linarith
  refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hη4 : 0 < η / 2 / 2 := ENNReal.half_pos hη2.ne'
  obtain ⟨N, hN⟩ := (hA.eventually (Iic_mem_nhds hη2)).exists
  obtain ⟨M, hM⟩ := ((hBM N).eventually (Iic_mem_nhds hη4)).exists
  have hC := (tendsto_finsetSum (Finset.range (N + 1)) fun n _ => hconv n M).eventually
    (Iic_mem_nhds (by rw [Finset.sum_const_zero]; exact hη4))
  filter_upwards [hC] with ε hε
  calc S.P {ω | δ < |∫ x, f x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω) -
        6 * ∫ x, f x ∂S.μ ω|}
      ≤ S.P ({ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁} ∪ (⋃ n ∈ Finset.range (N + 1), {ω | M < R' n ω}) ∪
        ⋃ n ∈ Finset.range (N + 1), {ω | δ / ((n : ℝ) + 1) <
          |∫ x, truncatedDilation f R₁ M (R' n ω) x ∂degreeWeightedMeasure ((S' n).mult (ε / ((n : ℝ) + 1)) ω)
              (ε / ((n : ℝ) + 1)) ((S' n).η ω) ((S' n).μ ω) -
            6 * ∫ x, truncatedDilation f R₁ M (R' n ω) x ∂(S' n).μ ω|}) :=
        measure_mono_ae (hincl.mono fun ω h hω => h N M ε hω)
    _ ≤ S.P {ω | ∀ n ≤ N, R' n ω ≤ 2 * R₁} + ∑ n ∈ Finset.range (N + 1), S.P {ω | M < R' n ω} +
        ∑ n ∈ Finset.range (N + 1), S.P {ω | δ / ((n : ℝ) + 1) <
          |∫ x, truncatedDilation f R₁ M (R' n ω) x ∂degreeWeightedMeasure ((S' n).mult (ε / ((n : ℝ) + 1)) ω)
              (ε / ((n : ℝ) + 1)) ((S' n).η ω) ((S' n).μ ω) -
            6 * ∫ x, truncatedDilation f R₁ M (R' n ω) x ∂(S' n).μ ω|} :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_biUnion_finset_le _ _))) (measure_biUnion_finset_le _ _))
    _ ≤ η / 2 + η / 2 / 2 + η / 2 / 2 := add_le_add (add_le_add hN hM) hε
    _ = η := by rw [add_assoc, ENNReal.add_halves, ENNReal.add_halves]

end MatedCRT
