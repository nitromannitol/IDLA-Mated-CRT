import LatticeProb.Prob.LevyProkhorovOfIntegrals
import MatedCRT.FirstPass.Derived.DegreeMeasureAtomicConvergence

/-!
# The cutoff degree measure converges to `6 ψ μ_h` in the Lévy–Prokhorov distance, in probability

For the `ε`-mated-CRT map of a valid environment, a continuous compactly supported cutoff `ψ ≥ 0`
and the vertex positions `v_k = η'(εk)` of a continuous version `η'` of the space-filling curve, the
cutoff degree measure `ν^ε = Σ_{k : v_k ∈ supp ψ} ε deg^ε(k) ψ(v_k) δ_{v_k}` (`degreeCutoffMeasure`)
converges to the finite measure `6 ψ μ_h` (density `6 ψ` against the `γ`-LQG measure `μ_h`) in the
Lévy–Prokhorov distance, in probability, along every sequence `ε_n → 0⁺`.

Both measures are carried by the compact set `supp ψ`, and `∫ g dν^ε → 6 ∫ g ψ dμ_h` in probability
for every continuous `g` (`tendstoInProbability_integral_degreeCutoffMeasure`), so the
Lévy–Prokhorov convergence follows from `LatticeProb.tendstoInMeasure_levyProkhorovDist_of_forall_integral`
(finitely many test functions control the distance of measures carried by a compact set). No
measurability of the random measures in `ω` and no subsequence argument is used.

* `degreeCutoffMeasure_apply_compl_tsupport`: every atom of `ν^ε` lies in `supp ψ`;
* `withDensity_ofReal_mul_apply_compl_tsupport`, `integral_withDensity_ofReal_mul`: the measure
  `c ψ μ` is carried by `supp ψ`, and `∫ g d(c ψ μ) = c ∫ g ψ dμ`;
* `tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_of_integral`: the Lévy–Prokhorov
  convergence to any random finite measure `μ₀` carried almost surely by `supp ψ` with
  `∫ g dμ₀ = 6 ∫ g ψ dμ_h` almost surely;
* `tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure`: the same for `μ₀ = 6 ψ μ_h` almost
  surely;
* `tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_projection`: the same for a projection
  `π (D n)` equal almost surely to `6 ψ μ_h`, the hypothesis `hμπ` of
  `LatticeProb.tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist`.
-/

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The cutoff degree measure is carried by `supp ψ`**: every atom `v_k` of
`Σ_{k : v_k ∈ supp ψ} ε deg(k) ψ(v_k) δ_{v_k}` lies in `tsupport ψ`. -/
theorem degreeCutoffMeasure_apply_compl_tsupport (m : ℤ → ℤ → ℕ) (ε : ℝ) (v : ℤ → ℂ)
    (ψ : ℂ → ℝ) : (degreeCutoffMeasure m ε v ψ : Measure ℂ) (tsupport ψ)ᶜ = 0 := by
  have hmem : ∀ x ∈ vertexWindow v (tsupport ψ), v x ∈ tsupport ψ := by
    intro x hx
    by_cases h : (v ⁻¹' tsupport ψ).Finite
    · exact (mem_vertexWindow h).1 hx
    · simp [vertexWindow, h] at hx
  show LatticeProb.atomicMeasure (vertexWindow v (tsupport ψ)) (degreeCutoffWeight m ε v ψ) v
    (tsupport ψ)ᶜ = 0
  rw [LatticeProb.atomicMeasure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (isClosed_tsupport ψ).isOpen_compl.measurableSet,
    indicator_of_notMem (show v x ∉ (tsupport ψ)ᶜ from fun h => h (hmem x hx)), mul_zero]

/-- The measure `c ψ μ` with density `c ψ` against `μ` is carried by `supp ψ`. -/
theorem withDensity_ofReal_mul_apply_compl_tsupport (μ : Measure ℂ) {ψ : ℂ → ℝ} (c : ℝ) :
    (μ.withDensity fun z => ENNReal.ofReal (c * ψ z)) (tsupport ψ)ᶜ = 0 := by
  have hs : MeasurableSet (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl.measurableSet
  have h0 : ∀ z ∈ (tsupport ψ)ᶜ, ENNReal.ofReal (c * ψ z) = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, ENNReal.ofReal_zero]
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs h0, lintegral_zero]

/-- For a continuous `ψ ≥ 0` and `c ≥ 0`, `∫ g d(c ψ μ) = c ∫ g ψ dμ`. -/
theorem integral_withDensity_ofReal_mul (μ : Measure ℂ) {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ z, 0 ≤ ψ z) {c : ℝ} (hc : 0 ≤ c) (g : ℂ → ℝ) :
    ∫ x, g x ∂(μ.withDensity fun z => ENNReal.ofReal (c * ψ z)) = c * ∫ x, g x * ψ x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (hψ.measurable.const_mul c).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg hc (hψ0 z))]
  ring

/-- **Lévy–Prokhorov convergence of the cutoff degree measure, in probability.** In a valid
environment satisfying Lemma 2.10 (`hD27`), with the cell diameters near every ball tending to `0`
in probability, let `ε_n → 0⁺` and let `μ₀` be a random finite measure carried almost surely by
`supp ψ` with `∫ g dμ₀ = 6 ∫ g ψ dμ_h` almost surely for every continuous `g`. Then the
Lévy–Prokhorov distance between the cutoff degree measure `ν^{ε_n}` and `μ₀` tends to `0` in
probability. -/
theorem tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_of_integral
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hD27 : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → TendstoInProbability S.P
      (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun ε => S.P {ω | ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R}) (𝓝[>] 0) (𝓝 0))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝[>] 0)) {μ₀ : Ω → FiniteMeasure ℂ}
    (hsupp₀ : ∀ᵐ ω ∂S.P, (μ₀ ω : Measure ℂ) (tsupport ψ)ᶜ = 0)
    (hμ₀ : ∀ᵐ ω ∂S.P, ∀ g : ℂ → ℝ, Continuous g →
      ∫ x, g x ∂(μ₀ ω : Measure ℂ) = 6 * ∫ x, g x * ψ x ∂S.μ ω) :
    TendstoInMeasure S.P (fun n ω => levyProkhorovDist
      (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ : Measure ℂ)
      (μ₀ ω : Measure ℂ)) atTop 0 := by
  classical
  -- `μ₀` modified on the null set where it charges `(supp ψ)ᶜ`
  obtain ⟨μ₁, hsupp₁, hμ₁⟩ : ∃ μ₁ : Ω → FiniteMeasure ℂ,
      (∀ ω, (μ₁ ω : Measure ℂ) (tsupport ψ)ᶜ = 0) ∧ ∀ᵐ ω ∂S.P, μ₁ ω = μ₀ ω :=
    ⟨fun ω => if (μ₀ ω : Measure ℂ) (tsupport ψ)ᶜ = 0 then μ₀ ω else 0,
      fun ω => by by_cases h : (μ₀ ω : Measure ℂ) (tsupport ψ)ᶜ = 0 <;> simp [h],
      by filter_upwards [hsupp₀] with ω h; simp [h]⟩
  have hint : ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x ∧ g x ≤ 1) → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => S.P {ω | δ < |∫ x, g x ∂(degreeCutoffMeasure (S.mult (ε n) ω) (ε n)
        (vertexPoint (ε n) ⇑(η' ω)) ψ : Measure ℂ) - ∫ x, g x ∂(μ₁ ω : Measure ℂ)|}) atTop
        (𝓝 0) := by
    intro g hg _ δ hδ
    have H : Tendsto (fun n => S.P {ω | δ < |∫ x, g x ∂(degreeCutoffMeasure (S.mult (ε n) ω)
        (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ : Measure ℂ) - 6 * ∫ x, g x * ψ x ∂S.μ ω|}) atTop
        (𝓝 0) :=
      (tendstoInProbability_integral_degreeCutoffMeasure hγ hγ2 hS hD27 hae hψ hψc hψ0 hdiam hg δ
        hδ).comp hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds H (fun _ => zero_le)
      fun n => measure_mono_ae ?_
    filter_upwards [hμ₁, hμ₀] with ω h1 h2 hlt
    have e : ∫ x, g x ∂(μ₁ ω : Measure ℂ) = 6 * ∫ x, g x * ψ x ∂S.μ ω := by
      rw [h1]
      exact h2 g hg
    rw [e] at hlt
    exact hlt
  refine (LatticeProb.tendstoInMeasure_levyProkhorovDist_of_forall_integral hψc.isCompact
    (μ := fun n ω => degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ)
    (μ₀ := μ₁) (fun n ω => degreeCutoffMeasure_apply_compl_tsupport _ _ _ ψ) hsupp₁
    hint).congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
  filter_upwards [hμ₁] with ω h
  simp only [h]

/-- **The cutoff degree measure converges to `6 ψ μ_h` in the Lévy–Prokhorov distance, in
probability.** Under the hypotheses of
`tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_of_integral`, for every random finite
measure `μ₀` equal almost surely to `6 ψ μ_h` (density `6 ψ` against the LQG measure `μ_h`), the
Lévy–Prokhorov distance between `ν^{ε_n}` and `μ₀` tends to `0` in probability as `ε_n → 0⁺`. -/
theorem tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hD27 : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → TendstoInProbability S.P
      (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun ε => S.P {ω | ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R}) (𝓝[>] 0) (𝓝 0))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝[>] 0)) {μ₀ : Ω → FiniteMeasure ℂ}
    (hμ₀ : ∀ᵐ ω ∂S.P,
      (μ₀ ω : Measure ℂ) = (S.μ ω).withDensity fun z => ENNReal.ofReal (6 * ψ z)) :
    TendstoInMeasure S.P (fun n ω => levyProkhorovDist
      (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ : Measure ℂ)
      (μ₀ ω : Measure ℂ)) atTop 0 := by
  refine tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_of_integral hγ hγ2 hS hD27 hae hψ
    hψc hψ0 hdiam hε ?_ ?_
  · filter_upwards [hμ₀] with ω h
    rw [h]
    exact withDensity_ofReal_mul_apply_compl_tsupport _ 6
  · filter_upwards [hμ₀] with ω h g _
    rw [h]
    exact integral_withDensity_ofReal_mul _ hψ hψ0 (by norm_num) g

/-- **Projection form.** If the projection `π (D n ω)` of a random state `D n` is almost surely
equal to `6 ψ μ_h` for every `n`, then the Lévy–Prokhorov distance between `ν^{ε_n}` and
`π (D n)` tends to `0` in probability: the hypothesis `hμπ` of
`LatticeProb.tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist`. -/
theorem tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_projection
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hD27 : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → TendstoInProbability S.P
      (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun ε => S.P {ω | ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R}) (𝓝[>] 0) (𝓝 0))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝[>] 0)) {X : Type*} {D : ℕ → Ω → X}
    {π : X → FiniteMeasure ℂ}
    (hπD : ∀ n, ∀ᵐ ω ∂S.P,
      (π (D n ω) : Measure ℂ) = (S.μ ω).withDensity fun z => ENNReal.ofReal (6 * ψ z)) :
    TendstoInMeasure S.P (fun n ω => levyProkhorovDist
      (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ : Measure ℂ)
      (π (D n ω) : Measure ℂ)) atTop 0 := by
  refine (tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure (μ₀ := fun ω => π (D 0 ω)) hγ
    hγ2 hS hD27 hae hψ hψc hψ0 hdiam hε (hπD 0)).congr' (Eventually.of_forall fun n => ?_)
    EventuallyEq.rfl
  filter_upwards [hπD 0, hπD n] with ω h0 hn
  simp only [h0, hn]

end MatedCRT.FirstPass.Derived
