import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FixedGreenSum
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.GreenMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LaplacianMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Measure

/-! # Measurability of truncated Green sums -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal

/-- At a fixed positive mesh, the normalized Green sum over cells avoiding
the pole ball has a measurable version. -/
theorem MatedCRTEnv.IsValid.exists_measurable_truncatedGreenSum
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (z y : ℂ) (r δ : ℝ) :
    ∃ X : Ω → ℝ, Measurable X ∧ ∀ᵐ ω ∂S.P,
      X ω = (S.mε ε)⁻¹ * ∑ a ∈ truncatedGreenCells ε (S.η ω) z y r δ,
        greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) a := by
  classical
  obtain ⟨V, hV, hVa⟩ := hS.exists_measurable_interiorCellVertices ε (ball z r) (Or.inl isOpen_ball)
  obtain ⟨W, hW, hWa⟩ := hS.exists_measurable_cellVertices_set ε (ball y δ) (Or.inl isOpen_ball)
  obtain ⟨v, hv, hva⟩ := hS.exists_measurable_vertexOf hε
  let A : Ω → ℤ := fun ω => v (ω, y)
  have hA : Measurable A := hv.comp (measurable_id.prodMk measurable_const)
  let f : Ω → ℤ → ℝ := fun ω a =>
    if a ∈ V ω \ W ω then greenKernel (S.mult ε ω) (V ω) (A ω) a else 0
  have hf : ∀ a, Measurable (fun ω => f ω a) := by
    intro a
    have hmem : MeasurableSet {ω | a ∈ V ω \ W ω} := by
      apply measurableSet_setOfPred.mpr
      exact ((measurable_set_mem a).comp hV).and (((measurable_set_mem a).comp hW).not)
    have hg : Measurable (fun ω => greenKernel (S.mult ε ω) (V ω) (A ω) a) :=
      measurable_countable_evaluation A hA
        (fun b ω => greenKernel (S.mult ε ω) (V ω) b a)
        (fun b => hS.measurable_greenKernel ε V hV b a)
    exact Measurable.ite hmem hg measurable_const
  refine ⟨fun ω => (S.mε ε)⁻¹ * ∑ᶠ a, f ω a,
    measurable_const.mul (measurable_finsum_real f hf), ?_⟩
  filter_upwards [hVa, hWa, hva, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
    with ω hvω hwω haω harea hp
  let F := truncatedGreenCells ε (S.η ω) z y r δ
  have hF : (F : Set ℤ) = V ω \ W ω := by
    rw [coe_truncatedGreenCells harea.1 hp hε z y r δ, hvω, hwω]
  have hsum : (∑ᶠ a, f ω a) = ∑ a ∈ F, f ω a := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    by_contra hnot
    apply ha
    have hmem : a ∉ V ω \ W ω := by
      rw [← hF]
      exact hnot
    change (if a ∈ V ω \ W ω then _ else 0) = 0
    rw [ite_eq_right hmem]
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hmem : a ∈ V ω \ W ω := by
    rw [← hF]
    exact ha
  change (if a ∈ V ω \ W ω then greenKernel (S.mult ε ω) (V ω) (A ω) a else 0) = _
  rw [ite_eq_left hmem, hvω]
  change greenKernel (S.mult ε ω) _ (v (ω, y)) a = _
  rw [haω y]

/-- Almost-sure convergence along a further subsequence of every positive mesh
sequence implies convergence in probability, provided each sum has a measurable version. -/
theorem tendstoInProbability_of_ae_subsequences
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℝ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ e, 0 < e → AEMeasurable (X e) P)
    (hsub : ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝[>] 0) →
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P,
        Tendsto (fun n => X (e (ns n)) ω) atTop (𝓝 (Y ω))) :
    TendstoInProbability P X Y := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos : ∀ n, 0 < e n := by intro n; dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall hepos⟩
  obtain ⟨ns, _, hns⟩ := hsub e he
  have hY : AEMeasurable Y P := by
    apply aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun n ω => X (e (ns n)) ω)
    · intro n; exact hX _ (hepos _)
    · exact hns
  intro t ht
  apply tendsto_measure_zero_of_subsequence P (fun e => {ω | t < |X e ω - Y ω|})
  · intro e he'
    exact nullMeasurableSet_lt aemeasurable_const ((hX e he').sub hY).abs
  · intro es hes hzero
    have hes' : Tendsto es atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall hes⟩
    obtain ⟨φ, hφ, hφae⟩ := hsub es hes'
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hφae] with ω hω
    have h := hω.eventually (Metric.ball_mem_nhds (Y ω) ht)
    filter_upwards [h] with n hn
    simp only [not_lt]
    exact le_of_lt (by simpa [Real.dist_eq] using hn)

/-- The normalized Green sum outside a fixed pole ball converges in probability
when the corresponding boundary circle has zero LQG mass almost surely. -/
theorem greenSum_tendstoInProbability_fixed_truncation
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hsmall : δ + dist y z < r)
    (hcircle : ∀ᵐ ω ∂S.P, S.μ ω (sphere y δ) = 0) :
    TendstoInProbability S.P
      (fun e ω => (S.mε e)⁻¹ * ∑ a ∈ truncatedGreenCells e (S.η ω) z y r δ,
        greenKernel (S.mult e ω) (interiorCellVertices e (S.η ω) (ball z r))
          (vertexOf e (S.η ω) y) a)
      (fun ω => ∫ x in ball z r \ ball y δ,
        (S.c₀ / 6) * greenFunction (ball z r) y x ∂S.μ ω) := by
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply tendstoInProbability_of_ae_subsequences
  · intro e he
    obtain ⟨X, hX, hXa⟩ := hS.exists_measurable_truncatedGreenSum he z y r δ
    exact hX.aemeasurable.congr hXa
  · exact greenSum_ae_subsequence_fixed_truncation 𝒮 h33 hγ hγ2 hρ hρ1 S hS
      hr hδ hball hy hsmall hcircle

end MatedCRT
