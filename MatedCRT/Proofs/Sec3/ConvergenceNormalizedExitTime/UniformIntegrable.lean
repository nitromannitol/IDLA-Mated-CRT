import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellIntegrable
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-!
# Integrability from uniform cell approximations

A uniform approximation on a measurable set by bounded measurable functions
gives integrability against every measure giving that set finite mass. This
allows the Green-kernel convergence to supply measurability and boundedness of
the continuum kernel away from its pole.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls
open scoped ENNReal

/-- Uniform approximation by bounded measurable functions on a measurable
set gives integrability for every measure with finite mass on that set. -/
theorem integrableOn_of_uniform_bounded_measurable_approx
    {α : Type*} [MeasurableSpace α] {K : Set α} (hK : MeasurableSet K)
    {g : α → ℝ}
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ f : α → ℝ, Measurable f ∧
      ∃ C : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C ∧ ‖f x - g x‖ ≤ δ)
    (μ : Measure α) (hμ : μ K < ⊤) : IntegrableOn g K μ := by
  have hg : AEMeasurable g (μ.restrict K) := by
    apply aemeasurable_of_unif_approx
    intro δ hδ
    obtain ⟨f, hf, C, hC⟩ := happrox δ hδ
    refine ⟨f, hf.aemeasurable, ?_⟩
    filter_upwards [ae_restrict_mem hK] with x hx
    simpa only [Real.dist_eq, Real.norm_eq_abs] using (hC x hx).2
  obtain ⟨f, hf, C, hC⟩ := happrox 1 zero_lt_one
  apply IntegrableOn.of_bound hμ hg.aestronglyMeasurable (C + 1)
  filter_upwards [ae_restrict_mem hK] with x hx
  have h := norm_add_le (g x - f x) (f x)
  rw [sub_add_cancel] at h
  have hdiff := (hC x hx).2
  rw [norm_sub_rev] at hdiff
  linarith [(hC x hx).1]

/-- On a bounded set, a rescaled vertex function is almost surely measurable
and bounded, without assuming measurability of its environment-dependent values. -/
theorem MatedCRTEnv.IsValid.ae_measurable_bounded_rescale
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ε : ℝ} (hS : S.IsValid 𝒮 γ) (hε : 0 < ε)
    (K : Set ℂ) (hK : Bornology.IsBounded K) (u : Ω → ℤ → ℝ) :
    ∀ᵐ ω ∂S.P, Measurable (rescale (S.mε ε) ε (S.η ω) (u ω)) ∧
      ∃ C : ℝ, ∀ x ∈ K, ‖rescale (S.mε ε) ε (S.η ω) (u ω) x‖ ≤ C := by
  classical
  obtain ⟨V, hV, hVe⟩ := hS.exists_measurable_vertexOf hε
  filter_upwards [hVe, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hVω harea hp
  have hv : Measurable (fun x => vertexOf ε (S.η ω) x) := by
    have hv' : Measurable (fun x : ℂ => V (ω, x)) :=
      hV.comp (measurable_const.prodMk measurable_id)
    simpa only [hVω] using hv'
  constructor
  · unfold rescale
    exact measurable_const.mul ((measurable_of_countable (u ω)).comp hv)
  · have hfin := Tightness.cellVertices_finite harea.1 hp hε hK
    obtain ⟨C, hC⟩ := (hfin.image (fun a => ‖(S.mε ε)⁻¹ * u ω a‖)).bddAbove
    refine ⟨C, fun x hx => hC ?_⟩
    exact ⟨vertexOf ε (S.η ω) x,
      ⟨x, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x, hx⟩, rfl⟩

/-- Uniform convergence in probability to a deterministic function provides
deterministic bounded measurable approximations on the same set. The failure
events need not be measurable. -/
theorem bounded_measurable_approx_of_uniformInProbability
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set α)
    (F : ℝ → Ω → α → ℝ) (g : α → ℝ)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, Measurable (F ε ω) ∧
      ∃ C : ℝ, ∀ x ∈ K, ‖F ε ω x‖ ≤ C)
    (hconv : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ x ∈ K, δ < ‖F ε ω x - g x‖}) (𝓝[>] 0) (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → ∃ f : α → ℝ, Measurable f ∧
      ∃ C : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C ∧ ‖f x - g x‖ ≤ δ := by
  classical
  intro δ hδ
  have hsmall := ENNReal.tendsto_nhds_zero.1 (hconv δ hδ) (1 / 2) (by norm_num)
  obtain ⟨ε, hε, hεpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  have hlt : P {ω | ∃ x ∈ K, δ < ‖F ε ω x - g x‖} < 1 :=
    hε.trans_lt (by norm_num)
  have hex : ∃ ω, (Measurable (F ε ω) ∧ ∃ C : ℝ, ∀ x ∈ K, ‖F ε ω x‖ ≤ C) ∧
      ∀ x ∈ K, ‖F ε ω x - g x‖ ≤ δ := by
    by_contra hn
    have hall : ∀ᵐ ω ∂P, ∃ x ∈ K, δ < ‖F ε ω x - g x‖ := by
      filter_upwards [hF ε hεpos] with ω hw
      by_contra hbad
      apply hn
      refine ⟨ω, hw, fun x hx => ?_⟩
      exact le_of_not_gt (fun h => hbad ⟨x, hx, h⟩)
    have hle : P univ ≤ P {ω | ∃ x ∈ K, δ < ‖F ε ω x - g x‖} := by
      apply measure_mono_ae
      filter_upwards [hall] with ω hω _
      exact hω
    simp only [measure_univ] at hle
    exact (not_le_of_gt hlt) hle
  obtain ⟨ω, ⟨hm, C, hC⟩, hclose⟩ := hex
  exact ⟨F ε ω, hm, C, fun x hx => ⟨hC x hx, hclose x hx⟩⟩

/-- Lemma 3.3 itself gives integrability of the limiting Green kernel on
sets separated from the pole. No independent continuity theorem for a
non-centered ball is needed for this truncated integral. -/
theorem greenFunction_ae_integrableOn_away_from_pole
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (D : Set ℂ) (hD : D ⊆ closedBall z r \ {y}) (hDρ : D ⊆ ball 0 ρ)
    (hdist : 0 < infDist y D) :
    ∀ᵐ ω ∂S.P, IntegrableOn (fun x => S.c₀ / 6 * greenFunction (ball z r) y x) D (S.μ ω) := by
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let K := closure D
  have hKz : K ⊆ closedBall z r := closure_minimal (hD.trans sdiff_subset) isClosed_closedBall
  have hKρ : K ⊆ closedBall (0 : ℂ) ρ :=
    closure_minimal (hDρ.trans ball_subset_closedBall) isClosed_closedBall
  have hyK : y ∉ K := by
    intro h
    have hz := infDist_zero_of_mem_closure h
    linarith
  have hK : K ⊆ closedBall z r \ {y} := by
    intro x hx
    exact ⟨hKz hx, by simpa only [mem_singleton_iff] using (ne_of_mem_of_not_mem hx hyK)⟩
  have hdistK : 0 < infDist y K := by simpa only [K, infDist_closure] using hdist
  have hbounded : Bornology.IsBounded K := isBounded_closedBall.subset hKz
  let F : ℝ → Ω → ℂ → ℝ := fun ε ω => rescale (S.mε ε) ε (S.η ω)
    (fun a => ε⁻¹ * greenKernel (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) a)
  let g : ℂ → ℝ := fun x => S.c₀ / 6 * greenFunction (ball z r) y x
  have happrox := bounded_measurable_approx_of_uniformInProbability S.P K F g
    (fun ε hε => hS.ae_measurable_bounded_rescale hε K hbounded _)
    (by
      intro δ hδ
      have h := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy δ hδ K hK hdistK
      simpa only [ProbTendsToOne, compl_ofPred, not_forall, not_imp, not_le,
        exists_prop, Real.norm_eq_abs, F, g] using h)
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω harea hp
  have hsub : K ⊆ ball (0 : ℂ) (ρ + 1) := by
    intro x hx
    have hx' := hKρ hx
    rw [mem_closedBall] at hx'
    rw [mem_ball]
    linarith
  have hmass : S.μ ω K < ⊤ :=
    (measure_mono hsub).trans_lt (ball_mass_lt_top_of_proper harea hp 0 (ρ + 1))
  exact (integrableOn_of_uniform_bounded_measurable_approx isClosed_closure.measurableSet
    happrox (S.μ ω) hmass).mono_set subset_closure

end MatedCRT
