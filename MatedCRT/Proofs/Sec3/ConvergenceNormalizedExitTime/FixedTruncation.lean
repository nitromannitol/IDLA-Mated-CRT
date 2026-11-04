import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.TruncatedIntegral
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCells

/-! # Fixed-radius truncation of the cell union -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- The outer shells of a pole ball shrink to its boundary circle. When that
circle has zero mass, the shell masses converge to zero. -/
theorem tendsto_measure_outside_ball_shell {μ : Measure ℂ} {y : ℂ} {δ : ℝ}
    (hfinite : μ (closedBall y (δ + 1)) ≠ ∞) (hcircle : μ (sphere y δ) = 0) :
    Tendsto (fun n : ℕ => μ (closedBall y (δ + 1 / ((n : ℝ) + 1)) \ ball y δ))
      atTop (𝓝 0) := by
  let s : ℕ → Set ℂ := fun n => closedBall y (δ + 1 / ((n : ℝ) + 1)) \ ball y δ
  have hs : Antitone s := by
    intro m n hmn
    apply sdiff_subset_sdiff ?_ Subset.rfl
    apply closedBall_subset_closedBall
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have hinter : ⋂ n, s n = sphere y δ := by
    ext w
    simp only [mem_iInter, s, Set.mem_sdiff, mem_closedBall, mem_ball, mem_sphere]
    constructor
    · intro hw
      have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hc : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
      have hlim : Tendsto (fun n : ℕ => δ + 1 / ((n : ℝ) + 1)) atTop (𝓝 δ) := by
        simpa using hc.add hzero
      have hle : dist w y ≤ δ := ge_of_tendsto' hlim fun n => (hw n).1
      exact le_antisymm hle (not_lt.1 (hw 0).2)
    · intro hw n
      rw [hw]
      constructor
      · have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
      · exact lt_irrefl _
  have hf : ∃ n, μ (s n) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top hfinite (measure_mono ?_)⟩
    simp [s]
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := s)
    (fun _ => (measurableSet_closedBall.diff measurableSet_ball).nullMeasurableSet) hs hf
  rw [hinter, hcircle] at h
  change Tendsto (fun n => μ (s n)) atTop (𝓝 0) at h
  exact h

/-- At a fixed radius with null boundary circle, the omitted mass is small
whenever cells meeting the outer ball are sufficiently small. -/
theorem exists_fixed_truncation_small_discrepancy {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r δ : ℝ) (hcircle : μ (sphere y δ) = 0) {τ : ℝ≥0∞} (hτ : 0 < τ) :
    ∃ d : ℝ, 0 < d ∧ ∀ ε : ℝ, 0 < ε →
      (∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) →
      μ ((ball z r \ ball y δ) \
        fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ))) < τ := by
  have ho := tendsto_measure_inside_ball_shell (ball_mass_lt_top_of_proper hη hp z r).ne
  have hfinite : μ (closedBall y (δ + 1)) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (closedBall_subset_ball (by linarith))).trans_lt
      (ball_mass_lt_top_of_proper hη hp y (δ + 2))
  have hi := tendsto_measure_outside_ball_shell hfinite hcircle
  have hsum : Tendsto (fun n : ℕ =>
      μ (ball z r \ ball z (r - 1 / ((n : ℝ) + 1))) +
      μ (closedBall y (δ + 1 / ((n : ℝ) + 1)) \ ball y δ)) atTop (𝓝 0) := by
    simpa using ho.add hi
  obtain ⟨n, hn⟩ := (hsum.eventually (Iio_mem_nhds hτ)).exists
  let d : ℝ := 1 / ((n : ℝ) + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, ?_⟩
  intro ε hε hsmall
  apply lt_of_le_of_lt _ hn
  exact (measure_mono (punctured_ball_sdiff_fill_subset_shells hη.1 hη.2.2.1 hε hd.le hsmall)).trans
    (measure_union_le _ _)

/-- For a fixed radius with null boundary circle, integration over the
truncated cell union converges to integration over the punctured ball. The
integrand need only be integrable away from the pole. -/
theorem tendsto_integral_fixed_truncated_cells {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r δ : ℝ) (hcircle : μ (sphere y δ) = 0) {f : ℂ → ℝ}
    (hf : IntegrableOn f (ball z r \ ball y δ) μ) :
    Tendsto (fun ε : ℝ => ∫ x in fillCells ε η
      (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)), f x ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x in ball z r \ ball y δ, f x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro t ht
  obtain ⟨τ, hτ, hsmall⟩ := exists_small_setIntegral_of_integrableOn hf ht
  obtain ⟨d, hd, hmass⟩ := exists_fixed_truncation_small_discrepancy hη hp z y r δ hcircle hτ
  obtain ⟨R, hR⟩ := (isBounded_ball : Bornology.IsBounded (ball z r)).subset_ball (0 : ℂ)
  obtain ⟨ε₀, hε₀, hdiam⟩ := cell_diam_small_of_proper hη.1 hp R d hd
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ε₀ := nhdsWithin_le_nhds (Iio_mem_nhds hε₀)
  filter_upwards [self_mem_nhdsWithin, heps] with ε hε hεsmall
  have hdiam' : ∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d := by
    intro a ha
    obtain ⟨w, hw, hwball⟩ := ha
    exact hdiam ε hε hεsmall a ⟨w, hw, hR hwball⟩
  have hfill : MeasurableSet (fillCells ε η
      (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ))) := by
    unfold fillCells
    exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
      (isCompact_Icc.image hη.1).isClosed.measurableSet
  have hsubset := fill_truncated_cells_subset (ε := ε) (r := r) (δ := δ)
    (z := z) (y := y) hη.1
  have hint := hsmall _ sdiff_subset (hmass ε hε hdiam')
  rw [setIntegral_sdiff hfill hf hsubset] at hint
  simpa only [Real.dist_eq, abs_sub_comm] using hint

/-- Uniform convergence of rescaled vertex functions on the punctured ball
identifies the limit of their truncated vertex sums. -/
theorem tendsto_fixed_truncated_vertex_sum {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r δ : ℝ) (hcircle : μ (sphere y δ) = 0) {f : ℂ → ℝ}
    (hf : IntegrableOn f (ball z r \ ball y δ) μ)
    (l : Filter ℝ) (hl : l ≤ 𝓝[>] (0 : ℝ))
    (F : ℝ → Finset ℤ) (m : ℝ → ℝ) (u : ℝ → ℤ → ℝ)
    (hF : ∀ᶠ ε in l, (F ε : Set ℤ) =
      interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ))
    (hconv : TendstoUniformlyOn
      (fun ε => rescale (m ε) ε η (fun a => ε⁻¹ * u ε a)) f l
      (ball z r \ ball y δ)) :
    Tendsto (fun ε : ℝ => (m ε)⁻¹ * ∑ a ∈ F ε, u ε a) l
      (𝓝 (∫ x in ball z r \ ball y δ, f x ∂μ)) := by
  have hDfin : μ (ball z r \ ball y δ) < ⊤ :=
    (measure_mono sdiff_subset).trans_lt (ball_mass_lt_top_of_proper hη hp z r)
  have hfillconv := (tendsto_integral_fixed_truncated_cells hη hp z y r δ hcircle hf).mono_left hl
  rw [Metric.tendsto_nhds]
  intro t ht
  obtain ⟨κ, hκ, hκmass⟩ := exists_pos_mul_lt (half_pos ht) (μ.real (ball z r \ ball y δ))
  have hκmass' : κ * μ.real (ball z r \ ball y δ) < t / 2 := by
    simpa [mul_comm] using hκmass
  have hconv' := (Metric.tendstoUniformlyOn_iff.1 hconv) κ hκ
  have hfillconv' := (Metric.tendsto_nhds.1 hfillconv) (t / 2) (half_pos ht)
  have hpos : ∀ᶠ ε : ℝ in l, 0 < ε := hl self_mem_nhdsWithin
  filter_upwards [hpos, hF, hconv', hfillconv'] with ε hε hFε hconvε hfillε
  have hset : (⋃ a ∈ F ε, cell ε η a) = fillCells ε η (F ε : Set ℤ) := by
    simp only [fillCells, Finset.mem_coe]
  have hsub : fillCells ε η (F ε : Set ℤ) ⊆ ball z r \ ball y δ := by
    rw [hFε]
    exact fill_truncated_cells_subset hη.1
  have hfin : μ (fillCells ε η (F ε : Set ℤ)) < ⊤ := (measure_mono hsub).trans_lt hDfin
  have hrescale : IntegrableOn (rescale (m ε) ε η (fun a => ε⁻¹ * u ε a))
      (fillCells ε η (F ε : Set ℤ)) μ := by
    rw [← hset]
    exact integrableOn_finset_iUnion.2 (fun a _ => integrableOn_rescale_cell hη hp hε a (m ε) _)
  have hbound : ∀ x ∈ fillCells ε η (F ε : Set ℤ),
      |rescale (m ε) ε η (fun a => ε⁻¹ * u ε a) x - f x| ≤ κ := by
    intro x hx
    have h := hconvε x (hsub hx)
    simpa only [Real.dist_eq, abs_sub_comm] using h.le
  have herr := abs_setIntegral_sub_le_of_uniform_bound hfin hrescale (hf.mono_set hsub) hbound
  have hmass : μ.real (fillCells ε η (F ε : Set ℤ)) ≤ μ.real (ball z r \ ball y δ) :=
    measureReal_mono hsub hDfin.ne
  have hidentity := setIntegral_rescale_inv_epsilon_finset_cells hη hp hε (F ε) (m ε) (u ε)
  rw [hset] at hidentity
  have herr' : |(m ε)⁻¹ * ∑ a ∈ F ε, u ε a -
      ∫ x in fillCells ε η (F ε : Set ℤ), f x ∂μ| < t / 2 := by
    rw [← hidentity]
    exact lt_of_le_of_lt (herr.trans (mul_le_mul_of_nonneg_left hmass hκ.le)) hκmass'
  rw [hFε] at herr'
  rw [Real.dist_eq] at hfillε ⊢
  have htriangle := abs_sub_le ((m ε)⁻¹ * ∑ a ∈ F ε, u ε a)
    (∫ x in fillCells ε η (F ε : Set ℤ), f x ∂μ)
    (∫ x in ball z r \ ball y δ, f x ∂μ)
  rw [hFε] at htriangle
  linarith

end MatedCRT
