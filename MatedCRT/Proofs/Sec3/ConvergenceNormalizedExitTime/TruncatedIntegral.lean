import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BoundaryShell
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AwayFromPole

/-! # Integrals over the omitted part of the truncated cell union -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- An integrable function has small integral on subsets of its domain with
small measure. -/
theorem exists_small_setIntegral_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {D : Set α} {f : α → ℝ} (hf : IntegrableOn f D μ)
    {t : ℝ} (ht : 0 < t) :
    ∃ τ : ℝ≥0∞, 0 < τ ∧ ∀ A ⊆ D, μ A < τ → |∫ x in A, f x ∂μ| < t := by
  obtain ⟨τ, hτ, hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (μ := μ.restrict D) (f := fun x => ‖f x‖ₑ) hf.hasFiniteIntegral.ne
    (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
  refine ⟨τ, hτ, ?_⟩
  intro A hAD hA
  have hmass : (μ.restrict D) A < τ := lt_of_le_of_lt (Measure.restrict_le_self A) hA
  have hlin := hsmall A hmass
  have hint : ‖∫ x in A, f x ∂(μ.restrict D)‖ₑ < ENNReal.ofReal t :=
    lt_of_le_of_lt (enorm_integral_le_lintegral_enorm f) hlin
  rw [Measure.restrict_restrict_of_subset hAD] at hint
  rw [Real.enorm_eq_ofReal_abs] at hint
  exact (ENNReal.ofReal_lt_ofReal_iff ht).1 hint

/-- For an integrable continuum function, the integral over the part omitted
by the truncated cell union can be made small uniformly in the mesh. -/
theorem exists_truncation_small_integral_discrepancy {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r : ℝ) {f : ℂ → ℝ} (hf : IntegrableOn f (ball z r) μ)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∃ δ d : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
      (∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) →
      |∫ x in (ball z r \ ball y δ) \
        fillCells ε η (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)),
        f x ∂μ| < t := by
  obtain ⟨τ, hτ, hsmall⟩ := exists_small_setIntegral_of_integrableOn hf ht
  obtain ⟨δ, d, hδ, hδρ, hd, hmass⟩ :=
    exists_truncation_small_discrepancy hη hp z y r hρ hτ
  refine ⟨δ, d, hδ, hδρ, hd, ?_⟩
  intro ε hε hdiam
  apply hsmall
  · exact sdiff_subset.trans sdiff_subset
  · exact hmass ε hε hdiam

/-- The integral of a fixed integrable continuum function over the truncated
cell union approximates its integral over the punctured ball. -/
theorem exists_truncation_approx_integral {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r : ℝ) {f : ℂ → ℝ} (hf : IntegrableOn f (ball z r) μ)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∃ δ d : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
      (∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) →
      |(∫ x in ball z r \ ball y δ, f x ∂μ) -
        ∫ x in fillCells ε η
          (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ)), f x ∂μ| < t := by
  obtain ⟨δ, d, hδ, hδρ, hd, hsmall⟩ :=
    exists_truncation_small_integral_discrepancy hη hp z y r hf hρ ht
  refine ⟨δ, d, hδ, hδρ, hd, ?_⟩
  intro ε hε hdiam
  have hfill : MeasurableSet (fillCells ε η
      (interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ))) := by
    unfold fillCells
    exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
      (isCompact_Icc.image hη.1).isClosed.measurableSet
  have hsubset := fill_truncated_cells_subset (ε := ε) (r := r) (δ := δ)
    (z := z) (y := y) hη.1
  rw [← setIntegral_sdiff hfill (hf.mono_set sdiff_subset) hsubset]
  exact hsmall ε hε hdiam

/-- The normalized vertex sum differs from the punctured continuum integral
by at most the uniform error on the cell union times its mass, plus an
arbitrarily small truncation error. -/
theorem exists_truncation_approx_vertex_sum {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z y : ℂ) (r : ℝ) {f : ℂ → ℝ} (hf : IntegrableOn f (ball z r) μ)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∃ δ d : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < d ∧
      ∀ (ε : ℝ), 0 < ε →
      (∀ a ∈ cellVertices ε η (ball z r), diam (cell ε η a) ≤ d) →
      ∀ (F : Finset ℤ), (F : Set ℤ) =
        interiorCellVertices ε η (ball z r) \ cellVertices ε η (ball y δ) →
      ∀ (m : ℝ) (u : ℤ → ℝ) (κ : ℝ),
      (∀ x ∈ fillCells ε η (F : Set ℤ),
        |rescale m ε η (fun a => ε⁻¹ * u a) x - f x| ≤ κ) →
      |m⁻¹ * ∑ a ∈ F, u a - ∫ x in ball z r \ ball y δ, f x ∂μ| ≤
        κ * μ.real (fillCells ε η (F : Set ℤ)) + t := by
  obtain ⟨δ, d, hδ, hδρ, hd, hsmall⟩ :=
    exists_truncation_approx_integral hη hp z y r hf hρ ht
  refine ⟨δ, d, hδ, hδρ, hd, ?_⟩
  intro ε hε hdiam F hF m u κ hbound
  have hset : (⋃ a ∈ F, cell ε η a) = fillCells ε η (F : Set ℤ) := by
    simp only [fillCells, Finset.mem_coe]
  have hsubset : fillCells ε η (F : Set ℤ) ⊆ ball z r \ ball y δ := by
    rw [hF]
    exact fill_truncated_cells_subset hη.1
  have hfin : μ (fillCells ε η (F : Set ℤ)) < ⊤ :=
    (measure_mono (hsubset.trans sdiff_subset)).trans_lt (ball_mass_lt_top_of_proper hη hp z r)
  have hrescale : IntegrableOn (rescale m ε η (fun a => ε⁻¹ * u a))
      (fillCells ε η (F : Set ℤ)) μ := by
    rw [← hset]
    exact integrableOn_finset_iUnion.2 (fun a _ => integrableOn_rescale_cell hη hp hε a m _)
  have hfixed : IntegrableOn f (fillCells ε η (F : Set ℤ)) μ :=
    hf.mono_set (hsubset.trans sdiff_subset)
  have hbound' := abs_setIntegral_sub_le_of_uniform_bound hfin hrescale hfixed hbound
  have hsmall' := hsmall ε hε hdiam
  rw [← hF] at hsmall'
  have hidentity := setIntegral_rescale_inv_epsilon_finset_cells hη hp hε F m u
  rw [hset] at hidentity
  rw [← hidentity]
  calc
    _ ≤ |(∫ x in fillCells ε η (F : Set ℤ),
          rescale m ε η (fun a => ε⁻¹ * u a) x ∂μ) -
        ∫ x in fillCells ε η (F : Set ℤ), f x ∂μ| +
        |(∫ x in fillCells ε η (F : Set ℤ), f x ∂μ) -
          ∫ x in ball z r \ ball y δ, f x ∂μ| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hbound' (le_of_lt (by simpa [abs_sub_comm] using hsmall'))

end MatedCRT
