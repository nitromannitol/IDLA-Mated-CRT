import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.WeightedCellIntegral

/-! # Integrability for degree-weighted cell measures -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A compactly supported continuous test times a rescaled vertex function
is integrable for the degree-weighted measure. Properness gives finitely many
cells meeting the test support; on each cell the rescaled function is almost
everywhere constant. -/
theorem integrable_mul_rescale_degreeWeightedMeasure
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (t : ℝ) (u : ℤ → ℝ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x => f x * rescale t ε η u x) (degreeWeightedMeasure m ε η μ) := by
  classical
  let F := (Tightness.cellVertices_finite hη.1 hp hε hfc.isCompact.isBounded).toFinset
  let ν : ℤ → Measure ℂ := fun a => ((matedDeg m a : ℕ) : ℝ≥0∞) • μ.restrict (cell ε η a)
  change Integrable (fun x => f x * rescale t ε η u x) (Measure.sum ν)
  apply integrable_sum_measure
  · intro a
    have hcell : IsCompact (cell ε η a) := isCompact_Icc.image hη.1
    have hfi : IntegrableOn f (cell ε η a) μ := hf.continuousOn.integrableOn_compact hcell
    have heq : (fun x => f x * rescale t ε η u x) =ᵐ[μ.restrict (cell ε η a)]
        fun x => f x * (t⁻¹ * u a) := by
      filter_upwards [ae_vertexOf_eq_on_cell hη hp hε a] with x hx
      simp [rescale, hx]
    have hi : IntegrableOn (fun x => f x * rescale t ε η u x) (cell ε η a) μ :=
      (integrable_congr heq).2 (hfi.mul_const _)
    exact hi.smul_measure (by simp)
  · apply summable_of_ne_finset_zero (s := F)
    intro a ha
    have ha' : a ∉ cellVertices ε η (tsupport f) := by simpa [F] using ha
    have hz : (∫ x in cell ε η a, ‖f x * rescale t ε η u x‖ ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hfx : f x = 0 := by
        apply Function.notMem_support.mp
        intro hfmem
        exact ha' ⟨x, hx, subset_tsupport f hfmem⟩
      simp [hfx]
    change (∫ x, ‖f x * rescale t ε η u x‖ ∂ν a) = 0
    rw [show ν a = ((matedDeg m a : ℕ) : ℝ≥0∞) • μ.restrict (cell ε η a) from rfl,
      integral_smul_measure, hz]
    simp

/-- For a continuous compactly supported test, the finite-cell occupation
estimate requires only the geometric covering and oscillation bounds. -/
theorem abs_integral_degreeWeightedMeasure_sub_green_sum_le_of_continuous
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (δ : ℝ) (F : Finset ℤ)
    (hcover : ∀ b ∈ cellVertices ε η (tsupport f), b ∈ F)
    (hdeg : ∀ b ∈ F, matedDeg m b ≠ 0)
    (hosc : ∀ b ∈ F, ∀ x ∈ cell ε η b, |f x - f (vertexPoint ε η b)| ≤ δ) :
    |(∫ x, f x * rescale t ε η (fun b => ε⁻¹ * greenKernel m A a b) x
        ∂degreeWeightedMeasure m ε η μ) -
      ∑ b ∈ F, t⁻¹ * greenFn m A a b * f (vertexPoint ε η b)| ≤
      δ * ∑ b ∈ F, t⁻¹ * greenFn m A a b := by
  apply abs_integral_degreeWeightedMeasure_sub_green_sum_le_of_support hη hp hε ht
    m A a f δ F (integrable_mul_rescale_degreeWeightedMeasure hη hp hε m t _ hf hfc)
    hcover hdeg
  · intro b _
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.image hη.1)
  · exact hosc

/-- A nonnegative cutoff which is at least one on selected vertices bounds
the total Green-function occupation mass of those vertices. -/
theorem green_occupation_mass_le_cutoff_sum (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    {t : ℝ} (ht : 0 ≤ t) (F E : Finset ℤ) (hFE : F ⊆ E) (φ : ℤ → ℝ)
    (hφ : ∀ b ∈ E, 0 ≤ φ b) (hone : ∀ b ∈ F, 1 ≤ φ b) :
    ∑ b ∈ F, t * greenFn m A a b ≤ ∑ b ∈ E, t * greenFn m A a b * φ b := by
  calc
    _ ≤ ∑ b ∈ F, t * greenFn m A a b * φ b := by
      apply Finset.sum_le_sum
      intro b hb
      have hg : 0 ≤ greenFn m A a b := by unfold greenFn; exact ENNReal.toReal_nonneg
      nlinarith [mul_nonneg ht hg, hone b hb]
    _ ≤ ∑ b ∈ E, t * greenFn m A a b * φ b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hFE
      intro b hb _
      exact mul_nonneg (mul_nonneg ht (by unfold greenFn; exact ENNReal.toReal_nonneg)) (hφ b hb)

/-- The cutoff bound also holds with the occupation sum indexed by a finite
set of vertices, in the form used by Green-function integral convergence. -/
theorem green_occupation_mass_le_cutoff_tsum (m : ℤ → ℤ → ℕ) (A C : Set ℤ)
    (hC : C.Finite) (a : ℤ) {t : ℝ} (ht : 0 ≤ t) (F : Finset ℤ)
    (hFC : ∀ b ∈ F, b ∈ C) (φ : ℤ → ℝ)
    (hφ : ∀ b ∈ C, 0 ≤ φ b) (hone : ∀ b ∈ F, 1 ≤ φ b) :
    ∑ b ∈ F, t * greenFn m A a b ≤
      t * ∑' b : C, greenFn m A a b * φ b := by
  classical
  have hFE : F ⊆ hC.toFinset := fun b hb => hC.mem_toFinset.2 (hFC b hb)
  have hsum : (∑' b : C, greenFn m A a b * φ b) =
      ∑ b ∈ hC.toFinset, greenFn m A a b * φ b := by
    rw [tsum_subtype C (fun b => greenFn m A a b * φ b),
      tsum_eq_sum (s := hC.toFinset) ?_]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [Set.indicator_of_mem (hC.mem_toFinset.1 hb)]
    · intro b hb
      exact Set.indicator_of_notMem (fun h => hb (hC.mem_toFinset.2 h)) _
  calc
    _ ≤ ∑ b ∈ hC.toFinset, t * greenFn m A a b * φ b :=
      green_occupation_mass_le_cutoff_sum m A a ht F hC.toFinset hFE φ
        (fun b hb => hφ b (hC.mem_toFinset.1 hb)) hone
    _ = t * ∑' b : C, greenFn m A a b * φ b := by
      rw [hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end MatedCRT.GreenEnvironment
