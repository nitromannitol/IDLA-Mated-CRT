import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.WeightedIntegrability
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCells
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Oscillation of tests on cells meeting their support -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

/-- A continuous compactly supported test has uniformly small oscillation on
all cells meeting its support when the mesh is sufficiently small. -/
theorem exists_small_cells_test_oscillation {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {d : ℝ} (hd : 0 < d) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ a ∈ cellVertices ε η (tsupport f), ∀ x ∈ cell ε η a,
        |f x - f (vertexPoint ε η a)| ≤ d := by
  have hu : UniformContinuous f := hfc.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuous_iff.mp hu d hd
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_ball (0 : ℂ)
  obtain ⟨ε₀, hε₀, hsmall⟩ := cell_diam_small_of_proper hη hp R (δ / 2) (half_pos hδ)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε₀ a ha x hx
  have haR : a ∈ cellVertices ε η (ball 0 R) := by
    obtain ⟨y, hy, hyf⟩ := ha
    exact ⟨y, hy, hR hyf⟩
  have hdist : dist x (vertexPoint ε η a) < δ := by
    have hc : IsCompact (cell ε η a) := isCompact_Icc.image hη
    have hbound := dist_le_diam_of_mem hc.isBounded hx (Tightness.vertexPoint_mem_cell hε a)
    have hdiam := hsmall ε hε hε₀ a haR
    linarith
  have h := huδ hdist
  simpa only [Real.dist_eq] using le_of_lt h

/-- Vertices of cells meeting a bounded set remain in a fixed ball at small scales. -/
theorem exists_vertexPoint_bound_of_bounded {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    ∃ R > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ a ∈ cellVertices ε η K, vertexPoint ε η a ∈ closedBall 0 R := by
  obtain ⟨r, hr⟩ := hK.subset_ball (0 : ℂ)
  obtain ⟨ε₀, hε₀, hsmall⟩ := cell_diam_small_of_proper hη hp r 1 zero_lt_one
  refine ⟨|r| + 2, by positivity, ε₀, hε₀, ?_⟩
  intro ε hε hε₀ a ha
  obtain ⟨x, hx, hxK⟩ := ha
  have ha' : a ∈ cellVertices ε η (ball 0 r) := ⟨x, hx, hr hxK⟩
  have hc : IsCompact (cell ε η a) := isCompact_Icc.image hη
  have hd := dist_le_diam_of_mem hc.isBounded (Tightness.vertexPoint_mem_cell hε a) hx
  have hdiam := hsmall ε hε hε₀ a ha'
  have hx' : dist x 0 < r := hr hxK
  have htri := dist_triangle (vertexPoint ε η a) x 0
  change dist (vertexPoint ε η a) 0 ≤ |r| + 2
  have hrr := le_abs_self r
  linarith

/-- A smooth nonnegative compactly supported function can equal one on a ball. -/
theorem exists_smooth_cutoff_one_on_closedBall (R : ℝ) (hR : 0 < R) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ ∀ x ∈ closedBall 0 R, f x = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun _ => b.nonneg, ?_⟩
  intro x hx
  exact b.one_of_mem_closedBall hx

/-- The finite sum over cells meeting the support equals the occupation sum
on any finite vertex set containing those cells. -/
theorem green_sum_eq_tsum_of_support {η : ℝ → ℂ} {ε t : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (A C : Set ℤ) (a : ℤ)
    (f : ℂ → ℝ) (F : Finset ℤ)
    (hFC : ∀ b ∈ F, b ∈ C)
    (hcover : ∀ b ∈ cellVertices ε η (tsupport f), b ∈ F) :
    ∑ b ∈ F, t * greenFn m A a b * f (vertexPoint ε η b) =
      t * ∑' b : C, greenFn m A a b * f (vertexPoint ε η b) := by
  classical
  rw [tsum_subtype C (fun b => greenFn m A a b * f (vertexPoint ε η b)),
    tsum_eq_sum (s := F) ?_, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Set.indicator_of_mem (hFC b hb)]
    ring
  · intro b hb
    by_cases hbC : b ∈ C
    · rw [Set.indicator_of_mem hbC]
      have hz : f (vertexPoint ε η b) = 0 := by
        apply Function.notMem_support.mp
        intro hv
        exact hb (hcover b ⟨vertexPoint ε η b, Tightness.vertexPoint_mem_cell hε b,
          subset_tsupport f hv⟩)
      simp [hz]
    · exact Set.indicator_of_notMem hbC _

/-- The error between the degree-weighted kernel integral and the occupation
sum is controlled by the test oscillation and a nonnegative cutoff sum. -/
theorem abs_integral_sub_occupation_le_cutoff
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (m : ℤ → ℤ → ℕ) (A C : Set ℤ)
    (hC : C.Finite) (a : ℤ) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 ≤ δ) (F : Finset ℤ)
    (hFC : ∀ b ∈ F, b ∈ C)
    (hcover : ∀ b ∈ cellVertices ε η (tsupport f), b ∈ F)
    (hdeg : ∀ b ∈ F, matedDeg m b ≠ 0)
    (hosc : ∀ b ∈ F, ∀ x ∈ cell ε η b, |f x - f (vertexPoint ε η b)| ≤ δ)
    (φ : ℂ → ℝ) (hφ : ∀ b ∈ C, 0 ≤ φ (vertexPoint ε η b))
    (hone : ∀ b ∈ F, 1 ≤ φ (vertexPoint ε η b)) :
    |(∫ x, f x * rescale t ε η (fun b => ε⁻¹ * greenKernel m A a b) x
        ∂degreeWeightedMeasure m ε η μ) -
      t⁻¹ * ∑' b : C, greenFn m A a b * f (vertexPoint ε η b)| ≤
      δ * (t⁻¹ * ∑' b : C, greenFn m A a b * φ (vertexPoint ε η b)) := by
  rw [← green_sum_eq_tsum_of_support hε m A C a f F hFC hcover]
  calc
    _ ≤ δ * ∑ b ∈ F, t⁻¹ * greenFn m A a b :=
      abs_integral_degreeWeightedMeasure_sub_green_sum_le_of_continuous hη hp hε ht
        m A a hf hfc δ F hcover hdeg hosc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (green_occupation_mass_le_cutoff_tsum m A C hC a (inv_nonneg.mpr ht.le) F hFC
        (fun b => φ (vertexPoint ε η b)) hφ hone) hδ

end MatedCRT.GreenEnvironment
