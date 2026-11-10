import MatedCRT.FirstPass.S2h.CertBack
import MatedCRT.FirstPass.S1c.TestDense

/-!
# Density of the Laplacian identity of a certificate (fp-S2h, z1; CHATGPT-cone-good-set.md Section 3.1)

The moment identity `∫ W Δ D_k = ∫_A D_k dν` is known on a family `D_k` of nonnegative test functions which approximates
every nonnegative test function on `B_{3/4}`, together with its Laplacian, uniformly on `B̄_{3/4}`
(`exists_dense_nonnegTest_family`). For a witness `W` continuous on `B̄_{3/4}` and vanishing outside it, the identity then
holds for every nonnegative test function (Armitage-Gardiner, distributional Laplacian; `ν` is finite on `B̄_{3/4}`).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- A real number bounded by `ε K` for every `ε > 0` (with `K ≥ 0`) vanishes. -/
theorem eq_of_forall_pos_le_mul {a b K : ℝ} (hK : 0 ≤ K) (h : ∀ ε : ℝ, 0 < ε → |a - b| ≤ ε * K) : a = b := by
  by_contra hab
  have hpos : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hε : 0 < |a - b| / (2 * (K + 1)) := by positivity
  have h1 := h _ hε
  have h2 : |a - b| / (2 * (K + 1)) * K ≤ |a - b| / (2 * (K + 1)) * (K + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  have h3 : |a - b| / (2 * (K + 1)) * (K + 1) = |a - b| / 2 := by
    field_simp
  linarith

/-- **The Laplacian identity on all nonnegative test functions (fp-S2h, z1).** -/
theorem lap_identity_nonneg {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] {W : ℂ → ℝ}
    (hW : ContinuousOn W (closedBall (0 : ℂ) (3 / 4))) (hW0 : ∀ x, x ∉ closedBall (0 : ℂ) (3 / 4) → W x = 0)
    {A : Set ℂ} (hAm : MeasurableSet A) (hA : A ⊆ closedBall (0 : ℂ) (3 / 4))
    {D : ℕ → ℂ → ℝ} (hDmem : ∀ k, D k ∈ nonnegTest (3 / 4))
    (hdense : ∀ φ ∈ nonnegTest (3 / 4), ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) (3 / 4),
      |φ x - D k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (D k) x| < ε)
    (hid : ∀ k, ∫ x, W x * Laplacian.laplacian (D k) x = ∫ x, D k x ∂(ν.restrict A))
    {φ : ℂ → ℝ} (hφ : φ ∈ nonnegTest (3 / 4)) :
    ∫ x, W x * Laplacian.laplacian φ x = ∫ x, φ x ∂(ν.restrict A) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (3 / 4)).exists_bound_of_continuousOn hW
  have hM' : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), |W x| ≤ max M 0 := fun x hx => by
    have := hM x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hMnn : 0 ≤ max M 0 := le_max_right _ _
  have hfinA : ν A < ⊤ := lt_of_le_of_lt (measure_mono hA) (isCompact_closedBall (0 : ℂ) (3 / 4)).measure_lt_top
  have : IsFiniteMeasure (ν.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinA⟩
  have hKnn : 0 ≤ max M 0 * (volume (closedBall (0 : ℂ) (3 / 4))).toReal + (ν.restrict A univ).toReal :=
    add_nonneg (mul_nonneg hMnn ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  apply eq_of_forall_pos_le_mul hKnn
  intro ε hε
  obtain ⟨k, hk⟩ := hdense φ hφ ε hε
  -- (i) the Laplacian pairings of `φ` and `D k` differ by `max M 0 * ε * vol(B̄_{3/4})`
  have hi : |(∫ x, W x * Laplacian.laplacian φ x) - ∫ x, W x * Laplacian.laplacian (D k) x| ≤
      max M 0 * ε * (volume (closedBall (0 : ℂ) (3 / 4))).toReal := by
    rw [← integral_sub (integrable_mul_laplacian_of_contOn hW hφ.1)
      (integrable_mul_laplacian_of_contOn hW (hDmem k).1)]
    have hg : ∀ x, W x * Laplacian.laplacian φ x - W x * Laplacian.laplacian (D k) x =
        W x * (Laplacian.laplacian φ x - Laplacian.laplacian (D k) x) := fun x => (mul_sub _ _ _).symm
    simp only [hg]
    have hzero : ∫ x, W x * (Laplacian.laplacian φ x - Laplacian.laplacian (D k) x) =
        ∫ x in closedBall (0 : ℂ) (3 / 4), W x * (Laplacian.laplacian φ x - Laplacian.laplacian (D k) x) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hW0 x hx]).symm
    rw [hzero, ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun x hx => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM' x hx) (hk x hx).2.le (abs_nonneg _) hMnn
  -- (iii) the two measures `D k` and `φ` on `A` differ by `ε ν(A)`
  have hiii : |(∫ x, D k x ∂(ν.restrict A)) - ∫ x, φ x ∂(ν.restrict A)| ≤ ε * (ν.restrict A univ).toReal := by
    have hcont : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → Integrable f (ν.restrict A) :=
      fun f hf hc => hf.integrable_of_hasCompactSupport hc
    rw [← integral_sub (hcont (D k) (hDmem k).1.1.continuous (hDmem k).1.2.1)
      (hcont φ hφ.1.1.continuous hφ.1.2.1), ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [ae_restrict_mem hAm] with x hx
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hk x (hA hx)).1.le
  calc |(∫ x, W x * Laplacian.laplacian φ x) - ∫ x, φ x ∂(ν.restrict A)|
      ≤ |(∫ x, W x * Laplacian.laplacian φ x) - ∫ x, W x * Laplacian.laplacian (D k) x| +
          |(∫ x, W x * Laplacian.laplacian (D k) x) - ∫ x, φ x ∂(ν.restrict A)| := abs_sub_le _ _ _
    _ ≤ max M 0 * ε * (volume (closedBall (0 : ℂ) (3 / 4))).toReal + ε * (ν.restrict A univ).toReal := by
        refine add_le_add hi ?_
        rw [hid k]
        exact hiii
    _ = ε * (max M 0 * (volume (closedBall (0 : ℂ) (3 / 4))).toReal + (ν.restrict A univ).toReal) := by ring

end MatedCRT
