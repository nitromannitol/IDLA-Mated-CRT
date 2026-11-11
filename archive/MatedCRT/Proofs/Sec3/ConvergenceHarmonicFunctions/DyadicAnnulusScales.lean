import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Choosing nested dyadic annulus scales -/

namespace MatedCRT

/-- Choose finitely many nested dyadic radii between a positive cutoff and
an outer distance. The number of scales is large enough for the polynomial
survival estimate and the smallest radius is exactly the cutoff. -/
theorem exists_dyadic_annulus_scales {cutoff distance : ℝ}
    (hc : 0 < cutoff) (hd : cutoff ≤ distance) :
    ∃ (n : ℕ) (r : ℕ → ℝ),
      Antitone r ∧ (∀ i, 0 < r i) ∧ r n = cutoff ∧
      r 0 ≤ distance ∧ distance < 2 * r 0 ∧
      (∀ i < n, r (i + 1) = r i / 2) ∧
      distance ≤ cutoff * (2 : ℝ) ^ (n + 1) := by
  have hratio : 1 ≤ distance / cutoff := (one_le_div hc).2 hd
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
  let r : ℕ → ℝ := fun i => cutoff * (2 : ℝ) ^ (n - i)
  have hpos : ∀ i, 0 < r i := by
    intro i
    exact mul_pos hc (pow_pos (by norm_num) _)
  have hanti : Antitone r := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le_sub_left hij n)) hc.le
  have hfirst : r 0 = cutoff * (2 : ℝ) ^ n := by simp [r]
  have hlast : r n = cutoff := by simp [r]
  have hstep : ∀ i < n, r (i + 1) = r i / 2 := by
    intro i hi
    have hsub : n - i = (n - (i + 1)) + 1 := by omega
    dsimp [r]
    rw [hsub, pow_succ]
    ring
  have hlo : r 0 ≤ distance := by
    rw [hfirst]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hn
  have hhi : distance < 2 * r 0 := by
    rw [hfirst]
    have h := (div_lt_iff₀ hc).mp hn'
    rw [pow_succ] at h
    linarith
  refine ⟨n, r, hanti, hpos, hlast, hlo, hhi, hstep, ?_⟩
  rw [pow_succ]
  rw [hfirst] at hhi
  linarith

/-- The selected scales satisfy the restart-set nesting required by the
annulus survival estimate. Every retained radius lies between the cutoff
and the outer distance. -/
theorem exists_dyadic_annulus_scales_with_restart {cutoff distance ε : ℝ}
    {η : ℝ → ℂ} {z : ℂ} (hc : 0 < cutoff) (hd : cutoff ≤ distance) :
    ∃ (n : ℕ) (r : ℕ → ℝ),
      Antitone r ∧ (∀ i ≤ n, cutoff ≤ r i ∧ r i ≤ distance) ∧
      distance ≤ cutoff * (2 : ℝ) ^ (n + 1) ∧
      (∀ i < n, cellVertices ε η (Metric.sphere z (r (i + 1))) ∩
        cellVertices ε η (Metric.ball z (r (i + 1))) ⊆
          cellVertices ε η (Metric.ball z (r i / 2))) := by
  obtain ⟨n, r, hanti, _, hlast, hlo, _, hstep, hscale⟩ :=
    exists_dyadic_annulus_scales hc hd
  refine ⟨n, r, hanti, ?_, hscale, ?_⟩
  · intro i hi
    exact ⟨hlast ▸ hanti hi, (hanti (Nat.zero_le i)).trans hlo⟩
  · apply nested_disk_restart_subset r n
    intro i hi
    exact (hstep i hi).le

end MatedCRT

#print axioms MatedCRT.exists_dyadic_annulus_scales
#print axioms MatedCRT.exists_dyadic_annulus_scales_with_restart
