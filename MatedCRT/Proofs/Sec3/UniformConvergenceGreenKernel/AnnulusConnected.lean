import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Harmonic.Analytic

/-! # A disc with a smaller closed disc removed is connected

The domain on which Lemma 3.1 is applied in the proof of Lemma 3.3 is `B_R(z) \ cl(B_s(y))`, which
avoids the pole `y` of the Green kernel. Every point is joined, along the ray from `y`, to the
connected circle `∂B_{t₀}(y)`. -/

namespace MatedCRT.GreenEnvironment

open Set Metric

/-- `B_R(z) \ cl(B_s(y))` is connected when `cl(B_s(y)) ⊆ B_R(z)` (strictly). -/
theorem isConnected_ball_diff_closedBall {z y : ℂ} {R s : ℝ} (hs : 0 ≤ s)
    (hy : dist y z + s < R) : IsConnected (ball z R \ closedBall y s) := by
  set t₀ : ℝ := (s + (R - dist y z)) / 2 with ht₀
  have ht₀s : s < t₀ := by rw [ht₀]; linarith
  have ht₀R : dist y z + t₀ < R := by rw [ht₀]; linarith
  have ht₀0 : 0 < t₀ := lt_of_le_of_lt hs ht₀s
  have hS : sphere y t₀ ⊆ ball z R \ closedBall y s := by
    intro w hw
    rw [mem_sphere] at hw
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
        _ < R := by rw [hw]; linarith
    · rw [mem_closedBall, not_le, hw]
      exact ht₀s
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hSc : IsConnected (sphere y t₀) := isConnected_sphere hrank y ht₀0.le
  obtain ⟨x₀, hx₀⟩ := hSc.nonempty
  refine ⟨⟨x₀, hS hx₀⟩, ?_⟩
  refine isPreconnected_of_forall x₀ fun w hw => ?_
  have hwy : s < dist w y := by
    have := hw.2
    rw [mem_closedBall, not_le] at this
    exact this
  have hn : 0 < dist w y := lt_of_le_of_lt hs hwy
  set p : ℂ := y + (t₀ / dist w y) • (w - y) with hp
  have hpS : p ∈ sphere y t₀ := by
    rw [mem_sphere, dist_eq_norm, hp, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos ht₀0 hn), ← dist_eq_norm, div_mul_cancel₀ _ hn.ne']
  refine ⟨segment ℝ w p ∪ sphere y t₀, ?_, Or.inr hx₀, Or.inl (left_mem_segment ℝ w p), ?_⟩
  · refine union_subset ?_ hS
    intro q hq
    refine ⟨(convex_ball z R).segment_subset hw.1 (hS hpS).1 hq, ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
    rw [mem_closedBall, not_le, dist_eq_norm]
    have hrepr : a • w + b • p - y = (a + b * (t₀ / dist w y)) • (w - y) := by
      rw [hp]
      calc a • w + b • (y + (t₀ / dist w y) • (w - y)) - y =
            a • w + b • (y + (t₀ / dist w y) • (w - y)) - (a + b) • y := by
            rw [hab, one_smul]
        _ = (a + b * (t₀ / dist w y)) • (w - y) := by
            simp only [add_smul, smul_add, smul_sub, mul_smul]
            abel
    rw [hrepr, norm_smul, Real.norm_eq_abs, ← dist_eq_norm,
      abs_of_nonneg (by positivity), add_mul, mul_assoc, div_mul_cancel₀ _ hn.ne']
    have h1 : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      linarith
    · nlinarith
  · exact (convex_segment w p).isPreconnected.union p (right_mem_segment ℝ w p) hpS
      hSc.isPreconnected

end MatedCRT.GreenEnvironment
