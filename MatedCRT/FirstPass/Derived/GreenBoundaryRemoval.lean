import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov

/-!
# Removing the boundary constraint in the Green kernel bound

Deterministic part of the passage from [BG20, Lem. 5.5] to [BG20, Lem. 5.4]: a bound for the
Green kernel `g_B(·, x)` at distance at most `δ₀` from the pole is propagated, by the maximum
principle for the harmonic function `v ↦ g_B(v, x)` on `B \ {x}`, to the vertices at distance more
than `δ₀`.

## Main statements

* `MatedCRT.greenKernel_le_of_vBoundary_le`: maximum principle for `v ↦ g_B(v, x)` on a subset
  `R ⊆ B` not containing the pole.
* `MatedCRT.greenKernel_le_log_of_nearRange`: a logarithmic bound for the points at distance in
  `[r₀, δ₀]` of the pole gives the bound `C log (1/r) + C log (4/δ₀)` for all distances `r ≥ r₀`
  (at most `2`), when adjacent vertices have points at distance at most `2 δ_c ≤ δ₀/2`.
-/

namespace MatedCRT

open Set

variable {m : ℤ → ℤ → ℕ}

/-- **Maximum principle for the Green kernel.** If `R ⊆ B` is a set of vertices not containing the
pole `x` and `g_B(·, x) ≤ M` on the outer boundary of `R`, then `g_B(·, x) ≤ M` on `R`. -/
theorem greenKernel_le_of_vBoundary_le (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B R : Set ℤ} (hB : B.Finite) (hRB : R ⊆ B) {x : ℤ}
    (hx : x ∉ R) {M : ℝ} (hM : ∀ b ∈ vBoundary m R, greenKernel m B b x ≤ M) :
    ∀ y ∈ R, greenKernel m B y x ≤ M := by
  have hR : R.Finite := hB.subset hRB
  have hlf' : IsLocallyFiniteMult m := hlf
  have hesc := escape_of_adjacent_succ hcons hR
  set u : ℤ → ℝ := fun v => greenKernel m B v x with hu_def
  have hu : u = fun v => (mdeg m x : ℝ)⁻¹ * greenFn m B v x := by
    funext v
    simp only [hu_def, greenKernel]
    ring
  have hsub : ∀ v ∈ R, 0 ≤ mLaplacian m u v := by
    intro v hv
    rw [hu, mLaplacian_const_mul, greenFn_laplacian_fst hlf' hcons hB x v (hRB hv)]
    have : v ≠ x := fun h => hx (h ▸ hv)
    simp [this]
  have key : ∀ y ∈ R, u y - M ≤ 0 := by
    refine nonpos_of_lapSum_nonneg hlf' hR hesc (w := fun x => u x - M) ?_ ?_
    · intro v hv
      have hshift : lapSum hlf' (fun y => u y - M) v = lapSum hlf' u v := by
        simp only [lapSum, sub_sub_sub_cancel_right]
      rw [hshift, ← mLaplacian_mul_mdeg hlf' u v]
      exact mul_nonneg (hsub v hv) (Nat.cast_nonneg _)
    · intro v hv b' hvb' hb'
      show u b' - M ≤ 0
      linarith [hM b' ⟨hb', v, hv, hvb'⟩]
  intro y hy
  linarith [key y hy]

/-- **A near-range logarithmic bound for the Green kernel gives a bound at all distances.**
Let `p` assign a point to each vertex, adjacent vertices having points at distance at most
`2 δ_c ≤ δ₀/2`, and `r₀ ≤ δ₀/2`. If `g_B(a, b) ≤ C log (1/‖p a - p b‖)` whenever
`r₀ ≤ ‖p a - p b‖ ≤ δ₀` (`b` in a set `B'` of poles), then
`g_B(a, b) ≤ C log (1/‖p a - p b‖) + C log (4/δ₀)` whenever `r₀ ≤ ‖p a - p b‖ ≤ 2`
([BG20, proof of Lem. 5.4, (5.19)] by the maximum principle). -/
theorem greenKernel_le_log_of_nearRange (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B B' : Set ℤ} (hB : B.Finite)
    (p : ℤ → ℂ) {r₀ δ₀ δc C : ℝ} (hC : 0 ≤ C) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hr₀ : r₀ ≤ δ₀ / 2) (hδc : 4 * δc ≤ δ₀)
    (hstep : ∀ y y', m y y' ≠ 0 → ‖p y - p y'‖ ≤ 2 * δc)
    (hmain : ∀ a ∈ B, ∀ b ∈ B', r₀ ≤ ‖p a - p b‖ → ‖p a - p b‖ ≤ δ₀ →
      greenKernel m B a b ≤ C * Real.log (1 / ‖p a - p b‖)) :
    ∀ a ∈ B, ∀ b ∈ B', r₀ ≤ ‖p a - p b‖ → ‖p a - p b‖ ≤ 2 →
      greenKernel m B a b ≤ C * Real.log (1 / ‖p a - p b‖) + C * Real.log (4 / δ₀) := by
  intro a ha b hb hr hr2
  have hlog4 : 0 ≤ Real.log (4 / δ₀) := Real.log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  have hlog2 : 0 ≤ Real.log (2 / δ₀) := Real.log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  by_cases hnear : ‖p a - p b‖ ≤ δ₀
  · have := hmain a ha b hb hr hnear
    linarith [mul_nonneg hC hlog4]
  · rw [not_le] at hnear
    set R : Set ℤ := {y | y ∈ B ∧ δ₀ < ‖p y - p b‖} with hR_def
    have hRB : R ⊆ B := fun y hy => hy.1
    have hbR : b ∉ R := fun h => by
      have := h.2
      simp only [sub_self, norm_zero] at this
      linarith
    have hM : ∀ b' ∈ vBoundary m R, greenKernel m B b' b ≤ C * Real.log (2 / δ₀) := by
      rintro b' ⟨hb'R, y, hyR, hyb'⟩
      by_cases hb'B : b' ∈ B
      · have hnR : ‖p b' - p b‖ ≤ δ₀ := not_lt.1 fun h => hb'R ⟨hb'B, h⟩
        have h1 := hstep y b' hyb'
        have h2 : ‖p y - p b‖ ≤ ‖p y - p b'‖ + ‖p b' - p b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        have hy2 := hyR.2
        have hlow : δ₀ / 2 ≤ ‖p b' - p b‖ := by linarith
        have hpos : 0 < δ₀ / 2 := by positivity
        have := hmain b' hb'B b hb (hr₀.trans hlow) hnR
        refine this.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by
          have : 0 < ‖p b' - p b‖ := hpos.trans_le hlow
          positivity) ?_) hC)
        calc 1 / ‖p b' - p b‖ ≤ 1 / (δ₀ / 2) := one_div_le_one_div_of_le hpos hlow
          _ = 2 / δ₀ := by field_simp
      · have : greenKernel m B b' b = 0 := by
          unfold greenKernel
          rw [greenFn_eq_zero_of_not_mem m hb'B b]
          simp
        rw [this]
        exact mul_nonneg hC hlog2
    have hg := greenKernel_le_of_vBoundary_le hlf hcons hB hRB hbR hM a ⟨ha, hnear⟩
    refine hg.trans ?_
    have hrpos : 0 < ‖p a - p b‖ := hδ₀.trans hnear
    have hlogle : Real.log (2 / δ₀) ≤ Real.log (1 / ‖p a - p b‖) + Real.log (4 / δ₀) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      rw [div_mul_div_comm, div_le_div_iff₀ hδ₀ (by positivity)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hlogle hC]

end MatedCRT
