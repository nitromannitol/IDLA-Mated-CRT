import MatedCRT.FirstPass.Derived.InterpolatedWalkPath

/-!
# The interpolated walk stays within half a step of the current vertex

For a sequence `a : ℕ → ℂ` whose consecutive points are at distance at most `2d`, the linear
interpolation `linInterp a` stays within `d` of `a m` on the half-step window `|s - m| ≤ 1/2`:
on `[m, m + 1/2]` it lies on the segment from `a m` to `a (m + 1)`, at most half-way, and on
`[m - 1/2, m]` it lies on the segment from `a (m - 1)` to `a m`, at least half-way.

For the embedded walk `interpolatedWalk ε η 1 x` (time = step count) this is the half-step
nearness hypothesis of the template itinerary lemma
`LatticeProb.PolarTemplate.isTemplateWalk_of_uniform_approx` (Lattice-Probability); consecutive
vertex points are within `2d` when the cells of consecutive vertices intersect and have diameter at
most `d` (`dist_le_two_mul_of_inter_nonempty`).
-/

set_option autoImplicit false

open scoped NNReal

namespace MatedCRT.LinInterpHalfStep

/-- `linInterp a s` on the step `⌊s⌋₊ = n`: the point `a n + (s - n) (a (n+1) - a n)`. -/
theorem linInterp_of_floor_eq {a : ℕ → ℂ} {s : ℝ} {n : ℕ} (h : ⌊s⌋₊ = n) :
    linInterp a s = a n + ((s - n : ℝ) : ℂ) * (a (n + 1) - a n) := by
  unfold linInterp
  rw [h]
  push_cast
  ring

/-- **Half-step nearness of the linear interpolation.** If `0 ≤ s`, `|s - m| ≤ 1/2`, and the
consecutive points `a m, a (m+1)` and (for `m ≥ 1`) `a (m-1), a m` are within `2d`, then
`linInterp a s` is within `d` of `a m`. -/
theorem dist_linInterp_le_of_half_step {a : ℕ → ℂ} {s d : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hsm : |s - m| ≤ 1 / 2) (hnext : dist (a m) (a (m + 1)) ≤ 2 * d)
    (hprev : ∀ k, k + 1 = m → dist (a k) (a m) ≤ 2 * d) :
    dist (linInterp a s) (a m) ≤ d := by
  obtain ⟨h1, h2⟩ := abs_le.1 hsm
  rcases le_or_gt (m : ℝ) s with hms | hms
  · have hfl : ⌊s⌋₊ = m := (Nat.floor_eq_iff hs).2 ⟨hms, by linarith⟩
    have key : linInterp a s - a m = ((s - m : ℝ) : ℂ) * (a (m + 1) - a m) := by
      rw [linInterp_of_floor_eq hfl]
      ring
    have hθ : (0 : ℝ) ≤ s - m := by linarith
    rw [dist_eq_norm, key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hθ, ← dist_eq_norm,
      dist_comm]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - (s - m) by linarith)
      (dist_nonneg (x := a m) (y := a (m + 1)))]
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.cast_zero] at hms
      linarith
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
    push_cast at h1 hms
    have hfl : ⌊s⌋₊ = k := (Nat.floor_eq_iff hs).2 ⟨by linarith, hms⟩
    have key : linInterp a s - a (k + 1) = ((1 - (s - k) : ℝ) : ℂ) * (a k - a (k + 1)) := by
      rw [linInterp_of_floor_eq hfl]
      push_cast
      ring
    have hθ : (0 : ℝ) ≤ 1 - (s - k) := by linarith
    rw [dist_eq_norm, key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hθ, ← dist_eq_norm]
    have hp := hprev k rfl
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - (1 - (s - k)) by linarith)
      (dist_nonneg (x := a k) (y := a (k + 1)))]

/-- **Half-step nearness of the embedded walk** (time = step count): `interpolatedWalk ε η 1 x t`
is within `d` of the vertex point of `x m` when `|t - m| ≤ 1/2` and the vertex points of
consecutive steps around `m` are within `2d`. -/
theorem dist_interpolatedWalk_le_of_half_step {ε d : ℝ} {η : ℝ → ℂ} {x : ℕ → ℤ} {t : ℝ≥0}
    {m : ℕ} (htm : |(t : ℝ) - m| ≤ 1 / 2)
    (hnext : dist (vertexPoint ε η (x m)) (vertexPoint ε η (x (m + 1))) ≤ 2 * d)
    (hprev : ∀ k, k + 1 = m → dist (vertexPoint ε η (x k)) (vertexPoint ε η (x m)) ≤ 2 * d) :
    dist (interpolatedWalk ε η 1 x t) (vertexPoint ε η (x m)) ≤ d := by
  rw [interpolatedWalk_eq_interpPathFn]
  unfold interpPathFn
  rw [one_mul]
  exact dist_linInterp_le_of_half_step (a := fun k => vertexPoint ε η (x k)) t.2 htm hnext hprev

/-- Points of two intersecting bounded sets of diameter at most `d` are within `2d`. -/
theorem dist_le_two_mul_of_inter_nonempty {X : Type*} [PseudoMetricSpace X] {s t : Set X}
    {p q : X} {d : ℝ} (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) (hp : p ∈ s)
    (hq : q ∈ t) (hst : (s ∩ t).Nonempty) (hds : Metric.diam s ≤ d)
    (hdt : Metric.diam t ≤ d) : dist p q ≤ 2 * d := by
  obtain ⟨w, hws, hwt⟩ := hst
  calc dist p q ≤ dist p w + dist w q := dist_triangle _ _ _
    _ ≤ d + d := add_le_add ((Metric.dist_le_diam_of_mem hs hp hws).trans hds)
        ((Metric.dist_le_diam_of_mem ht hwt hq).trans hdt)
    _ = 2 * d := by ring

end MatedCRT.LinInterpHalfStep
