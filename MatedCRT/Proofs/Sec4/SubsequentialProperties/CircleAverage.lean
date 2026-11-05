import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-!
# Circle averages: continuity and superharmonicity from rational circles

Deterministic potential theory for the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, Steps 2 and 3,
l.1803-1915), where the super-mean-value inequality of a subsequential limit is first obtained on the countably many
circles with rational centre and radius.

* `tendsto_circleAverage`: circle averages of a function continuous on `cl(B_r(x))` are continuous in the centre and
  the radius, for circles inside `cl(B_r(x))`.
* `isSuperharmonicOn_of_ratCircles`: a continuous function on an open set with the super-mean-value inequality on all
  circles with rational centre and radius whose closed disc lies in the set is superharmonic there (in the sense of
  `HarmonicBalls.IsSuperharmonicOn`, Armitage-Gardiner Definition 3.1.2).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Real

/-- The point `q₁ + q₂ i` with rational coordinates. -/
noncomputable def ratPoint (q₁ q₂ : ℚ) : ℂ := ⟨q₁, q₂⟩

/-- Points with rational coordinates are dense. -/
theorem exists_ratPoint_dist_lt (x : ℂ) {δ : ℝ} (hδ : 0 < δ) : ∃ q₁ q₂ : ℚ, dist (ratPoint q₁ q₂) x < δ := by
  obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show x.re - δ / 2 < x.re + δ / 2 by linarith)
  obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show x.im - δ / 2 < x.im + δ / 2 by linarith)
  refine ⟨q₁, q₂, ?_⟩
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  have h1 : |(ratPoint q₁ q₂ - x).re| < δ / 2 := by
    simp only [ratPoint, Complex.sub_re]
    rw [abs_lt]; constructor <;> linarith [hq₁.1, hq₁.2]
  have h2 : |(ratPoint q₁ q₂ - x).im| < δ / 2 := by
    simp only [ratPoint, Complex.sub_im]
    rw [abs_lt]; constructor <;> linarith [hq₂.1, hq₂.2]
  linarith

/-- Distance between corresponding points of two circles. -/
theorem dist_circleMap_le (c c' : ℂ) (R R' θ : ℝ) :
    dist (circleMap c R θ) (circleMap c' R' θ) ≤ dist c c' + |R - R'| := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : circleMap c R θ - circleMap c' R' θ = (c - c') + ((R - R' : ℝ) : ℂ) * Complex.exp (θ * Complex.I) := by
    simp only [circleMap]; push_cast; ring
  rw [h]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Continuity of circle averages** in the centre and the radius, for circles inside a closed disc on which the
function is continuous. -/
theorem tendsto_circleAverage {g : ℂ → ℝ} {x : ℂ} {r : ℝ} (hr : 0 ≤ r) (hg : ContinuousOn g (closedBall x r))
    {c : ℕ → ℂ} {R : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 x)) (hR : Tendsto R atTop (𝓝 r))
    (hsub : ∀ᶠ n in atTop, sphere (c n) |R n| ⊆ closedBall x r) :
    Tendsto (fun n => circleAverage g (c n) (R n)) atTop (𝓝 (circleAverage g x r)) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hsub
  have hunif := (isCompact_closedBall x r).uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at hunif
  have hsph : sphere x |r| ⊆ closedBall x r := by
    rw [abs_of_nonneg hr]; exact sphere_subset_closedBall
  have hcont : ∀ (c' : ℂ) (R' : ℝ), sphere c' |R'| ⊆ closedBall x r →
      Continuous fun θ => g (circleMap c' R' θ) := fun c' R' h =>
    hg.comp_continuous (continuous_circleMap c' R') fun θ => h (circleMap_mem_sphere' c' R' θ)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨η, hη, hηg⟩ := hunif (δ / 2) (half_pos hδ)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hc (η / 2) (half_pos hη)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hR (η / 2) (half_pos hη)
  refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hsubn := hN₀ n (max_le_iff.1 hn).1
  have hc' := hN₁ n (max_le_iff.1 (max_le_iff.1 hn).2).1
  have hR' := hN₂ n (max_le_iff.1 (max_le_iff.1 hn).2).2
  rw [Real.dist_eq] at hR'
  have hpt : ∀ θ, |g (circleMap (c n) (R n) θ) - g (circleMap x r θ)| ≤ δ / 2 := by
    intro θ
    have hd : dist (circleMap (c n) (R n) θ) (circleMap x r θ) < η :=
      (dist_circleMap_le _ _ _ _ θ).trans_lt (by linarith)
    have := hηg _ (hsubn (circleMap_mem_sphere' _ _ θ)) _ (hsph (circleMap_mem_sphere' _ _ θ)) hd
    rw [Real.dist_eq] at this
    exact this.le
  have hint1 := (hcont (c n) (R n) hsubn).intervalIntegrable (μ := volume) 0 (2 * π)
  have hint0 := (hcont x r hsph).intervalIntegrable (μ := volume) 0 (2 * π)
  have hI : ‖∫ θ in (0 : ℝ)..2 * π, (g (circleMap (c n) (R n) θ) - g (circleMap x r θ))‖ ≤
      δ / 2 * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
      rw [Real.norm_eq_abs]; exact hpt θ
  rw [intervalIntegral.integral_sub hint1 hint0, Real.norm_eq_abs] at hI
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [sub_zero, abs_of_pos h2π] at hI
  rw [Real.dist_eq]
  simp only [Real.circleAverage, smul_eq_mul]
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 h2π)]
  calc (2 * π)⁻¹ * |(∫ θ in (0 : ℝ)..2 * π, g (circleMap (c n) (R n) θ)) - ∫ θ in (0 : ℝ)..2 * π, g (circleMap x r θ)|
      ≤ (2 * π)⁻¹ * (δ / 2 * (2 * π)) := mul_le_mul_of_nonneg_left hI (inv_nonneg.2 h2π.le)
    _ = δ / 2 := by rw [mul_comm (δ / 2), ← mul_assoc, inv_mul_cancel₀ h2π.ne', one_mul]
    _ < δ := half_lt_self hδ

/-- **Superharmonicity from rational circles.** A function continuous on an open set `U`, with
`⨍_{∂B_s(z)} g ≤ g(z)` for every `z` with rational coordinates and rational `s > 0` such that `cl(B_s(z)) ⊆ U`, is
superharmonic on `U`. -/
theorem isSuperharmonicOn_of_ratCircles {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℝ} (hg : ContinuousOn g U)
    (hmean : ∀ q₁ q₂ s : ℚ, (0 : ℝ) < s → closedBall (ratPoint q₁ q₂) s ⊆ U →
      circleAverage g (ratPoint q₁ q₂) s ≤ g (ratPoint q₁ q₂)) :
    IsSuperharmonicOn U g := by
  refine ⟨hg.lowerSemicontinuousOn, fun x hx r hr hxr => ⟨?_, ?_⟩⟩
  · exact (hg.mono ((sphere_subset_closedBall).trans hxr)).circleIntegrable hr.le
  · have hpt : ∀ n : ℕ, ∃ q₁ q₂ : ℚ, dist (ratPoint q₁ q₂) x < 1 / ((n : ℝ) + 1) := fun n =>
      exists_ratPoint_dist_lt x (by positivity)
    choose q₁ q₂ hq using hpt
    have hrad : ∀ n : ℕ, ∃ s : ℚ, r - 3 / ((n : ℝ) + 1) < s ∧ (s : ℝ) < r - 2 / ((n : ℝ) + 1) := by
      intro n
      apply exists_rat_btwn
      have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h3 : 3 / ((n : ℝ) + 1) = 3 * (1 / ((n : ℝ) + 1)) := by ring
      have h2 : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
      rw [h3, h2]
      linarith
    choose s hs using hrad
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun n => ratPoint (q₁ n) (q₂ n)) atTop (𝓝 x) :=
      tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) (fun n => (hq n).le) hinv)
    have hR : Tendsto (fun n => ((s n : ℚ) : ℝ)) atTop (𝓝 r) := by
      have h3 : Tendsto (fun n : ℕ => r - 3 * (1 / ((n : ℝ) + 1))) atTop (𝓝 r) := by
        simpa using (hinv.const_mul 3).const_sub r
      have h2 : Tendsto (fun n : ℕ => r - 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 r) := by
        simpa using (hinv.const_mul 2).const_sub r
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le h3 h2 (fun n => ?_) (fun n => ?_)
      · have : 3 / ((n : ℝ) + 1) = 3 * (1 / ((n : ℝ) + 1)) := by ring
        linarith [(hs n).1]
      · have : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
        linarith [(hs n).2]
    have hspos : ∀ᶠ n in atTop, (0 : ℝ) < s n := hR.eventually (lt_mem_nhds hr)
    -- the rational discs lie in `cl(B_r(x))`
    have hdisc : ∀ n, closedBall (ratPoint (q₁ n) (q₂ n)) (s n) ⊆ closedBall x r := by
      intro n y hy
      rw [mem_closedBall] at hy ⊢
      have h1 := hq n
      have h2 := (hs n).2
      have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h2' : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
      linarith [dist_triangle y (ratPoint (q₁ n) (q₂ n)) x]
    have hsph : ∀ᶠ n in atTop, sphere (ratPoint (q₁ n) (q₂ n)) |((s n : ℚ) : ℝ)| ⊆ closedBall x r := by
      filter_upwards [hspos] with n hn
      rw [abs_of_pos hn]
      exact sphere_subset_closedBall.trans (hdisc n)
    have hlim := tendsto_circleAverage hr.le (hg.mono hxr) hc hR hsph
    have hgx : Tendsto (fun n => g (ratPoint (q₁ n) (q₂ n))) atTop (𝓝 (g x)) :=
      ((hg.continuousAt (hU.mem_nhds hx)).tendsto).comp hc
    refine le_of_tendsto_of_tendsto hlim hgx ?_
    filter_upwards [hspos] with n hn
    exact hmean (q₁ n) (q₂ n) (s n) hn ((hdisc n).trans hxr)

end MatedCRT
