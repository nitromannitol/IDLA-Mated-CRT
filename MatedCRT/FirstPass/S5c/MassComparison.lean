import MatedCRT.Defs.Setting

/-!
# FIRST PASS, Lemma 5.3: comparison of least supersolutions at two masses

Deterministic, no new frozen input. For `0 < s ≤ u` and a supersolution `w` at mass `u` (HB `supersolutions μ r 0 u`),
the function `(s/u) w` is a supersolution at mass `s`: it is continuous, `Δ((s/u) w) ≤ (s/u) μ ≤ μ` in the sense of
`LaplacianLE` (since `0 < s/u ≤ 1`), and the obstacle `-u G_{B_r}(0,·) ≤ w` scales to `-s G_{B_r}(0,·) ≤ (s/u) w`.
Hence `v_s(x) ≤ (s/u) v_u(x)` for `x ≠ 0`, an infimum over a larger set (Armitage-Gardiner, Classical Potential Theory,
Perron-type infimum of superharmonic majorants; HB Defs/Obstacle.lean `supersolutions`, `leastSupersolution`). At the
pole the inequality follows by continuity of both least supersolutions on `B̄_r`. Conclusion (3.4): `v_s/s ≤ v_u/u`.
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric Laplacian

/-- Scaling a supersolution at mass `u` by `s/u ∈ (0,1]` gives a supersolution at mass `s`. -/
theorem scale_mem_supersolutions {μ : Measure ℂ} {r s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) {w : ℂ → ℝ}
    (hw : w ∈ supersolutions μ r 0 u) : (fun x => (s / u) * w x) ∈ supersolutions μ r 0 s := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hu0 : u ≠ 0 := hu.ne'
  have hc0 : 0 ≤ s / u := (div_pos hs hu).le
  have hc1 : s / u ≤ 1 := (div_le_one hu).2 hsu
  simp only [supersolutions, Set.mem_ofPred_eq] at hw ⊢
  obtain ⟨hcont, hlap, hobs⟩ := hw
  refine ⟨continuousOn_const.mul hcont, ⟨hlap.1.smul (s / u), ?_⟩, ?_⟩
  · intro φ hφ hφ0 hφi
    have key := hlap.2 φ hφ hφ0 hφi
    have e : ∫ x, (s / u) * w x * Δ φ x = (s / u) * ∫ x, w x * Δ φ x := by
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    rw [e]
    calc (s / u) * ∫ x, w x * Δ φ x ≤ (s / u) * ∫ x, φ x ∂μ :=
          mul_le_mul_of_nonneg_left key hc0
      _ ≤ ∫ x, φ x ∂μ := mul_le_of_le_one_left (integral_nonneg hφ0) hc1
  · intro x hx hx0
    have h := hobs x hx hx0
    have e : s / u * (-u * greenFunction (ball 0 r) 0 x) = -s * greenFunction (ball 0 r) 0 x := by
      field_simp
    show -s * greenFunction (ball 0 r) 0 x ≤ s / u * w x
    rw [← e]
    exact mul_le_mul_of_nonneg_left h hc0

/-- Pointwise comparison off the pole: for `0 < s ≤ u` and `x ≠ 0` in `B̄_r`,
`v_{B_r}(s)(x) ≤ (s/u) v_{B_r}(u)(x)` (infimum over the larger set of supersolutions at mass `s`). -/
theorem leastSupersolution_le_scale {μ : Measure ℂ} {r s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) r) (hx0 : x ≠ 0) :
    leastSupersolution μ r 0 s x ≤ (s / u) * leastSupersolution μ r 0 u x := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hs0 : s ≠ 0 := hs.ne'
  have hu0 : u ≠ 0 := hu.ne'
  have hsu' : 0 < s / u := div_pos hs hu
  have hus : 0 < u / s := div_pos hu hs
  have hBdd : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s) := by
    refine ⟨-s * greenFunction (ball 0 r) 0 x, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hw.2.2 x hx hx0
  have hA : ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 u).Nonempty :=
    (supersolutions_nonempty μ r 0 hu.le).image _
  have h1 : ∀ w ∈ supersolutions μ r 0 u,
      sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s) ≤ (s / u) * w x := fun w hw =>
    csInf_le hBdd ⟨fun y => (s / u) * w y, scale_mem_supersolutions hs hsu hw, rfl⟩
  have h2 : (u / s) * sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s) ≤
      sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 u) := by
    apply le_csInf hA
    rintro _ ⟨w, hw, rfl⟩
    calc (u / s) * sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s)
        ≤ (u / s) * ((s / u) * w x) := mul_le_mul_of_nonneg_left (h1 w hw) hus.le
      _ = w x := by field_simp
  unfold leastSupersolution
  calc sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s)
      = (s / u) * ((u / s) * sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 s)) := by
        field_simp
    _ ≤ (s / u) * sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r 0 u) :=
        mul_le_mul_of_nonneg_left h2 hsu'.le

/-- Conclusion (3.4) of three-inputs A6: `v_s/s ≤ v_u/u` on `B̄_r`, for `0 < s ≤ u`, when both least supersolutions are
continuous on `B̄_r` (the pole is handled by continuity: `B̄_r ∖ {0}` is dense in `B̄_r` for `r > 0`). -/
theorem leastSupersolution_div_le {μ : Measure ℂ} {r s u : ℝ} (hr : 0 < r) (hs : 0 < s) (hsu : s ≤ u)
    (hcs : ContinuousOn (leastSupersolution μ r 0 s) (closedBall 0 r))
    (hcu : ContinuousOn (leastSupersolution μ r 0 u) (closedBall 0 r)) :
    ∀ x ∈ closedBall (0 : ℂ) r,
      leastSupersolution μ r 0 s x / s ≤ leastSupersolution μ r 0 u x / u := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have hs0 : s ≠ 0 := hs.ne'
  have hu0 : u ≠ 0 := hu.ne'
  have hpt : ∀ x ∈ closedBall (0 : ℂ) r, x ≠ 0 →
      leastSupersolution μ r 0 s x / s ≤ leastSupersolution μ r 0 u x / u := by
    intro x hx hx0
    have h := leastSupersolution_le_scale (μ := μ) hs hsu hx hx0
    have e : (s / u) * leastSupersolution μ r 0 u x / s = leastSupersolution μ r 0 u x / u := by
      field_simp
    calc leastSupersolution μ r 0 s x / s
        ≤ ((s / u) * leastSupersolution μ r 0 u x) / s := div_le_div_of_nonneg_right h hs.le
      _ = leastSupersolution μ r 0 u x / u := e
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    have hball : closedBall (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds 0 hr
    have hF : Tendsto (fun y => leastSupersolution μ r 0 s y / s) (𝓝[≠] (0 : ℂ))
        (𝓝 (leastSupersolution μ r 0 s 0 / s)) :=
      ((hcs.continuousAt hball).div_const s).tendsto.mono_left nhdsWithin_le_nhds
    have hG : Tendsto (fun y => leastSupersolution μ r 0 u y / u) (𝓝[≠] (0 : ℂ))
        (𝓝 (leastSupersolution μ r 0 u 0 / u)) :=
      ((hcu.continuousAt hball).div_const u).tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ y in 𝓝[≠] (0 : ℂ),
        leastSupersolution μ r 0 s y / s ≤ leastSupersolution μ r 0 u y / u := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_of_mem hball fun y hy => hy),
        self_mem_nhdsWithin] with y hy hy0
      exact hpt y hy hy0
    exact le_of_tendsto_of_tendsto hF hG hev
  · exact hpt x hx hx0

end MatedCRT.S5c
