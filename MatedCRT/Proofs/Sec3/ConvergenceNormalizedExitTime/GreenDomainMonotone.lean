import HarmonicBalls.Defs.Green

/-!
Domain monotonicity of the Green function, with the diagonal convention used by
`HarmonicBalls`. This follows directly from restriction of harmonic minorants.
-/

open Set Metric

namespace HarmonicBalls

/-- The Green function increases when a bounded domain is enlarged. -/
theorem greenFunction_le_of_subset {O U : Set ℂ} (hU : Bornology.IsBounded U)
    (hsub : O ⊆ U) (x y : ℂ) : greenFunction O x y ≤ greenFunction U x y := by
  classical
  by_cases h : x ∈ O ∧ y ∈ O ∧ x ≠ y
  · have hUxy : x ∈ U ∧ y ∈ U ∧ x ≠ y := ⟨hsub h.1, hsub h.2.1, h.2.2⟩
    have hminor : greatestHarmonicMinorant U (newtonKernelEReal x) y ≤
        greatestHarmonicMinorant O (newtonKernelEReal x) y := by
      apply iSup₂_le
      intro f hf
      exact (show IsHarmonicMinorant O (newtonKernelEReal x) f from
        ⟨hf.1.mono hsub, fun z hz => hf.2 z (hsub hz)⟩).le_greatestHarmonicMinorant y
    obtain ⟨r, hr⟩ := hU.subset_closedBall x
    have hlow := (isHarmonicMinorant_const_newtonKernelEReal hr).le_greatestHarmonicMinorant y
    have hbot : greatestHarmonicMinorant U (newtonKernelEReal x) y ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
    have hup : greatestHarmonicMinorant O (newtonKernelEReal x) y ≤
        (newtonKernel x y : EReal) := by
      simpa [newtonKernelEReal, Ne.symm h.2.2] using
        greatestHarmonicMinorant_le (u := newtonKernelEReal x) h.2.1
    have htop : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
    have hreal := EReal.toReal_le_toReal hminor hbot htop
    simpa [greenFunction, h.1, h.2.1, h.2.2, hUxy.1, hUxy.2.1] using
      (sub_le_sub_left hreal (newtonKernel x y))
  · simpa only [greenFunction, h, ↓reduceIte] using greenFunction_nonneg hU x y

/-- An enclosing ball gives the logarithmic upper bound for its Green function. -/
theorem greenFunction_le_log_div {O : Set ℂ} {x y : ℂ} {R : ℝ}
    (hR : 0 < R) (hO : O ⊆ closedBall x R) (hx : x ∈ O) (hy : y ∈ O)
    (hxy : x ≠ y) :
    greenFunction O x y ≤ (2 * Real.pi)⁻¹ * Real.log (R / ‖x - y‖) := by
  have hlow := (isHarmonicMinorant_const_newtonKernelEReal hO).le_greatestHarmonicMinorant y
  have hup : greatestHarmonicMinorant O (newtonKernelEReal x) y ≤
      (newtonKernel x y : EReal) := by
    simpa [newtonKernelEReal, Ne.symm hxy] using
      greatestHarmonicMinorant_le (u := newtonKernelEReal x) hy
  have htop : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  have hreal := EReal.toReal_le_toReal hlow (EReal.coe_ne_bot _) htop
  rw [EReal.toReal_coe] at hreal
  have hdist : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  rw [Real.log_div hR.ne' hdist]
  have hgreen : greenFunction O x y =
      newtonKernel x y - (greatestHarmonicMinorant O (newtonKernelEReal x) y).toReal := by
    simp [greenFunction, hx, hy, hxy]
  rw [hgreen, newtonKernel]
  nlinarith

/-- On a unit neighbourhood of the pole, the Green function is bounded by the
logarithmic kernel appearing in the largest-exit-time estimate. -/
theorem greenFunction_le_exitTimeKernel {O : Set ℂ} {x y : ℂ}
    (hO : O ⊆ closedBall x 2) (hx : x ∈ O) (hy : y ∈ O)
    (hxy : x ≠ y) (hd : ‖x - y‖ ≤ 1) :
    greenFunction O x y ≤ Real.log (1 / ‖x - y‖) + 1 := by
  have hdist : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hlog : 0 ≤ Real.log (1 / ‖x - y‖) :=
    Real.log_nonneg ((one_le_div₀ hdist).mpr hd)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hc0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hc1 : (2 * Real.pi)⁻¹ ≤ 1 := by
    have hπ : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hπ)
  have heq : Real.log (2 / ‖x - y‖) = Real.log 2 + Real.log (1 / ‖x - y‖) := by
    rw [Real.log_div (by norm_num) hdist.ne', Real.log_div one_ne_zero hdist.ne', Real.log_one]
    ring
  calc
    greenFunction O x y ≤ (2 * Real.pi)⁻¹ * Real.log (2 / ‖x - y‖) :=
      greenFunction_le_log_div (by norm_num) hO hx hy hxy
    _ ≤ Real.log (1 / ‖x - y‖) + 1 := by
      rw [heq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hlog,
        mul_nonneg hc0 (sub_nonneg.mpr hlog2)]

end HarmonicBalls
