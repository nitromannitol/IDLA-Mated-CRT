import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicPolynomialHorizon
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalInitialMaximum

/-! A dyadic horizon for the floored initial maximum.
The dyadic iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- A polynomial upper bound for the floored maximum gives the two-sided
rescaled bounds needed to choose the dyadic level and a cubic-log horizon. -/
theorem exists_dyadic_horizon_of_floored_initial_maximum
    (ε O K b α c s : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 0 < K) (hεK : ε ≤ K) (hKε : ε * K ≤ 1)
    (hb : 0 ≤ b) (hα : 0 < α) (hc : 0 < c) (hs : 0 < s)
    (hS : max O (ε ^ (-b)) ≤ ε⁻¹) :
    let S := max O (ε ^ (-b))
    let x := S * (ε * K)
    let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
    let q := (1 / 2 : ℝ) ^ α
    let A := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * 3
    let C := (1 + b) / Real.log 2
    ∃ N n : ℕ,
      S * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
      (N : ℝ) * (2 / s + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n ∧
      (n : ℝ) ≤ (C + 2) * (2 / s + 2) *
        (A + |Real.log q| * (C + 2)) ^ 2 * (1 + |Real.log ε|) ^ 3 + 2 := by
  let S := max O (ε ^ (-b))
  let x := S * (ε * K)
  have hSpos : 0 < S := lt_of_lt_of_le (Real.rpow_pos_of_pos hε _) (le_max_right _ _)
  have hxpos : 0 < x := mul_pos hSpos (mul_pos hε hK)
  have hSone : 1 ≤ S := by
    have h := Real.rpow_le_rpow_of_exponent_ge hε hε1 (show -b ≤ (0 : ℝ) by linarith)
    simpa only [Real.rpow_zero] using h.trans (le_max_right O (ε ^ (-b)))
  have hlo : ε ^ (2 : ℝ) ≤ x := by
    rw [Real.rpow_two]
    dsimp [x]
    nlinarith [mul_nonneg (sub_nonneg.mpr hεK) hε.le,
      mul_nonneg (sub_nonneg.mpr hSone) (mul_nonneg hε.le hK.le)]
  have hhi : x ≤ ε ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    have hmul := mul_le_mul_of_nonneg_left hS hε.le
    have hone : ε * S ≤ 1 := by simpa only [mul_inv_cancel₀ hε.ne'] using hmul
    have hxK : x ≤ K := by
      dsimp [x]
      nlinarith [mul_nonneg (sub_nonneg.mpr hone) hK.le]
    have hKinv : K ≤ ε⁻¹ := by
      have h := (le_div_iff₀ hε).2 (show K * ε ≤ 1 by nlinarith)
      simpa only [one_div] using h
    exact hxK.trans hKinv
  have htarget : ε ^ b ≤ ε ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have h := exists_dyadic_horizon_of_polynomial_scales ε S (ε ^ (-b)) x
    1 b 2 1 α c s hε hε1 hSpos (Real.rpow_pos_of_pos hε _) hxpos hα hc hs
    (by norm_num) (by norm_num) (by linarith) (by simpa only [Real.rpow_neg_one] using hS) htarget hlo hhi
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using h


/-- Conditional initial-odometer control gives a dyadic level and a
cubic-logarithmic horizon with probability tending to one on the event. -/
theorem tendsToOneOn_exists_dyadic_horizon_of_floored_maximum
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (O : ℝ → Ω → ℝ) {K b α c s : ℝ}
    (hK : 0 < K) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hα : 0 < α) (hc : 0 < c) (hs : 0 < s)
    (hsmall : TendsToOneOn P F (fun ε => {ω | ε * O ε ω ≤ 1})) :
    TendsToOneOn P F (fun ε => {ω |
      let S := max (O ε ω) (ε ^ (-b))
      let x := S * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      let A := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * 3
      let C := (1 + b) / Real.log 2
      ∃ N n : ℕ,
        S * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
        (N : ℝ) * (2 / s + 2) *
          (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n ∧
        (n : ℝ) ≤ (C + 2) * (2 / s + 2) *
          (A + |Real.log q| * (C + 2)) ^ 2 * (1 + |Real.log ε|) ^ 3 + 2}) := by
  have hmax := tendsToOneOn_floored_initial_maximum_le_inv P F O hb1 hsmall
  unfold TendsToOneOn at hmax ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmax
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hK).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (inv_pos.mpr hK)).filter_mono nhdsWithin_le_nhds]
    with ε hε hε1 hεK hεKi
  apply measure_mono
  rintro ω ⟨hF, hbad⟩
  refine ⟨hF, ?_⟩
  intro hS
  apply hbad
  have hKε : ε * K ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hεKi.le hK.le
    simpa only [inv_mul_cancel₀ hK.ne'] using hh
  exact exists_dyadic_horizon_of_floored_initial_maximum ε (O ε ω) K b α c s
    hε hε1.le hK hεK.le hKε hb hα hc hs hS

end MatedCRT.Sec7
