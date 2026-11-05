import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicHorizonCertificate
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalBudgetSum

/-! Conditional choice of a dyadic level with a spatial budget.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- A deterministic-horizon budget and conditional initial-maximum control
provide a dyadic level and a budgeted stopping horizon with high probability. -/
theorem tendsToOneOn_exists_dyadic_horizon_with_budget
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (O r₀ F D : ℝ → Ω → ℝ) {K b α c s T δ : ℝ}
    (hK : 0 < K) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hα : 0 < α) (hc : 0 < c) (hs : 0 < s)
    (hsmall : TendsToOneOn P E (fun ε => {ω | ε * O ε ω ≤ 1}))
    (hbudget : TendsToOneOn P E (fun ε => {ω |
      let S := max (O ε ω) (ε ^ (-b))
      let x := S * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      let A := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * 3
      let C := (1 + b) / Real.log 2
      let H := (C + 2) * (2 / s + 2) *
        (A + |Real.log q| * (C + 2)) ^ 2 * (1 + |Real.log ε|) ^ 3 + 2
      0 ≤ F ε ω ∧ 0 ≤ D ε ω ∧
      r₀ ε ω + (x ^ α * (2 / s + 2) *
        ((1 + |Real.log a| + |Real.log q|) ^ 2 * T) + F ε ω * H) +
        (H + 1) * (2 * D ε ω) ≤ δ})) :
    TendsToOneOn P E (fun ε => {ω |
      let S := max (O ε ω) (ε ^ (-b))
      let x := S * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      ∃ N n : ℕ,
        S * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
        let H := (N : ℝ) * (2 / s + 2) *
          (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2
        H < (n : ℝ) ∧ r₀ ε ω + (x ^ α * (2 / s + 2) *
          ((1 + |Real.log a| + |Real.log q|) ^ 2 * T) + F ε ω * H) +
          (H + 1) * (2 * D ε ω) ≤ δ}) := by
  have hmax := tendsToOneOn_floored_initial_maximum_le_inv P E O hb1 hsmall
  have hboth := tendsToOneOn_inter P E _ _ hmax hbudget
  unfold TendsToOneOn at hboth ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboth
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hK).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (inv_pos.mpr hK)).filter_mono nhdsWithin_le_nhds]
    with ε hε hε1 hεK hεKi
  apply measure_mono
  rintro ω ⟨hE, hbad⟩
  refine ⟨hE, ?_⟩
  rintro ⟨hS, hF, hD, hbound⟩
  apply hbad
  have hKε : ε * K ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hεKi.le hK.le
    simpa only [inv_mul_cancel₀ hK.ne'] using hh
  exact exists_dyadic_horizon_with_budget ε (O ε ω) K b α c s (r₀ ε ω) (F ε ω)
    (D ε ω) T δ hε hε1.le hK hεK.le hKε hb hα hc hs hF hD hS hbound

end MatedCRT.Sec7
