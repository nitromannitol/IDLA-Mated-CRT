import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalDyadicHorizon

/-! The dyadic budget at a deterministic horizon controls the selected level.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

/-- A budget at the cubic-logarithmic upper horizon also bounds the actual
horizon of the selected dyadic level. -/
theorem exists_dyadic_horizon_with_budget
    (ε O K b α c s r₀ F D T δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 < K)
    (hεK : ε ≤ K) (hKε : ε * K ≤ 1)
    (hb : 0 ≤ b) (hα : 0 < α) (hc : 0 < c) (hs : 0 < s)
    (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hS : max O (ε ^ (-b)) ≤ ε⁻¹)
    (hbudget :
      let S := max O (ε ^ (-b))
      let x := S * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      let A := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * 3
      let C := (1 + b) / Real.log 2
      let H := (C + 2) * (2 / s + 2) *
        (A + |Real.log q| * (C + 2)) ^ 2 * (1 + |Real.log ε|) ^ 3 + 2
      r₀ + (x ^ α * (2 / s + 2) *
        ((1 + |Real.log a| + |Real.log q|) ^ 2 * T) + F * H) +
        (H + 1) * (2 * D) ≤ δ) :
    let S := max O (ε ^ (-b))
    let x := S * (ε * K)
    let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
    let q := (1 / 2 : ℝ) ^ α
    ∃ N n : ℕ,
      S * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
      let H := (N : ℝ) * (2 / s + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2
      H < (n : ℝ) ∧ r₀ + (x ^ α * (2 / s + 2) *
        ((1 + |Real.log a| + |Real.log q|) ^ 2 * T) + F * H) +
        (H + 1) * (2 * D) ≤ δ := by
  obtain ⟨N, n, htarget, hn, hupper⟩ :=
    exists_dyadic_horizon_of_floored_initial_maximum ε O K b α c s
      hε hε1 hK hεK hKε hb hα hc hs hS
  refine ⟨N, n, htarget, hn, ?_⟩
  dsimp only at hn hupper hbudget ⊢
  have hH := le_trans (le_of_lt hn) hupper
  have hFH := mul_le_mul_of_nonneg_left hH hF
  have hDH := mul_le_mul_of_nonneg_right (add_le_add_right hH 1) (by positivity : 0 ≤ 2 * D)
  linarith

end MatedCRT.Sec7
