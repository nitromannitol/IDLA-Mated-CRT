import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalBudgetCertificate

/-! Choosing a dyadic level from polynomial floor and diameter bounds.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Qualitative initial control and polynomial errors yield a budgeted dyadic
horizon with high probability on the conditioning event. -/
theorem tendsToOneOn_budgeted_dyadic_horizon_of_polynomial_errors
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (O r₀ R D : ℝ → Ω → ℝ) {K b α c s T δ q d E₁ E₂ : ℝ}
    (hK : 0 < K) (hb : 0 ≤ b) (hb1 : b < 1)
    (hα : 0 < α) (hc : 0 < c) (hs : 0 < s) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hq : 0 < q) (hd : 0 < d)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn P E (fun ε => {ω | ε * O ε ω ≤ a}))
    (hr₀ : ∀ a : ℝ, 0 < a → TendsToOneOn P E (fun ε => {ω | r₀ ε ω ≤ a}))
    (hpoly : TendsToOneOn P E (fun ε => {ω |
      0 ≤ R ε ω ∧ R ε ω ≤ E₁ * ε ^ q ∧
      0 ≤ D ε ω ∧ D ε ω ≤ E₂ * ε ^ d})) :
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
          ((1 + |Real.log a| + |Real.log q|) ^ 2 * T) + R ε ω * H) +
          (H + 1) * (2 * D ε ω) ≤ δ}) := by
  let A := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * 3
  let C := (1 + b) / Real.log 2
  let Cₕ := (C + 2) * (2 / s + 2) *
    (A + |Real.log ((1 / 2 : ℝ) ^ α)| * (C + 2)) ^ 2
  let H : ℝ → Ω → ℝ := fun ε _ => Cₕ * (1 + |Real.log ε|) ^ 3 + 2
  let x : ℝ → Ω → ℝ := fun ε ω => max (O ε ω) (ε ^ (-b)) * (ε * K)
  let G : ℝ → Set Ω := fun ε => {ω | 0 ≤ ε}
  have hG : ProbTendsToOne P G := by
    unfold ProbTendsToOne
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : 0 < ε := hε
    simp [G, hp.le]
  have hCₕ : 0 ≤ Cₕ := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [Cₕ, C]
    positivity
  have hgood : TendsToOneOn P E (fun ε => {ω |
      0 ≤ H ε ω ∧ H ε ω ≤ Cₕ * (1 + |Real.log ε|) ^ 3 + 2 ∧
      0 ≤ R ε ω ∧ R ε ω ≤ E₁ * ε ^ q ∧
      0 ≤ D ε ω ∧ D ε ω ≤ E₂ * ε ^ d}) := by
    unfold TendsToOneOn at hpoly ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpoly
      (Eventually.of_forall fun _ => zero_le) ?_
    apply Eventually.of_forall
    intro ε
    apply measure_mono
    rintro ω ⟨hE, hbad⟩
    refine ⟨hE, ?_⟩
    intro h
    apply hbad
    have hH : 0 ≤ H ε ω := by dsimp [H]; positivity
    exact ⟨hH, le_rfl, h⟩
  have hx : ∀ a : ℝ, 0 < a → TendsToOneOn P E (fun ε => {ω | x ε ω ≤ a}) :=
    tendsToOneOn_rescaled_maximum_with_mesh_floor P E O hK.le hb1 G hG hsmall
  have hxnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ x ε ω := by
    intro ε ω hε
    exact mul_nonneg (le_max_of_le_right (Real.rpow_nonneg hε _))
      (mul_nonneg hε hK.le)
  have hbudget := tendsToOneOn_dyadic_budget_and_errors_of_cubic_horizon P E x r₀ H R D
    hα hc (show 0 ≤ 2 / s + 2 by positivity) hT hq hd hCₕ G hG hxnonneg hx hr₀ hgood δ hδ
  apply tendsToOneOn_exists_dyadic_horizon_with_budget P E O r₀ R D hK hb hb1.le hα hc hs
    (hsmall 1 (by norm_num))
  simpa only [x, H, Cₕ, A, C] using hbudget

end MatedCRT.Sec7
