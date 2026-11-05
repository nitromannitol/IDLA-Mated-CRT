import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalHorizonBudget
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalHorizonCertificate

/-! Conditional dyadic budgets with nonnegative error terms.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Retain nonnegativity of the floor and diameter while controlling the full
spatial budget on a cubic-logarithmic horizon. -/
theorem tendsToOneOn_dyadic_budget_and_errors_of_cubic_horizon
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (x r₀ H R D : ℝ → Ω → ℝ) {α c C T q d Cₕ E₁ E₂ : ℝ}
    (hα : 0 < α) (hc : 0 < c) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hq : 0 < q) (hd : 0 < d) (hCₕ : 0 ≤ Cₕ)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hxnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ x ε ω)
    (hx : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | x ε ω ≤ a}))
    (hr₀ : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | r₀ ε ω ≤ a}))
    (hgood : TendsToOneOn P F (fun ε => {ω |
      0 ≤ H ε ω ∧ H ε ω ≤ Cₕ * (1 + |Real.log ε|) ^ 3 + 2 ∧
      0 ≤ R ε ω ∧ R ε ω ≤ E₁ * ε ^ q ∧
      0 ≤ D ε ω ∧ D ε ω ≤ E₂ * ε ^ d})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω |
      0 ≤ R ε ω ∧ 0 ≤ D ε ω ∧
      r₀ ε ω + (x ε ω ^ α * C *
        ((1 + |Real.log ((c / 8) * (x ε ω * (1 / 2 : ℝ)) ^ α)| +
          |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 * T) + R ε ω * H ε ω) +
        (H ε ω + 1) * (2 * D ε ω) ≤ a}) := by
  intro a ha
  have hbudget := tendsToOneOn_dyadic_budget_of_cubic_horizon P F x r₀ H R D
    hα hc hC hT hq hd hCₕ G hG hxnonneg hx hr₀ hgood a ha
  have hboth := tendsToOneOn_inter P F _ _ hgood hbudget
  unfold TendsToOneOn at hboth ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboth
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  rintro ω ⟨hF, hbad⟩
  refine ⟨hF, ?_⟩
  rintro ⟨h, hbudget⟩
  exact hbad ⟨h.2.2.1, h.2.2.2.2.1, hbudget⟩

end MatedCRT.Sec7
