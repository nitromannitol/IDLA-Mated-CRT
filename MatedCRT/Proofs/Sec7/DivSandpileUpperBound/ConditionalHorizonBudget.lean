import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolylogBudget
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalBudgetSum

/-! Conditional polynomial errors over a logarithmic shell horizon. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- A polynomial mesh error times a random cubic-logarithmic horizon tends to
zero on an event when the required bounds hold there with high probability. -/
theorem tendsToOneOn_random_cubic_horizon_mul_error
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (H D : ℝ → Ω → ℝ) {α C E : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hgood : TendsToOneOn P F (fun ε => {ω |
      0 ≤ H ε ω ∧ H ε ω ≤ C * (1 + |Real.log ε|) ^ 3 + 2 ∧
      0 ≤ D ε ω ∧ D ε ω ≤ E * ε ^ α})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | (H ε ω + 1) * D ε ω ≤ a}) := by
  have hp : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) :=
    tendsto_rpow_mul_log_loss_pow hα 0 |>.congr' (by simp)
  have hl := tendsto_rpow_mul_log_loss_pow hα 3
  have hlim : Tendsto (fun ε : ℝ => E *
      (C * (ε ^ α * (1 + |Real.log ε|) ^ 3) + 3 * ε ^ α))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hl.const_mul C).add (hp.const_mul 3)).const_mul E
  intro a ha
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      E * (C * (ε ^ α * (1 + |Real.log ε|) ^ 3) + 3 * ε ^ α) < a :=
    hlim.eventually (eventually_lt_nhds ha)
  unfold TendsToOneOn at hgood ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgood
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, hevent] with ε hε hevent
  apply measure_mono
  rintro ω ⟨hF, hbad⟩
  refine ⟨hF, ?_⟩
  rintro ⟨hH0, hH, hD0, hD⟩
  apply hbad
  change (H ε ω + 1) * D ε ω ≤ a
  have hbound : 0 ≤ C * (1 + |Real.log ε|) ^ 3 + 3 := by positivity
  have hmul := mul_le_mul (show H ε ω + 1 ≤ C * (1 + |Real.log ε|) ^ 3 + 3 by linarith)
    hD hD0 hbound
  nlinarith


/-- The floor and cell-diameter contributions both vanish when they are
polynomially bounded on the same cubic-logarithmic horizon event. -/
theorem tendsToOneOn_random_dyadic_horizon_budgets
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (H R D : ℝ → Ω → ℝ) {q d C E₁ E₂ : ℝ}
    (hq : 0 < q) (hd : 0 < d) (hC : 0 ≤ C)
    (hgood : TendsToOneOn P F (fun ε => {ω |
      0 ≤ H ε ω ∧ H ε ω ≤ C * (1 + |Real.log ε|) ^ 3 + 2 ∧
      0 ≤ R ε ω ∧ R ε ω ≤ E₁ * ε ^ q ∧
      0 ≤ D ε ω ∧ D ε ω ≤ E₂ * ε ^ d})) :
    (∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | R ε ω * H ε ω ≤ a})) ∧
    (∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω |
      (H ε ω + 1) * (2 * D ε ω) ≤ a})) := by
  have hR : TendsToOneOn P F (fun ε => {ω |
      0 ≤ H ε ω ∧ H ε ω ≤ C * (1 + |Real.log ε|) ^ 3 + 2 ∧
      0 ≤ R ε ω ∧ R ε ω ≤ E₁ * ε ^ q}) := by
    unfold TendsToOneOn at hgood ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgood
      (Eventually.of_forall fun _ => zero_le) ?_
    apply Eventually.of_forall
    intro ε
    apply measure_mono
    rintro ω ⟨hF, hbad⟩
    exact ⟨hF, fun h => hbad ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩
  have hD : TendsToOneOn P F (fun ε => {ω |
      0 ≤ H ε ω ∧ H ε ω ≤ C * (1 + |Real.log ε|) ^ 3 + 2 ∧
      0 ≤ D ε ω ∧ D ε ω ≤ E₂ * ε ^ d}) := by
    unfold TendsToOneOn at hgood ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgood
      (Eventually.of_forall fun _ => zero_le) ?_
    apply Eventually.of_forall
    intro ε
    apply measure_mono
    rintro ω ⟨hF, hbad⟩
    exact ⟨hF, fun h => hbad ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  have hRlim := tendsToOneOn_random_cubic_horizon_mul_error P F H R hq hC hR
  have hDlim := tendsToOneOn_random_cubic_horizon_mul_error P F H D hd hC hD
  constructor
  · intro a ha
    have h := tendsToOneOn_inter P F _ _ (hRlim a ha) hR
    unfold TendsToOneOn at h ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) ?_
    apply Eventually.of_forall
    intro ε
    apply measure_mono
    rintro ω ⟨hF, hbad⟩
    refine ⟨hF, ?_⟩
    rintro ⟨hbound, _, _, hnonneg, _⟩
    apply hbad
    change (H ε ω + 1) * R ε ω ≤ a at hbound
    change 0 ≤ R ε ω at hnonneg
    change R ε ω * H ε ω ≤ a
    nlinarith
  · intro a ha
    have h := hDlim (a / 2) (by positivity)
    unfold TendsToOneOn at h ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) ?_
    apply Eventually.of_forall
    intro ε
    apply measure_mono
    rintro ω ⟨hF, hbad⟩
    refine ⟨hF, ?_⟩
    intro hbound
    apply hbad
    change (H ε ω + 1) * D ε ω ≤ a / 2 at hbound
    change (H ε ω + 1) * (2 * D ε ω) ≤ a
    nlinarith


/-- Initial-radius control and a polynomial bound on the floor and diameter
on a cubic-logarithmic horizon give the complete dyadic spatial budget. -/
theorem tendsToOneOn_dyadic_budget_of_cubic_horizon
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
      r₀ ε ω + (x ε ω ^ α * C *
        ((1 + |Real.log ((c / 8) * (x ε ω * (1 / 2 : ℝ)) ^ α)| +
          |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 * T) + R ε ω * H ε ω) +
        (H ε ω + 1) * (2 * D ε ω) ≤ a}) := by
  obtain ⟨hfloor, hdiam⟩ :=
    tendsToOneOn_random_dyadic_horizon_budgets P F H R D hq hd hCₕ hgood
  exact tendsToOneOn_delayed_dyadic_total_budget P F x r₀
    (fun ε ω => R ε ω * H ε ω) (fun ε ω => (H ε ω + 1) * (2 * D ε ω))
    hα hc hC hT G hG hxnonneg hx hr₀ hfloor hdiam

end MatedCRT.Sec7
