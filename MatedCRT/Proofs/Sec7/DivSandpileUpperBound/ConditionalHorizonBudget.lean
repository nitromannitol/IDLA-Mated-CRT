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

end MatedCRT.Sec7
