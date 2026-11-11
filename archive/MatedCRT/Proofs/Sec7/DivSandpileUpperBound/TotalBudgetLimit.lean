import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogBudgetLimit
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolylogBudget

/-! Vanishing of the complete logarithmic shell budget. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- Polynomial initial radii, radius floors, and cell diameters make the
complete spatial budget vanish over a polylogarithmic shell horizon. -/
theorem tendsto_total_log_shell_budget
    {α₀ α₁ α₂ α₃ β ω A s C C₀ C₁ C₂ C₃ : ℝ}
    (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hα₃ : 0 < α₃)
    (hβ : 0 < β) (hA : 0 < A) (hs : 0 < s) (hs1 : s ≤ 1)
    (horizon : ℝ → ℕ)
    (hbound : ∀ᶠ ε in 𝓝[>] 0, (horizon ε : ℝ) ≤
      C * (1 + |Real.log (A * ε ^ ω)|) ^ 3) :
    Tendsto (fun ε : ℝ => C₀ * ε ^ α₀ + C₁ *
      (ε ^ α₁ / (1 - (1 - s / (1 + |Real.log (A * ε ^ ω)|) ^ 2) ^ β)) +
      C₂ * ((horizon ε : ℝ) * ε ^ α₂) +
      2 * C₃ * ((horizon ε : ℝ) * ε ^ α₃ + ε ^ α₃))
      (𝓝[>] 0) (𝓝 0) := by
  have hp (α : ℝ) (hα : 0 < α) :
      Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using h.mono_left nhdsWithin_le_nhds
  have h₀ := (hp α₀ hα₀).const_mul C₀
  have h₁ := (tendsto_log_shell_radius_budget (ω := ω) hα₁ hβ hA hs hs1).const_mul C₁
  have h₂ := (tendsto_polylog_horizon_mul_rpow hα₂ hA 3 horizon hbound).const_mul C₂
  have h₃ := ((tendsto_polylog_horizon_mul_rpow hα₃ hA 3 horizon hbound).add
    (hp α₃ hα₃)).const_mul (2 * C₃)
  simpa using ((h₀.add h₁).add h₂).add h₃

end MatedCRT.Sec7
