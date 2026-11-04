import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicTestRadius
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusChoice

/-! Dyadic shell stopping for the one-step-delayed radius choice. -/

namespace MatedCRT.Sec7

/-- The delayed radius choice and the logarithmic survival estimate imply a
threshold crossing within the spatial budget, provided the displayed dyadic
radius and time budgets fit. -/
theorem exists_threshold_of_delayed_dyadic_bootstrap
    (O : ℕ → ℝ) (S K α F s c D B δ : ℝ) (n N : ℕ)
    (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) (hF : 0 ≤ F)
    (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 < c) (hD : 0 ≤ D)
    (h0 : O 0 ≤ S) (hO : ∀ k ≤ n, 0 ≤ O k)
    (htarget : S * (1 / 2 : ℝ) ^ N ≤ B)
    (hcut : ∀ k < n, (∀ i < k, O (i + 1) ≤ O i) →
      (c / 8) * delayedShellRadius O K α F k ≤ 1)
    (hstep : ∀ k < n, B < O k →
      (∑ j ∈ Finset.range k, delayedShellRadius O K α F j) +
        ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ O j) →
      O (k + 1) ≤ (1 - s / (1 +
        |Real.log ((c / 8) * delayedShellRadius O K α F k)|) ^ 2) * O k)
    (hbudget :
      let a := (c / 8) * (S * K * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      let C := 2 / s + 2
      let A := 1 + |Real.log a|
      let L := |Real.log q|
      let H := (N : ℝ) * C * (A + L * (N : ℝ)) ^ 2
      delayedShellRadius O K α F 0 +
        ((S * K) ^ α * C * ((A + L) ^ 2 *
          ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) + F * H) +
        (H + 1) * (2 * D) ≤ δ)
    (hn :
      let a := (c / 8) * (S * K * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      (N : ℝ) * (2 / s + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, delayedShellRadius O K α F j) +
        ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  let r := delayedShellRadius O K α F
  let a := (c / 8) * (S * K * (1 / 2 : ℝ)) ^ α
  let q := (1 / 2 : ℝ) ^ α
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hr := delayedShellRadius_bounds O K α F
  apply exists_shell_threshold_of_dyadic_budget_bootstrap O r
    (fun k => (c / 8) * r k) S K α F s a q D B δ n N
    hS hK.le hα hF hs hs1 ha hq hD h0 hO
    (fun k _ => hF.trans (hr.2.2 k)) htarget ?_ ?_ hstep hbudget hn
  · intro j k hk hprev hactive
    exact dyadic_test_radius_bounds_of_shifted_radii O r S K α c j k
      hS.le hK.le hα.le hc.le (fun i hi => hO i (by omega)) hr.1
      (fun i _ => hr.2.1 i) hprev hactive.le (hcut k hk hprev)
  · intro k _
    exact le_of_eq (delayedShellRadius_succ O K α F k)

end MatedCRT.Sec7
