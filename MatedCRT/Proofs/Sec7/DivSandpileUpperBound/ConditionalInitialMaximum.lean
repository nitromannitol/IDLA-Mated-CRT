import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalDyadicBudget

/-! A polynomial floor for the initial boundary maximum. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Adding the threshold `ε⁻ᵇ`, with `b < 1`, to an initial odometer maximum
preserves its qualitative mesh-normalized convergence to zero. -/
theorem tendsToOneOn_rescaled_maximum_with_mesh_floor
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (O : ℝ → Ω → ℝ) {K b : ℝ} (hK : 0 ≤ K) (hb : b < 1)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | ε * O ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω |
      max (O ε ω) (ε ^ (-b)) * (ε * K) ≤ a}) := by
  intro a ha
  let d := a / (2 * (K + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hs := (probTendsToOne_compl_union_iff P F (fun ε => {ω | ε * O ε ω ≤ d})).2
    (hsmall d hd)
  have hpow : Tendsto (fun ε : ℝ => ε ^ (1 - b) * K) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_rpow_nhdsGT_zero (sub_pos.mpr hb)).mul_const K
  have hfloor : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 - b) * K < a / 2 :=
    hpow.eventually (eventually_lt_nhds (by positivity))
  apply (probTendsToOne_compl_union_iff P F _).1
  apply (hG.inter hs).mono_ev
  filter_upwards [self_mem_nhdsWithin, hfloor] with ε hε hf ω hω
  rcases hω.2 with hF | hO
  · exact Or.inl hF
  · right
    change ε * O ε ω ≤ d at hO
    have h1 : O ε ω * (ε * K) ≤ a := by
      have hh := mul_le_mul_of_nonneg_right hO hK
      have hdK : d * K ≤ a := by
        dsimp [d]
        have hden : 0 < 2 * (K + 1) := by positivity
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith
      nlinarith
    have heq : ε ^ (-b) * (ε * K) = ε ^ (1 - b) * K := by
      rw [← mul_assoc, ← Real.rpow_add_one (ne_of_gt hε)]
      congr 1
      ring
    have h2 : ε ^ (-b) * (ε * K) ≤ a := by rw [heq]; linarith
    change max (O ε ω) (ε ^ (-b)) * (ε * K) ≤ a
    rw [max_mul_of_nonneg _ _ (mul_nonneg hε.le hK)]
    exact max_le h1 h2

/-- A positive polynomial floor can be included in the initial maximum while
retaining the logarithmic dyadic radius-budget estimate. -/
theorem tendsToOneOn_floored_initial_log_budget
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (O : ℝ → Ω → ℝ) {K b α c : ℝ} (hK : 0 ≤ K) (hb : b < 1)
    (hα : 0 < α) (hc : 0 < c) (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hε : ∀ ε ω, ω ∈ G ε → 0 ≤ ε)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω | ε * O ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P F (fun ε => {ω |
      let x := max (O ε ω) (ε ^ (-b)) * (ε * K)
      x ^ α * (1 + |Real.log ((c / 8) * (x * (1 / 2 : ℝ)) ^ α)| +
        |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 ≤ a}) := by
  apply tendsToOneOn_delayed_dyadic_initial_log_budget P F
    (fun ε ω => max (O ε ω) (ε ^ (-b)) * (ε * K)) hα hc G hG
  · intro ε ω hω
    exact mul_nonneg (le_max_of_le_right (Real.rpow_nonneg (hε ε ω hω) _))
      (mul_nonneg (hε ε ω hω) hK)
  · exact tendsToOneOn_rescaled_maximum_with_mesh_floor P F O hK hb G hG hsmall

end MatedCRT.Sec7
