import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicPrefixBudget

/-! Spatial bootstrap using the radius-dependent dyadic shell budget. -/

namespace MatedCRT.Sec7

/-- The dyadic radius budget closes shell contraction up to the first
threshold crossing. The horizon is strictly larger than the dyadic time bound. -/
theorem exists_shell_threshold_of_dyadic_budget_bootstrap
    (O r u : ℕ → ℝ) (S K α F s a q D B δ : ℝ) (n N : ℕ)
    (hS : 0 < S) (hK : 0 ≤ K) (hα : 0 < α) (hF : 0 ≤ F)
    (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hq : 0 < q) (hD : 0 ≤ D)
    (h0 : O 0 ≤ S) (hO : ∀ k ≤ n, 0 ≤ O k) (hr0 : ∀ k ≤ n, 0 ≤ r k)
    (htarget : S * (1 / 2 : ℝ) ^ N ≤ B)
    (hu : ∀ j k, k < n → (∀ i < k, O (i + 1) ≤ O i) →
      S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      a * q ^ j ≤ u k ∧ u k ≤ 1)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) F)
    (hstep : ∀ k < n, B < O k →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ O j) →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (u k)|) ^ 2) * O k)
    (hbudget :
      let C := 2 / s + 2
      let A := 1 + |Real.log a|
      let L := |Real.log q|
      let H := (N : ℝ) * C * (A + L * (N : ℝ)) ^ 2
      r 0 + ((S * K) ^ α * C * ((A + L) ^ 2 *
        ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * ((1 / 2 : ℝ) ^ α) ^ j) + F * H) +
        (H + 1) * (2 * D) ≤ δ)
    (hn : (N : ℝ) * (2 / s + 2) *
      (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, r j) + ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  let C : ℝ := 2 / s + 2
  let A : ℝ := 1 + |Real.log a|
  let L : ℝ := |Real.log q|
  let H : ℝ := (N : ℝ) * C * (A + L * (N : ℝ)) ^ 2
  let G : ℝ := (S * K) ^ α * C * ((A + L) ^ 2 *
    ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * ((1 / 2 : ℝ) ^ α) ^ j)
  change r 0 + (G + F * H) + (H + 1) * (2 * D) ≤ δ at hbudget
  change H < n at hn
  have hmono : ∀ k < n,
      O (k + 1) ≤ (1 - s / (1 + |Real.log (u k)|) ^ 2) * O k →
      O (k + 1) ≤ O k := by
    intro k hk hh
    have hp : 0 ≤ s / (1 + |Real.log (u k)|) ^ 2 := by positivity
    have hm := mul_nonneg hp (hO k (by omega))
    nlinarith
  have hprefix : ∀ k ≤ n, (∀ j < k, B < O j) →
      (∀ j < k, O (j + 1) ≤ (1 - s / (1 + |Real.log (u j)|) ^ 2) * O j) ∧
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ := by
    intro k hk
    induction k with
    | zero =>
      intro _
      constructor
      · intro j hj; omega
      · have hH : 0 ≤ H := by dsimp [H, C, A, L]; positivity
        have hG : 0 ≤ G := by
          dsimp [G, C, A, L]
          apply mul_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg hS.le hK) α) (by positivity))
          apply mul_nonneg (sq_nonneg _) 
          exact tsum_nonneg (fun j => by positivity)
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add]
        nlinarith [mul_nonneg hF hH, mul_nonneg hH hD, hr0 0 (by omega)]
    | succ k ih =>
      intro habove
      obtain ⟨hprev, hcost⟩ := ih (by omega) (fun j hj => habove j (by omega))
      have hnext := hstep k (by omega) (habove k (by omega)) hcost
        (fun j hj => hmono j (by omega) (hprev j hj))
      have hsteps : ∀ j < k + 1,
          O (j + 1) ≤ (1 - s / (1 + |Real.log (u j)|) ^ 2) * O j := by
        intro j hj
        by_cases hjk : j < k
        · exact hprev j hjk
        · have : j = k := by omega
          simpa [this] using hnext
      refine ⟨hsteps, ?_⟩
      let P : ℕ → ℝ := fun j => if j < k + 1 then O j else 0
      let t := levelCrossingTimes P (fun j => S * (1 / 2 : ℝ) ^ j)
      have hb := finite_dyadic_delayed_radius_budget O r u S K α F s a q (k + 1) N
        hS hK hα hF hs hs1 ha hq h0
        (fun j i hi hactive => hu j i (by omega)
          (fun l hl => hmono l (by omega) (hsteps l (by omega))) hactive)
        (fun j i hi _ => hsteps i hi) (fun i hi => hr i (by omega))
      change t N ≤ k + 1 ∧ (O (t N) ≤ S * (1 / 2 : ℝ) ^ N ∨ t N = k + 1) ∧
        (∑ i ∈ Finset.range (t N), r (i + 1)) ≤ G + F * (t N : ℝ) ∧
        (t N : ℝ) ≤ H at hb
      have ht : t N = k + 1 := by
        rcases hb.2.1 with hcross | heq
        · by_contra hne
          have hlt : t N < k + 1 := by omega
          exact (not_lt_of_ge (hcross.trans htarget)) (habove (t N) hlt)
        · exact heq
      have hsum : (∑ i ∈ Finset.range (t N), r (i + 1)) ≤ G + F * H := by
        exact hb.2.2.1.trans (add_le_add_right (mul_le_mul_of_nonneg_left hb.2.2.2 hF) G)
      have hc := shell_prefix_budget_of_delayed_sum r (t N) D (G + F * H) H hD
        (fun i hi => hr0 i (by omega)) hb.2.2.2 hsum (k + 1) (by omega)
      exact hc.trans hbudget
  have hex : ∃ k, k ≤ n ∧ O k ≤ B := by
    by_contra h
    have habove : ∀ k ≤ n, B < O k := by
      intro k hk
      exact lt_of_not_ge (fun hh => h ⟨k, hk, hh⟩)
    have hsteps := (hprefix n le_rfl (fun j hj => habove j (by omega))).1
    let P : ℕ → ℝ := fun j => if j < n then O j else 0
    let t := levelCrossingTimes P (fun j => S * (1 / 2 : ℝ) ^ j)
    have hb := finite_dyadic_delayed_radius_budget O r u S K α F s a q n N
      hS hK hα hF hs hs1 ha hq h0
      (fun j i hi hactive => hu j i hi
        (fun l hl => hmono l (by omega) (hsteps l (by omega))) hactive)
      (fun _ i hi _ => hsteps i hi) hr
    change t N ≤ n ∧ (O (t N) ≤ S * (1 / 2 : ℝ) ^ N ∨ t N = n) ∧
      (∑ i ∈ Finset.range (t N), r (i + 1)) ≤ G + F * (t N : ℝ) ∧
      (t N : ℝ) ≤ H at hb
    have ht : t N < n := by
      have hh : (t N : ℝ) < (n : ℝ) := hb.2.2.2.trans_lt hn
      exact_mod_cast hh
    rcases hb.2.1 with hc | heq
    · exact (not_lt_of_ge (hc.trans htarget)) (habove (t N) (by omega))
    · omega
  let τ := Nat.find hex
  have hτn : τ ≤ n := (Nat.find_spec hex).1
  have hτ : O τ ≤ B := (Nat.find_spec hex).2
  have hbefore : ∀ k < τ, B < O k := by
    intro k hk
    exact lt_of_not_ge (fun hle => Nat.find_min hex hk ⟨by omega, hle⟩)
  exact ⟨τ, hτn, hτ, hbefore, (hprefix τ hτn hbefore).2⟩

end MatedCRT.Sec7
