import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.HalvingTime

/-! Repeated halving up to a positive stopping threshold. -/

namespace MatedCRT.Sec7

/-- A fixed lower bound on the contraction rate implies threshold crossing
within `M` blocks of `N` steps whenever `M` halvings reach the threshold.
Contraction is assumed only before the threshold is crossed. -/
theorem exists_threshold_before_repeated_halvings
    (O : ℕ → ℝ) (p B : ℝ) (M N : ℕ)
    (hp : 0 < p) (hB : 0 < B) (hN : 2 < (N : ℝ) * p)
    (hO : ∀ k ≤ M * N, 0 ≤ O k)
    (hend : O 0 * (1 / 2 : ℝ) ^ M ≤ B)
    (hstep : ∀ k < M * N, B < O k → O (k + 1) ≤ (1 - p) * O k) :
    ∃ τ ≤ M * N, O τ ≤ B ∧ ∀ k < τ, B < O k := by
  have hex : ∃ k ≤ M * N, O k ≤ B := by
    by_contra h
    have habove : ∀ k ≤ M * N, B < O k := by
      intro k hk
      exact lt_of_not_ge (fun hk' => h ⟨k, hk, hk'⟩)
    have hmono : ∀ a b, a ≤ b → b ≤ M * N → O b ≤ O a := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hab ih =>
        intro hb
        have hs := hstep b (by omega) (habove b (by omega))
        have hd := mul_nonneg hp.le (hO b (by omega))
        have hnext : O (b + 1) ≤ O b := by nlinarith
        exact hnext.trans (ih (by omega))
    have hblock : ∀ j < M, O (j * N + N) ≤ O (j * N) / 2 := by
      intro j hj
      have htotal : j * N + N ≤ M * N := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right N (Nat.succ_le_of_lt hj)
      have hstart : 0 < O (j * N) := lt_trans hB (habove (j * N) (by omega))
      obtain ⟨k, hkN, hk⟩ := exists_halving_before_of_uniform_contraction
        (fun i => O (j * N + i)) p N (by simpa using hstart) hp hN (by
          intro i hi _
          simpa [Nat.add_assoc] using hstep (j * N + i) (by omega)
            (habove (j * N + i) (by omega)))
      have hm := hmono (j * N + k) (j * N + N) (by omega) htotal
      exact hm.trans hk
    have hdecay : ∀ j ≤ M, O (j * N) ≤ O 0 * (1 / 2 : ℝ) ^ j := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        calc
          O ((j + 1) * N) ≤ O (j * N) / 2 := by simpa [Nat.succ_mul] using hblock j (by omega)
          _ ≤ (O 0 * (1 / 2 : ℝ) ^ j) / 2 := by gcongr; exact ih (by omega)
          _ = O 0 * (1 / 2 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
    exact (not_lt_of_ge ((hdecay M le_rfl).trans hend)) (habove (M * N) le_rfl)
  let τ := Nat.find hex
  refine ⟨τ, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro k hk
  have hkN : k ≤ M * N := (Nat.le_of_lt hk).trans (Nat.find_spec hex).1
  exact lt_of_not_ge (fun hk' => Nat.find_min hex hk ⟨hkN, hk'⟩)

/-- With a uniform radius floor, repeated halving gives a finite stopping
horizon for the radius-dependent logarithmic contraction. -/
theorem exists_threshold_before_repeated_log_halvings
    (O r : ℕ → ℝ) (s a B : ℝ) (M N : ℕ)
    (hs : 0 < s) (ha : 0 < a) (hB : 0 < B)
    (hN : 2 * (1 + |Real.log a|) ^ 2 < (N : ℝ) * s)
    (hO : ∀ k ≤ M * N, 0 ≤ O k)
    (hr : ∀ k < M * N, a ≤ r k ∧ r k ≤ 1)
    (hend : O 0 * (1 / 2 : ℝ) ^ M ≤ B)
    (hstep : ∀ k < M * N, B < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ τ ≤ M * N, O τ ≤ B ∧ ∀ k < τ, B < O k := by
  let L := 1 + |Real.log a|
  have hL : 0 < L := by dsimp [L]; positivity
  have hLsq : 0 < L ^ 2 := by positivity
  apply exists_threshold_before_repeated_halvings O (s / L ^ 2) B M N
    (div_pos hs hLsq) hB ?_ hO hend ?_
  · rw [← mul_div_assoc, lt_div_iff₀ hLsq]
    exact hN
  · intro k hk hactive
    have hden : 0 < (1 + |Real.log (r k)|) ^ 2 := by positivity
    have hlog : 1 + |Real.log (r k)| ≤ L :=
      log_loss_le_of_radius_lower_bound ha (hr k hk).1 (hr k hk).2
    have hsq : (1 + |Real.log (r k)|) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlog 2
    have hrate : s / L ^ 2 ≤ s / (1 + |Real.log (r k)|) ^ 2 :=
      div_le_div_of_nonneg_left hs.le hden hsq
    have hmul := mul_le_mul_of_nonneg_right hrate (hO k (by omega))
    have h := hstep k hk hactive
    nlinarith

/-- A sufficiently long contraction block decreases a geometric majorant by
at least one half; repeating blocks produces a quantitative stopping horizon. -/
theorem geometric_majorant_le_of_halving_blocks
    (x p B : ℝ) (M N : ℕ) (hx : 0 ≤ x) (hp : 0 < p) (hp1 : p ≤ 1)
    (hB : 0 < B) (hN : 2 < (N : ℝ) * p)
    (hend : x * (1 / 2 : ℝ) ^ M ≤ B) :
    x * (1 - p) ^ (M * N) ≤ B := by
  let q := 1 - p
  have hq : 0 ≤ q := sub_nonneg.mpr hp1
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  let O : ℕ → ℝ := fun k => x * q ^ k
  have hO : ∀ k ≤ M * N, 0 ≤ O k := by
    intro k _
    exact mul_nonneg hx (pow_nonneg hq k)
  have hstep : ∀ k < M * N, B < O k → O (k + 1) ≤ (1 - p) * O k := by
    intro k _ _
    dsimp [O, q]
    rw [pow_succ]
    ring_nf
    exact le_rfl
  obtain ⟨τ, hτ, hsmall, _⟩ :=
    exists_threshold_before_repeated_halvings O p B M N hp hB hN hO
      (by simpa [O] using hend) hstep
  have hpow : q ^ (M * N) ≤ q ^ τ := pow_le_pow_of_le_one hq hq1 hτ
  exact (mul_le_mul_of_nonneg_left hpow hx).trans hsmall

/-- A polynomial radius floor gives a uniform logarithmic contraction rate;
halving blocks then bound the geometric majorant at a finite horizon. -/
theorem geometric_majorant_le_of_log_halving_blocks
    (x s a B : ℝ) (M N : ℕ) (hx : 0 ≤ x) (hs : 0 < s)
    (hsbound : s ≤ (1 + |Real.log a|) ^ 2)
    (hB : 0 < B) (hN : 2 * (1 + |Real.log a|) ^ 2 < (N : ℝ) * s)
    (hend : x * (1 / 2 : ℝ) ^ M ≤ B) :
    x * (1 - s / (1 + |Real.log a|) ^ 2) ^ (M * N) ≤ B := by
  have hden : 0 < (1 + |Real.log a|) ^ 2 := by positivity
  apply geometric_majorant_le_of_halving_blocks x (s / (1 + |Real.log a|) ^ 2)
    B M N hx (div_pos hs hden) ((div_le_one₀ hden).2 hsbound) hB ?_ hend
  rw [← mul_div_assoc, lt_div_iff₀ hden]
  exact hN

end MatedCRT.Sec7
