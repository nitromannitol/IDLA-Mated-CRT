import MatedCRT.Proofs.WalkPotential.Markov

/-!
# The probability of exiting a set before hitting a subset

For vertex sets `B, L ⊆ ℤ` of a multigraph `m` on `ℤ`, `exitBeforeHitProb m B L b` is the probability
`P^b[τ_B < σ_{B \ L}]` that simple random walk started at `b` exits `B` before hitting `B \ L` (Lemma 7.3, line 3021).
It equals `1` off `B` and `0` on `B \ L`, and it is harmonic, `∑_{c ∼ a} m(a,c) (p(c) - p(a)) = 0`, at the vertices
`a ∈ B ∩ L` of finite positive degree (Markov property at the first step).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open Classical in
theorem lt_vExitTime_iff {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} :
    (n : ℕ∞) < vExitTime A x ↔ ∀ k ≤ n, x k ∈ A := by
  unfold vExitTime
  split_ifs with h
  · rw [ENat.natCast_lt_natCast, Nat.lt_find_iff]
    simp only [not_not]
  · simp only [not_exists, not_not] at h
    simp [h]

open Classical in
theorem vExitTime_eq_coe_iff {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} :
    vExitTime A x = n ↔ x n ∉ A ∧ ∀ k < n, x k ∈ A := by
  unfold vExitTime
  split_ifs with h
  · rw [ENat.natCast_inj, Nat.find_eq_iff]
    simp only [not_not]
  · simp only [not_exists, not_not] at h
    simp [h]

/-- The walk exits `B` before hitting `B \ L` iff at some time it is outside `B`, having stayed in `B ∩ L` before. -/
theorem vExitTime_lt_vHitTime_iff {B L : Set ℤ} {x : ℕ → ℤ} :
    vExitTime B x < vHitTime (B \ L) x ↔ ∃ n, x n ∉ B ∧ ∀ k < n, x k ∈ B ∩ L := by
  unfold vHitTime
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt h)
    rw [← hn] at h
    obtain ⟨hxn, hlt⟩ := vExitTime_eq_coe_iff.1 hn.symm
    have h2 := lt_vExitTime_iff.1 h
    refine ⟨n, hxn, fun k hk => ⟨hlt k hk, ?_⟩⟩
    by_contra hL
    exact h2 k hk.le ⟨hlt k hk, hL⟩
  · rintro ⟨n, hxn, hlt⟩
    have h1 : vExitTime B x = n := vExitTime_eq_coe_iff.2 ⟨hxn, fun k hk => (hlt k hk).1⟩
    rw [h1]
    refine lt_vExitTime_iff.2 fun k hk => ?_
    rcases hk.lt_or_eq with hk | rfl
    · exact fun hBL => hBL.2 (hlt k hk).2
    · exact fun hBL => hxn hBL.1

theorem measurableSet_exitBeforeHit (B L : Set ℤ) :
    MeasurableSet {x : ℕ → ℤ | vExitTime B x < vHitTime (B \ L) x} := by
  have : {x : ℕ → ℤ | vExitTime B x < vHitTime (B \ L) x} =
      ⋃ n : ℕ, ((fun x : ℕ → ℤ => x n) ⁻¹' Bᶜ ∩
        ⋂ k ∈ Finset.range n, (fun x : ℕ → ℤ => x k) ⁻¹' (B ∩ L)) := by
    ext x
    rw [mem_ofPred_eq, vExitTime_lt_vHitTime_iff]
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_compl_iff, mem_iInter, Finset.mem_range]
  rw [this]
  refine MeasurableSet.iUnion fun n => ?_
  refine (measurable_pi_apply n (Set.to_countable _).measurableSet).inter ?_
  exact Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply k (Set.to_countable _).measurableSet

theorem pathCons_mem_exitBeforeHit {B L : Set ℤ} {a : ℤ} (ha : a ∈ B ∩ L) (x : ℕ → ℤ) :
    vExitTime B (pathCons a x) < vHitTime (B \ L) (pathCons a x) ↔ vExitTime B x < vHitTime (B \ L) x := by
  rw [vExitTime_lt_vHitTime_iff, vExitTime_lt_vHitTime_iff]
  constructor
  · rintro ⟨n, hn, hlt⟩
    cases n with
    | zero => exact absurd ha.1 hn
    | succ n => exact ⟨n, hn, fun k hk => hlt (k + 1) (by omega)⟩
  · rintro ⟨n, hn, hlt⟩
    refine ⟨n + 1, hn, fun k hk => ?_⟩
    cases k with
    | zero => exact ha
    | succ k => exact hlt k (by omega)

/-- The probability `P^b[τ_B < σ_{B \ L}]` that simple random walk started at `b` exits `B` before hitting `B \ L`. -/
noncomputable def exitBeforeHitProb (m : ℤ → ℤ → ℕ) (B L : Set ℤ) (b : ℤ) : ℝ :=
  (srwLaw m b {x | vExitTime B x < vHitTime (B \ L) x}).toReal

theorem exitBeforeHitProb_nonneg (m : ℤ → ℤ → ℕ) (B L : Set ℤ) (b : ℤ) : 0 ≤ exitBeforeHitProb m B L b :=
  ENNReal.toReal_nonneg

/-- Started outside `B`, the walk exits `B` at time `0`. -/
theorem exitBeforeHitProb_eq_one (m : ℤ → ℤ → ℕ) {B : Set ℤ} (L : Set ℤ) {a : ℤ} (ha : a ∉ B) :
    exitBeforeHitProb m B L a = 1 := by
  unfold exitBeforeHitProb
  have h : srwLaw m a {x | vExitTime B x < vHitTime (B \ L) x}ᶜ = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (srwLaw_ae_start m a))
    intro x hx
    rw [mem_ofPred_eq]
    intro hx0
    rw [mem_compl_iff] at hx
    apply hx
    rw [mem_ofPred_eq, vExitTime_lt_vHitTime_iff]
    exact ⟨0, by rw [hx0]; exact ha, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  rw [(prob_compl_eq_zero_iff (measurableSet_exitBeforeHit B L)).1 h, ENNReal.toReal_one]

/-- Started in `B \ L`, the walk hits `B \ L` at time `0`, before exiting `B`. -/
theorem exitBeforeHitProb_eq_zero (m : ℤ → ℤ → ℕ) {B L : Set ℤ} {a : ℤ} (haB : a ∈ B) (haL : a ∉ L) :
    exitBeforeHitProb m B L a = 0 := by
  unfold exitBeforeHitProb
  have h : srwLaw m a {x | vExitTime B x < vHitTime (B \ L) x} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (srwLaw_ae_start m a))
    intro x hx
    rw [mem_ofPred_eq]
    intro hx0
    rw [mem_ofPred_eq, vExitTime_lt_vHitTime_iff] at hx
    obtain ⟨n, hn, hlt⟩ := hx
    cases n with
    | zero => exact hn (by rw [hx0]; exact haB)
    | succ n => exact haL (by rw [← hx0]; exact (hlt 0 (Nat.succ_pos n)).2)
  rw [h, ENNReal.toReal_zero]

/-- The first-step decomposition of `P^a[τ_B < σ_{B \ L}]` at `a ∈ B ∩ L`. -/
theorem srwLaw_exitBeforeHit_eq_sum {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {B L : Set ℤ} {a : ℤ}
    (ha : a ∈ B ∩ L) (hdeg : mdeg m a ≠ 0) :
    srwLaw m a {x | vExitTime B x < vHitTime (B \ L) x} = ((mdeg m a : ℝ≥0∞))⁻¹ *
      ∑ b ∈ nbrs hlf a, (m a b : ℝ≥0∞) * srwLaw m b {x | vExitTime B x < vHitTime (B \ L) x} := by
  rw [srwLaw_apply_eq_lintegral m a (measurableSet_exitBeforeHit B L)]
  have hpre : pathCons a ⁻¹' {x : ℕ → ℤ | vExitTime B x < vHitTime (B \ L) x} =
      {x | vExitTime B x < vHitTime (B \ L) x} := Set.ext fun x => pathCons_mem_exitBeforeHit ha x
  rw [hpre, lintegral_srwStep hlf hdeg]

/-- `P^·[τ_B < σ_{B \ L}]` is harmonic at the vertices of `B ∩ L` of positive degree. -/
theorem lapSum_exitBeforeHitProb {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {B L : Set ℤ} {a : ℤ}
    (ha : a ∈ B ∩ L) (hdeg : mdeg m a ≠ 0) : lapSum hlf (exitBeforeHitProb m B L) a = 0 := by
  have h := congrArg ENNReal.toReal (srwLaw_exitBeforeHit_eq_sum hlf ha hdeg)
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun b _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have hD : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast hdeg
  unfold lapSum exitBeforeHitProb
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [← mdeg_cast_eq hlf a, h, mul_inv_cancel_left₀ hD, sub_self]

end MatedCRT
