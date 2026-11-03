import MatedCRT.Proofs.WalkPotential.ExitBeforeHit
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-!
# Harmonic comparison with the probability of exiting before hitting

Let `m` be a locally finite multigraph on `ℤ` and `B, L ⊆ ℤ` with `B ∩ L` finite and such that an edge leaves every
nonempty subset of `B ∩ L`. If `u` vanishes on `B \ L`, is subharmonic on `B ∩ L` and is at most `M ≥ 0` on `∂B`, then
`u(b) ≤ M P^b[τ_B < σ_{B \ L}]` for all `b ∈ B` (`le_mul_exitBeforeHitProb`): the comparison of the proof of Lemma 7.3
(lines 3026-3046), by the maximum principle applied to `u - M P^·[τ_B < σ_{B \ L}]`.
-/

namespace MatedCRT

open Set

theorem lapSum_const_mul {α : Type*} {m : α → α → ℕ} (hlf : IsLocallyFiniteMult m) (c : ℝ) (v : α → ℝ) (a : α) :
    lapSum hlf (fun b => c * v b) a = c * lapSum hlf v a := by
  simp only [lapSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Harmonic comparison** (proof of Lemma 7.3, lines 3026-3046). -/
theorem le_mul_exitBeforeHitProb {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) {B L : Set ℤ}
    (hU : (B ∩ L).Finite) (hesc : ∀ S ⊆ B ∩ L, S.Nonempty → ∃ a ∈ S, ∃ b ∉ S, m a b ≠ 0)
    {u : ℤ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hu0 : ∀ b ∈ B \ L, u b = 0)
    (hsub : ∀ a ∈ B ∩ L, 0 ≤ mLaplacian m u a) (hbd : ∀ c ∈ vBoundary m B, u c ≤ M) :
    ∀ b ∈ B, u b ≤ M * exitBeforeHitProb m B L b := by
  intro b hb
  by_cases hbL : b ∈ L
  swap
  · rw [hu0 b ⟨hb, hbL⟩]
    exact mul_nonneg hM (exitBeforeHitProb_nonneg m B L b)
  have hsubw : ∀ a ∈ B ∩ L, 0 ≤ lapSum hlf (fun c => u c - M * exitBeforeHitProb m B L c) a := by
    intro a ha
    obtain ⟨a', ha', c, -, hac⟩ := hesc {a} (singleton_subset_iff.2 ha) (singleton_nonempty a)
    rw [mem_singleton_iff] at ha'
    subst ha'
    have hdeg := mdeg_ne_zero_of_ne_zero hlf hac
    rw [lapSum_sub hlf u (fun c => M * exitBeforeHitProb m B L c) a',
      lapSum_const_mul hlf M (exitBeforeHitProb m B L) a', lapSum_exitBeforeHitProb hlf ha hdeg, mul_zero,
      sub_zero, ← mLaplacian_mul_mdeg hlf]
    exact mul_nonneg (hsub a' ha) (Nat.cast_nonneg _)
  have hbdw : ∀ a ∈ B ∩ L, ∀ c, m a c ≠ 0 → c ∉ B ∩ L →
      (fun c => u c - M * exitBeforeHitProb m B L c) c ≤ 0 := by
    intro a ha c hac hcU
    show u c - M * exitBeforeHitProb m B L c ≤ 0
    by_cases hcB : c ∈ B
    · have hcL : c ∉ L := fun hcL => hcU ⟨hcB, hcL⟩
      rw [hu0 c ⟨hcB, hcL⟩, exitBeforeHitProb_eq_zero m hcB hcL, mul_zero, sub_zero]
    · rw [exitBeforeHitProb_eq_one m L hcB, mul_one, sub_nonpos]
      exact hbd c ⟨hcB, a, ha.1, hac⟩
  have key : u b - M * exitBeforeHitProb m B L b ≤ 0 :=
    nonpos_of_lapSum_nonneg hlf hU hesc hsubw hbdw b ⟨hb, hbL⟩
  linarith

end MatedCRT
