import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.BallExtension
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestHolderApprox

/-!
# Lemma 3.4: a countable Hölder family on a ball

For the environment-dependent fixed-time step, a test function that is Hölder on the ball `B(z, r)`, with constants
depending on the environment, must be approximated uniformly on `B(z, r)` by one member of a single sequence of
bounded continuous functions on `ℂ`. The sequence is built from the countable approximation families
`exists_countable_holderWith_approx_ball`, indexed by the integer Hölder constant `n` and the exponent `1/(k+1)`:
on a bounded ball every Hölder exponent `χ` can be lowered to some `1/(k+1) ≤ χ` (Mathlib's `HolderOnWith.of_le`),
and every real constant raised to an integer. The members are transported to `ℂ` by `extendClosedBall`.

Terminology: Hölder regularity on a bounded set; quantitative Hölder approximation (Armstrong–Kuusi–Mourrat).
-/

namespace MatedCRT

open Metric Set Topology
open scoped NNReal ENNReal

/-- The Hölder exponent `1/(k+1)` of index `k`. -/
noncomputable def holderIndexExp (k : ℕ) : ℝ≥0 := 1 / ((k : ℝ≥0) + 1)

lemma holderIndexExp_pos (k : ℕ) : 0 < holderIndexExp k := by
  unfold holderIndexExp
  positivity

lemma holderIndexExp_le_one (k : ℕ) : holderIndexExp k ≤ 1 := by
  unfold holderIndexExp
  exact (div_le_one (by positivity)).2 (le_add_of_nonneg_left zero_le)

/-- Every positive Hölder exponent dominates some `1/(k+1)`. -/
lemma exists_holderIndexExp_le {χ : ℝ≥0} (hχ : 0 < χ) : ∃ k : ℕ, holderIndexExp k ≤ χ := by
  refine ⟨⌈(χ : ℝ)⁻¹⌉₊, ?_⟩
  have hχr : (0 : ℝ) < χ := by exact_mod_cast hχ
  have h1 : (χ : ℝ)⁻¹ ≤ ((⌈(χ : ℝ)⁻¹⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : (1 : ℝ) ≤ (χ : ℝ) * ((⌈(χ : ℝ)⁻¹⌉₊ : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left h1 hχr.le
    rwa [mul_inv_cancel₀ hχr.ne'] at this
  rw [← NNReal.coe_le_coe]
  unfold holderIndexExp
  push_cast
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Enlarging the Hölder constant keeps the Hölder property. -/
lemma holderOnWith_mono_const {A B s : ℝ≥0} {E : Set ℂ} {g : ℂ → ℝ} (hAB : A ≤ B)
    (h : HolderOnWith A s g E) : HolderOnWith B s g E := fun x hx y hy =>
  (h x hx y hy).trans (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.2 hAB) zero_le)

/-- The Hölder constant can be taken to be a natural number. -/
lemma exists_natCast_holderOnWith {s : ℝ≥0} {E : Set ℂ} {g : ℂ → ℝ} {A : ℝ≥0}
    (h : HolderOnWith A s g E) : ∃ n : ℕ, HolderOnWith (n : ℝ≥0) s g E := by
  obtain ⟨n, hn⟩ := exists_nat_ge A
  exact ⟨n, holderOnWith_mono_const hn h⟩

/-- Two points of the open ball `B(z, r)` are at distance at most `2r`. -/
lemma edist_le_two_r_of_mem_ball {z : ℂ} {r : ℝ} (_hr : 0 < r) {x y : ℂ} (hx : x ∈ ball z r)
    (hy : y ∈ ball z r) : edist x y ≤ ((Real.toNNReal (2 * r) : ℝ≥0) : ℝ≥0∞) := by
  rw [mem_ball] at hx hy
  have h : dist x y ≤ 2 * r := by linarith [dist_triangle x z y, dist_comm z y]
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h

/-- **Countable Hölder family on a ball.** For `δ > 0` there is a sequence of bounded continuous functions on `ℂ`,
each Hölder on the ball `B(z, r)`, such that every function that is Hölder on the ball (with some constants and
exponent) is uniformly within `δ` of a member of the sequence on the ball. -/
theorem exists_holder_family_ball (z : ℂ) {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : ℕ → ℂ → ℝ, (∀ j, Continuous (G j) ∧ (∃ M : ℝ, ∀ x, |G j x| ≤ M) ∧
        ∃ (C χ : ℝ≥0), 0 < χ ∧ χ ≤ 1 ∧ HolderOnWith C χ (G j) (ball z r)) ∧
      ∀ f : ℂ → ℝ, (∃ (C χ : ℝ≥0), 0 < χ ∧ HolderOnWith C χ f (ball z r)) →
        ∃ j, ∀ x ∈ ball z r, |f x - G j x| < δ := by
  choose D hDc hDH hDapp using fun p : ℕ × ℕ =>
    exists_countable_holderWith_approx_ball (z := z) hr (C := (p.1 : ℝ≥0))
      (χ := holderIndexExp p.2) (holderIndexExp_pos p.2)
  have hzeroH : ∀ C χ : ℝ≥0, HolderOnWith C χ (fun _ : ℂ => (0 : ℝ)) (ball z r) :=
    fun C χ x _ y _ => by simp
  have hne : ∀ p : ℕ × ℕ, (D p).Nonempty := by
    intro p
    obtain ⟨G, hG, -⟩ := hDapp p (fun _ => (0 : ℝ)) (hzeroH _ _) 1 one_pos
    exact ⟨G, hG⟩
  set U : Set C(closedBall z r, ℝ) := ⋃ p : ℕ × ℕ, D p with hU
  have hUc : U.Countable := Set.countable_iUnion fun p => hDc p
  have hUne : U.Nonempty := by
    obtain ⟨G, hG⟩ := hne (0, 0)
    exact ⟨G, mem_iUnion.2 ⟨(0, 0), hG⟩⟩
  obtain ⟨g, hg⟩ := hUc.exists_eq_range hUne
  refine ⟨fun j => extendClosedBall z r hr (g j), fun j => ?_, fun f hf => ?_⟩
  · have hmem : g j ∈ U := by
      rw [hg]
      exact mem_range_self j
    obtain ⟨p, hp⟩ := mem_iUnion.1 hmem
    have hH := hDH p (g j) hp
    exact ⟨continuous_extendClosedBall hr (g j), exists_bound_extendClosedBall hr (g j),
      (p.1 : ℝ≥0), holderIndexExp p.2, holderIndexExp_pos p.2, holderIndexExp_le_one p.2,
      holderOnWith_extendClosedBall hr (g j) hH⟩
  · obtain ⟨C0, χ0, hχ0, hf0⟩ := hf
    obtain ⟨k, hk⟩ := exists_holderIndexExp_le hχ0
    have hw := HolderOnWith.of_le (fun x hx y hy => edist_le_two_r_of_mem_ball hr hx hy) hf0 hk
    obtain ⟨n, hn⟩ := exists_natCast_holderOnWith hw
    obtain ⟨G, hG, hGapp⟩ := hDapp (n, k) f hn δ hδ
    have hGU : G ∈ U := mem_iUnion.2 ⟨(n, k), hG⟩
    rw [hg] at hGU
    obtain ⟨j, hj⟩ := hGU
    refine ⟨j, fun x hx => ?_⟩
    show |f x - extendClosedBall z r hr (g j) x| < δ
    rw [extendClosedBall_of_mem hr (g j) (ball_subset_closedBall hx), hj]
    exact hGapp x hx

end MatedCRT
