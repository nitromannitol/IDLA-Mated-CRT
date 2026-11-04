import MatedCRT.Proofs.Sec5.MeanValueInequality.ObstacleComparison

/-!
# Finite-volume Green-function bounds for Lemma 5.4

The diagonal is positive, and the killed Green function increases with the
domain.  These statements follow from the first-step equation and the finite
maximum principle, without comparing real-valued infinite expectations.
-/

namespace MatedCRT

open Set

/-- Green functions are nonnegative even under the `toReal` convention. -/
theorem greenFn_nonnegative (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) :
    0 ≤ greenFn m A a b := ENNReal.toReal_nonneg

/-- The diagonal Green function is strictly positive at a vertex satisfying
the first-step equation. -/
theorem greenFn_diag_pos_of_firstStep {m : ℤ → ℤ → ℕ} {A : Set ℤ} {a : ℤ} (ha : a ∈ A)
    (hfirst : ∀ b, ∀ x ∈ A,
      mLaplacian m (fun y => greenFn m A y b) x = -(if x = b then 1 else 0)) :
    0 < greenFn m A a a := by
  have hn := greenFn_nonnegative m A a a
  by_contra h
  have hz : greenFn m A a a = 0 := le_antisymm (not_lt.1 h) hn
  have hsub : 0 ≤ mLaplacian m (fun y => greenFn m A y a) a := by
    unfold mLaplacian
    dsimp only
    rw [hz]
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (finsum_nonneg fun b => ?_)
    rw [sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (greenFn_nonnegative m A b a)
  rw [hfirst a a ha] at hsub
  norm_num at hsub

/-- A Green function killed on `A` is dominated by that killed on the larger
finite domain `B`, provided both satisfy their first-step equations. -/
theorem greenFn_mono_of_firstStep {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hAB : A ⊆ B)
    (hfirstA : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (hfirstB : ∀ b, ∀ a ∈ B,
      mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0))
    (x b : ℤ) : greenFn m A x b ≤ greenFn m B x b := by
  let f : ℤ → ℝ := fun y => greenFn m A y b + (-1) * greenFn m B y b
  have hf0 : ∀ y ∉ A, f y ≤ 0 := by
    intro y hy
    simp only [f, greenFn_eq_zero_of_not_mem m hy b, zero_add, neg_one_mul]
    exact neg_nonpos.2 (greenFn_nonnegative m B y b)
  have hsub : ∀ y ∈ A, 0 ≤ mLaplacian m f y := by
    intro y hy
    dsimp [f]
    rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul,
      hfirstA b y hy, hfirstB b y (hAB hy)]
    ring_nf
    exact le_refl 0
  have h := le_zero_of_subharmonic_of_nonpos_off hcons hlf hA hf0 hsub x
  dsimp [f] at h
  linarith

end MatedCRT
