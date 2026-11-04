import MatedCRT.Proofs.WalkPotential.GreenFirstStep

/-!
# Green representation on a finite vertex set

The zero-boundary solution of the discrete Poisson equation is the Green potential of its
source. This is the finite-set part of Lawler and Limic, Corollary 6.2.4, used in Lemma 3.5.
-/

namespace MatedCRT

open Set Classical

/-- The Green potential of `f` has discrete Laplacian `-f` on a finite set. -/
theorem mLaplacian_greenPotential {m : ℤ → ℤ → ℕ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (f : ℤ → ℝ) {a : ℤ} (ha : a ∈ A) :
    mLaplacian m (fun x => ∑ b ∈ hA.toFinset, f b * greenFn m A x b) a = -f a := by
  rw [mLaplacian_finset_sum hlf]
  have ht : ∀ b ∈ hA.toFinset,
      mLaplacian m (fun x => f b * greenFn m A x b) a =
        -(f b * if a = b then 1 else 0) := by
    intro b hb
    rw [mLaplacian_const_mul, WalkPotential.mLaplacian_greenFn hlf hcons hA b a ha]
    ring
  rw [Finset.sum_congr rfl ht, Finset.sum_neg_distrib]
  simp [mul_ite, ha]

/-- A zero-boundary solution of `Δu = -f` is the Green potential of `f`. -/
theorem eq_greenPotential_of_zero_boundary {m : ℤ → ℤ → ℕ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (f u : ℤ → ℝ)
    (hu0 : ∀ a ∉ A, u a = 0) (hu : ∀ a ∈ A, mLaplacian m u a = -f a) (a : ℤ) :
    u a = ∑ b ∈ hA.toFinset, f b * greenFn m A a b := by
  let v : ℤ → ℝ := fun x => ∑ b ∈ hA.toFinset, f b * greenFn m A x b
  have hv0 : ∀ x ∉ A, v x = 0 := by
    intro x hx
    simp [v, greenFn_eq_zero_of_not_mem m hx]
  have hv : ∀ x ∈ A, mLaplacian m v x = -f x :=
    fun x hx => mLaplacian_greenPotential hlf hcons hA f hx
  have hd : ∀ x ∈ A, mLaplacian m (fun y => u y + (-1) * v y) x = 0 := by
    intro x hx
    rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul, hu x hx, hv x hx]
    ring
  have hle := le_zero_of_subharmonic hcons hlf hA (x := fun y => u y + (-1) * v y)
    (fun x hx => by simp [hu0 x hx, hv0 x hx]) (fun x hx => (hd x hx).ge) a
  have hge := le_zero_of_subharmonic hcons hlf hA (x := fun y => (-1) * (u y + (-1) * v y))
    (fun x hx => by simp [hu0 x hx, hv0 x hx]) (fun x hx => by
      rw [mLaplacian_const_mul, hd x hx]
      norm_num) a
  change u a = v a
  linarith

/-- If `h` is harmonic on `A` and agrees with `u` outside `A`, then `u` is the sum of `h` and
the Green potential of the source. -/
theorem eq_harmonic_add_greenPotential {m : ℤ → ℤ → ℕ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (f u h : ℤ → ℝ)
    (hboundary : ∀ a ∉ A, u a = h a) (hu : ∀ a ∈ A, mLaplacian m u a = -f a)
    (hh : ∀ a ∈ A, mLaplacian m h a = 0) (a : ℤ) :
    u a = h a + ∑ b ∈ hA.toFinset, f b * greenFn m A a b := by
  have hrep := eq_greenPotential_of_zero_boundary hlf hcons hA f (fun x => u x + (-1) * h x)
    (fun x hx => by rw [hboundary x hx]; ring) (fun x hx => by
      rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul, hu x hx, hh x hx]
      ring) a
  linarith

end MatedCRT
