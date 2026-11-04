import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity

/-!
# Monotonicity of normalized exit time

The normalized exit time grows with a finite domain, by the maximum
principle and the first-step Green-function equations.
-/

namespace MatedCRT

open Set

/-- A normalized exit time killed on a finite vertex set is bounded by the
one killed on a larger finite set. -/
theorem normExitTime_mono_of_firstStep {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B)
    (hfirstA : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (hfirstB : ∀ b, ∀ a ∈ B,
      mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0))
    (a : ℤ) : normExitTime m A a ≤ normExitTime m B a := by
  let f : ℤ → ℝ := fun x => normExitTime m A x + (-1) * normExitTime m B x
  have hf0 : ∀ x ∉ A, f x ≤ 0 := by
    intro x hx
    simp only [f, normExitTime_eq_zero_of_not_mem m hx, zero_add, neg_one_mul]
    exact neg_nonpos.2 (normExitTime_nonneg _ _ _)
  have hfsub : ∀ x ∈ A, 0 ≤ mLaplacian m f x := by
    intro x hx
    dsimp [f]
    rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul,
      normExitTime_laplacian_of_firstStep hlf hA hfirstA x hx,
      normExitTime_laplacian_of_firstStep hlf hB hfirstB x (hAB hx)]
    ring_nf
    exact le_refl 0
  have h := le_zero_of_subharmonic_of_nonpos_off hcons hlf hA hf0 hfsub a
  dsimp [f] at h
  linarith

end MatedCRT
