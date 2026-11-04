import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov

/-! # Domain monotonicity of the discrete Green kernel -/

namespace MatedCRT

open Set

/-- On finite domains satisfying the first-step equations, enlarging the
domain increases the degree-normalized Green kernel. -/
theorem greenKernel_mono_of_firstStep {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hAB : A ⊆ B)
    (hfirstA : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (hfirstB : ∀ b, ∀ a ∈ B,
      mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0))
    (x b : ℤ) : greenKernel m A x b ≤ greenKernel m B x b := by
  unfold greenKernel
  exact div_le_div_of_nonneg_right
    (greenFn_mono_of_firstStep hlf hcons hA hAB hfirstA hfirstB x b) (Nat.cast_nonneg _)

/-- The killed Green kernel increases with the finite vertex domain. -/
theorem greenKernel_mono_of_finite {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (x b : ℤ) :
    greenKernel m A x b ≤ greenKernel m B x b :=
  greenKernel_mono_of_firstStep hlf hcons hA hAB
    (fun b => greenFn_laplacian_fst hlf hcons hA b)
    (fun b => greenFn_laplacian_fst hlf hcons hB b) x b

end MatedCRT
