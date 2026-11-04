import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov

/-!
# The discrete Green kernel away from its pole

The scaled Green kernel is harmonic on a finite domain away from its pole. This is the
local input to the compactness argument in the proof of Lemma 3.3.
-/

namespace MatedCRT

open Set

/-- The rescaled discrete Green kernel has zero Laplacian away from the pole. -/
theorem matedLaplacian_scaled_greenKernel_eq_zero {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite)
    {o b : ℤ} (ho : o ∈ A) (hb : b ∈ A) (hne : b ≠ o) (ε : ℝ) :
    matedLaplacian m (fun x => ε⁻¹ * greenKernel m A o x) b = 0 := by
  change mLaplacian m (fun x => ε⁻¹ * greenKernel m A o x) b = 0
  rw [mLaplacian_const_mul, greenKernelLaplacianStep m A hsymm hlf hcons hA o ho b hb]
  simp [hne]

end MatedCRT
