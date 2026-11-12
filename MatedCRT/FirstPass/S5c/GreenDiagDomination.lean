import MatedCRT.Proofs.Sec5.MeanValueInequality.ObstacleComparison
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian

/-!
# Diagonal domination of the killed Green function

For a finite set `A`, the Green function `G_A(·, b)` of simple random walk killed on exiting `A` is
harmonic on `A \ {b}`, equals `G_A(b, b)` at `b` and vanishes off `A`. The finite maximum principle
therefore gives `G_A(a, b) ≤ G_A(b, b)` for every `a`. Probabilistically this is the hitting
identity `G_A(a, b) = P_a(T_b < τ_A) G_A(b, b)`; here it follows from the first-step equation
`Δ G_A(·, b) = -δ_b` alone, without the strong Markov property.

The uniform form reduces a bound on `max_{a,b} G_A(a,b)` to a bound on the diagonal.
-/

namespace MatedCRT

open Set

/-- The graph Laplacian does not see an additive constant. -/
theorem mLaplacian_sub_const_eq {m : ℤ → ℤ → ℕ} (u : ℤ → ℝ) (c : ℝ) (a : ℤ) :
    mLaplacian m (fun x => u x - c) a = mLaplacian m u a := by
  unfold mLaplacian
  congr 1
  refine finsum_congr fun b => ?_
  ring

/-- **Diagonal domination.** On a finite set `A`, the killed Green function satisfies
`G_A(a, b) ≤ G_A(b, b)` for all `a, b` (maximum principle for the harmonic function
`G_A(·, b)` on `A \ {b}`). -/
theorem greenFn_le_greenFn_diag {m : ℤ → ℤ → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) (a b : ℤ) :
    greenFn m A a b ≤ greenFn m A b b := by
  let f : ℤ → ℝ := fun y => greenFn m A y b - greenFn m A b b
  have hf0 : ∀ y ∉ A \ {b}, f y ≤ 0 := by
    intro y hy
    by_cases hyb : y = b
    · subst hyb
      simp [f]
    · have hyA : y ∉ A := fun h => hy ⟨h, hyb⟩
      simp only [f, greenFn_eq_zero_of_not_mem m hyA b, zero_sub]
      exact neg_nonpos.2 (greenFn_nonnegative m A b b)
  have hsub : ∀ y ∈ A \ {b}, 0 ≤ mLaplacian m f y := by
    rintro y ⟨hyA, hyb⟩
    have hyb' : y ≠ b := hyb
    have h := WalkPotential.mLaplacian_greenFn hlf hcons hA b y hyA
    simp [f, mLaplacian_sub_const_eq, h, hyb']
  have h := le_zero_of_subharmonic_of_nonpos_off hcons hlf (hA.sdiff) hf0 hsub a
  simp only [f] at h
  linarith

/-- **Uniform form.** If the diagonal of the killed Green function on a finite set `A` is bounded
by `M ≥ 0` on `A`, then every entry `G_A(a, b)` is bounded by `M`. -/
theorem greenFn_le_of_diag_le {m : ℤ → ℤ → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ A, greenFn m A b b ≤ M) (a b : ℤ) : greenFn m A a b ≤ M := by
  by_cases hb : b ∈ A
  · exact (greenFn_le_greenFn_diag hlf hcons hA a b).trans (hM b hb)
  · rw [Sec7.greenFn_eq_zero_of_not_mem_right m a hb]
    exact hM0

end MatedCRT
