import MatedCRT.Proofs.Sec4.GreenLaplacian

/-!
# Reversibility of the killed Green function

Lyons and Peres, Exercise 2.1, as used in the proof of Lemma 5.3.  The
first-step identity is supplied explicitly; it is proved in the Section 4
Green-function development.  The discrete divergence theorem and the
Green-function infrastructure used here include work by Leonardo Bonanno.
-/

namespace MatedCRT

open Set

/-- Reversibility of the Green function on a finite subset of a locally finite
symmetric multigraph.  `hfirst` is the first-step Green function equation. -/
theorem greenFn_reversible_of_firstStep {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hA : A.Finite)
    (hfirst : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (a b : ℤ) :
    greenFn m A a b * (mdeg m a : ℝ) = greenFn m A b a * (mdeg m b : ℝ) :=
  kernel_symm_of_laplacian hsymm hlf hA
    (fun _ hx c => greenFn_eq_zero_of_not_mem m hx c) hfirst a b

/-- The degree-normalized killed Green kernel is symmetric when every vertex
has positive degree. -/
theorem greenKernel_symm_of_firstStep {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hA : A.Finite)
    (hdeg : ∀ a, mdeg m a ≠ 0)
    (hfirst : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (a b : ℤ) : greenKernel m A a b = greenKernel m A b a := by
  have ha : (mdeg m a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg a)
  have hb : (mdeg m b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg b)
  unfold greenKernel
  apply (div_eq_div_iff hb ha).2
  exact greenFn_reversible_of_firstStep hsymm hlf hA hfirst a b

/-- The sum in Lemma 5.3 equals the normalized exit time multiplied by the
degree of its target. -/
theorem tsum_greenFn_eq_degree_mul_normExitTime_of_firstStep
    {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hA : A.Finite)
    (hdeg : ∀ a, mdeg m a ≠ 0)
    (hfirst : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (a : ℤ) : (∑' b : A, greenFn m A b a) =
      (mdeg m a : ℝ) * normExitTime m A a := by
  have ha : (mdeg m a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg a)
  have hpoint : ∀ b, greenFn m A b a = (mdeg m a : ℝ) * greenKernel m A a b := by
    intro b
    rw [greenKernel_symm_of_firstStep hsymm hlf hA hdeg hfirst a b]
    unfold greenKernel
    field_simp
  simp_rw [hpoint]
  exact tsum_mul_left

/-- Convert the normalized inequality in the proof of Lemma 5.3 into its
Green-function form. -/
theorem meanValue_of_normalized_of_firstStep {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hA : A.Finite)
    (hdeg : ∀ a, mdeg m a ≠ 0)
    (hfirst : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (a : ℤ) (K s : ℝ)
    (h : (1 + s) * normExitTime m A a ≤ K * greenKernel m A a 0) :
    (1 + s) * (∑' b : A, greenFn m A b a) ≤ K * greenFn m A 0 a := by
  have ha : (0 : ℝ) < mdeg m a := Nat.cast_pos.2 (Nat.pos_of_ne_zero (hdeg a))
  have hG : (mdeg m a : ℝ) * greenKernel m A a 0 = greenFn m A 0 a := by
    rw [greenKernel_symm_of_firstStep hsymm hlf hA hdeg hfirst a 0]
    unfold greenKernel
    field_simp
  rw [tsum_greenFn_eq_degree_mul_normExitTime_of_firstStep hsymm hlf hA hdeg hfirst]
  calc
    (1 + s) * ((mdeg m a : ℝ) * normExitTime m A a) =
        (mdeg m a : ℝ) * ((1 + s) * normExitTime m A a) := by ring
    _ ≤ (mdeg m a : ℝ) * (K * greenKernel m A a 0) := mul_le_mul_of_nonneg_left h ha.le
    _ = K * greenFn m A 0 a := by rw [← hG]; ring

end MatedCRT
