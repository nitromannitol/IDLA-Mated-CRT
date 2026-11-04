import MatedCRT.Proofs.Sec5.MeanValueInequality.Reversibility

/-!
# Discrete obstacle comparison for Lemma 5.3

This finite-graph argument isolates the maximum-principle step.  It uses the
Green-function Laplacian, normalized exit-time Laplacian, and maximum
principle in the Section 4 infrastructure, including work by Leonardo Bonanno.
-/

namespace MatedCRT

open Set

/-- Maximum principle for a subharmonic function with nonpositive values
outside a finite set. -/
theorem le_zero_of_subharmonic_of_nonpos_off {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hA : A.Finite) {f : ℤ → ℝ} (hf0 : ∀ x ∉ A, f x ≤ 0)
    (hsub : ∀ x ∈ A, 0 ≤ mLaplacian m f x) (a : ℤ) : f a ≤ 0 := by
  classical
  by_cases ha : a ∈ A
  · let g : ℤ → ℝ := fun x => if x ∈ A then f x else 0
    have hg0 : ∀ x ∉ A, g x = 0 := by intro x hx; simp [g, hx]
    have hgsub : ∀ x ∈ A, 0 ≤ mLaplacian m g x := by
      intro x hx
      have hcomp : mLaplacian m f x ≤ mLaplacian m g x := by
        unfold mLaplacian
        have hgx : g x = f x := by simp [g, hx]
        rw [hgx]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        refine finsum_le_finsum ?_ ?_ fun y => ?_
        · exact (hlf x).subset fun y hy hy0 => hy (by simp [hy0])
        · exact (hlf x).subset fun y hy hy0 => hy (by simp [hy0])
        · have hy : f y ≤ g y := by
            by_cases hyA : y ∈ A
            · simp [g, hyA]
            · simpa [g, hyA] using hf0 y hyA
          exact mul_le_mul_of_nonneg_left (sub_le_sub_right hy _) (Nat.cast_nonneg _)
      exact (hsub x hx).trans hcomp
    have := le_zero_of_subharmonic hcons hlf hA hg0 hgsub a
    simpa [g, ha] using this
  · exact hf0 a ha

/-- If the obstacle surplus vanishes outside `A` and has the prescribed
Laplacian on `A`, it is bounded by the Green potential minus the normalized
exit time.  The boundary hypothesis concerns the *sum* `w + K g_B`, not its
individual summands. -/
theorem obstacle_surplus_le_green_sub_exit {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (h0 : (0 : ℤ) ∈ A)
    (hfirstA : ∀ b, ∀ a ∈ A,
      mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (hfirstB : ∀ b, ∀ a ∈ B,
      mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0))
    (w : ℤ → ℝ) (K : ℝ)
    (hw : ∀ a ∈ A, mLaplacian m w a = (mdeg m a : ℝ)⁻¹)
    (hboundary : ∀ a ∉ A, w a + K * greenKernel m B 0 a ≤ 0)
    (a : ℤ) :
    w a + K * greenKernel m B 0 a ≤ K * greenKernel m A 0 a - normExitTime m A a := by
  classical
  let f : ℤ → ℝ := fun x =>
    w x + K * greenKernel m B 0 x + (-K) * greenKernel m A 0 x + normExitTime m A x
  have hf0 : ∀ x ∉ A, f x ≤ 0 := by
    intro x hx
    have hg : greenKernel m A 0 x = 0 := by
      have hdeg : ∀ z, mdeg m z ≠ 0 := fun z => (mdeg_pos_of_ne_zero hlf (hcons z)).ne'
      rw [greenKernel_symm_of_firstStep hsymm hlf hA hdeg hfirstA 0 x]
      exact greenKernel_eq_zero_of_not_mem m hx 0
    simpa [f, hg, normExitTime_eq_zero_of_not_mem m hx] using hboundary x hx
  have hsub : ∀ x ∈ A, 0 ≤ mLaplacian m f x := by
    intro x hx
    have hgB := greenKernel_laplacian_of_firstStep hsymm hlf hcons hB hfirstB 0 (hAB h0) x (hAB hx)
    have hgA := greenKernel_laplacian_of_firstStep hsymm hlf hcons hA hfirstA 0 h0 x hx
    have hq := normExitTime_laplacian_of_firstStep hlf hA hfirstA x hx
    dsimp [f]
    rw [mLaplacian_add_of_locallyFinite hlf, mLaplacian_add_of_locallyFinite hlf,
      mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul, mLaplacian_const_mul,
      hw x hx, hgB, hgA, hq]
    ring_nf
    exact le_refl 0
  have hf : f a ≤ 0 := le_zero_of_subharmonic_of_nonpos_off hcons hlf hA hf0 hsub a
  dsimp [f] at hf
  linarith

/-- Combining the obstacle comparison with upper and lower bounds gives the
normalized mean-value inequality, with margin `c / C`. -/
theorem normalized_meanValue_of_surplus_bounds {v q g K ε c C : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hC : 0 < C)
    (hcomparison : v ≤ K * g - q) (hv : c / ε ≤ v) (hq : q ≤ C / ε) :
    (1 + c / C) * q ≤ K * g := by
  have hmul := mul_le_mul_of_nonneg_left hq (div_nonneg hc.le hC.le)
  have hcancel : c / C * (C / ε) = c / ε := by field_simp
  rw [hcancel] at hmul
  nlinarith

end MatedCRT
