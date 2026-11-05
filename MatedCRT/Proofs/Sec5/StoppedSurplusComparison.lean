import MatedCRT.Proofs.Sec5.MeanValueInequality.ObstacleComparison

/-!
# Lemma 5.3 on `V^ε(Λ_t)`: comparison of the stopped surplus with the obstacle surplus

For a finite domain `A ⊆ B` containing the pole `0` (in the application `A = V^ε(Λ_t)`, `B = V^ε(B_ρ) \ V^ε(∂B_ρ)`),
the *stopped surplus* `u_A = K g_A(·, 0) - q_A` has Laplacian `(deg)⁻¹ - K (deg 0)⁻¹ 1_0` on `A` and vanishes off `A`.
The obstacle surplus `v = w + K g_B(0, ·)` of a function `w` with `Δ w = (deg)⁻¹` on `A ∩ D` and `Δ w ≥ 0` on `A \ D`
(in the application `w = w̃^ε_t`, `D = Λ^ε_t`, `K = t ε⁻¹`; Lemma 4.4) has the same Laplacian on `A ∩ D`. The maximum
principle gives the lower bound
`u_A(a) ≥ v(a) - sup_{x ∉ A} v(x) - ∑_{b ∈ E} g_A(a, b) / deg(b)` for every finite `E ⊇ A \ D`
(`stoppedSurplus_ge_obstacleSurplus`): the stopped surplus is at least the obstacle surplus, up to its values outside
`A` and the Green potential of the part of `A` not covered by the discrete cluster.
-/

namespace MatedCRT

open Set

/-- Adding a constant does not change the Laplacian. -/
theorem mLaplacian_add_const_of_locallyFinite {m : ℤ → ℤ → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (u : ℤ → ℝ) (c : ℝ) (a : ℤ) : mLaplacian m (fun x => u x + c) a = mLaplacian m u a := by
  rw [mLaplacian_add_of_locallyFinite hlf u (fun _ => c)]
  simp [mLaplacian]

/-- The Green potential `∑_{b ∈ E} g_A(·, b) / deg(b)` of a finite set `E` has Laplacian `-(deg)⁻¹ 1_E` on `A`. -/
theorem mLaplacian_greenPotential_finset {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hfirstA : ∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (E : Finset ℤ) {x : ℤ} (hx : x ∈ A) :
    mLaplacian m (fun y => ∑ b ∈ E, greenKernel m A y b) x = -(if x ∈ E then (mdeg m x : ℝ)⁻¹ else 0) := by
  classical
  have h := mLaplacian_finset_sum hlf E (fun b y => greenKernel m A y b) x
  rw [h]
  have hb : ∀ b, mLaplacian m (fun y => greenKernel m A y b) x =
      -(if x = b then (mdeg m x : ℝ)⁻¹ else 0) := by
    intro b
    have hc := mLaplacian_const_mul (m := m) ((mdeg m b : ℝ)⁻¹) (fun y => greenFn m A y b) x
    have he : (fun y => greenKernel m A y b) = fun y => (mdeg m b : ℝ)⁻¹ * greenFn m A y b := by
      funext y
      rw [greenKernel, div_eq_inv_mul]
    rw [he, hc, hfirstA b x hx]
    split_ifs with hxb
    · subst hxb
      ring
    · ring
  rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_neg_distrib, Finset.sum_ite_eq]

/-- **Comparison of the stopped surplus with the obstacle surplus.** Let `A ⊆ B` be finite, `0 ∈ A`, and let `w`
satisfy `Δ w = (deg)⁻¹` on `A ∩ D` and `Δ w ≥ 0` on `A \ D`. If `w + K g_B(0, ·) ≤ M` off `A` and `E ⊇ A \ D` is
finite, then `w(a) + K g_B(0, a) - M - ∑_{b ∈ E} g_A(a, b)/deg(b) ≤ K g_A(a, 0) - q_A(a)` for every `a`. -/
theorem stoppedSurplus_ge_obstacleSurplus {m : ℤ → ℤ → ℕ} {A B D : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (h0 : (0 : ℤ) ∈ A)
    (hfirstA : ∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))
    (hfirstB : ∀ b, ∀ a ∈ B, mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0))
    (w : ℤ → ℝ) (K M : ℝ) (E : Finset ℤ)
    (hwD : ∀ x ∈ A, x ∈ D → mLaplacian m w x = (mdeg m x : ℝ)⁻¹)
    (hwpos : ∀ x ∈ A, x ∉ D → 0 ≤ mLaplacian m w x)
    (hE : ∀ x ∈ A, x ∉ D → x ∈ E)
    (hM : ∀ x ∉ A, w x + K * greenKernel m B 0 x ≤ M) (a : ℤ) :
    w a + K * greenKernel m B 0 a - M - ∑ b ∈ E, greenKernel m A a b ≤
      K * greenKernel m A a 0 - normExitTime m A a := by
  classical
  have hdeg : ∀ z, mdeg m z ≠ 0 := fun z => (mdeg_pos_of_ne_zero hlf (hcons z)).ne'
  have hsymmA : ∀ x, greenKernel m A x 0 = greenKernel m A 0 x := fun x =>
    greenKernel_symm_of_firstStep hsymm hlf hA hdeg hfirstA x 0
  let Q : ℤ → ℝ := fun y => ∑ b ∈ E, greenKernel m A y b
  let f : ℤ → ℝ := fun x =>
    (w x + K * greenKernel m B 0 x + (-K) * greenKernel m A 0 x + normExitTime m A x + (-1) * Q x) + (-M)
  have hf0 : ∀ x ∉ A, f x ≤ 0 := by
    intro x hx
    have hg : greenKernel m A 0 x = 0 := by
      rw [← hsymmA x]
      exact greenKernel_eq_zero_of_not_mem m hx 0
    have hQ : Q x = 0 := Finset.sum_eq_zero fun b _ => greenKernel_eq_zero_of_not_mem m hx b
    have hq0 := normExitTime_eq_zero_of_not_mem m hx
    have := hM x hx
    simp only [f]
    rw [hg, hQ, hq0]
    linarith
  have hsub : ∀ x ∈ A, 0 ≤ mLaplacian m f x := by
    intro x hx
    have hgB := greenKernel_laplacian_of_firstStep hsymm hlf hcons hB hfirstB 0 (hAB h0) x (hAB hx)
    have hgA := greenKernel_laplacian_of_firstStep hsymm hlf hcons hA hfirstA 0 h0 x hx
    have hq := normExitTime_laplacian_of_firstStep hlf hA hfirstA x hx
    have hQ : mLaplacian m Q x = -(if x ∈ E then (mdeg m x : ℝ)⁻¹ else 0) :=
      mLaplacian_greenPotential_finset hlf hfirstA E hx
    have hdx : (0 : ℝ) ≤ (mdeg m x : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
    simp only [f]
    rw [mLaplacian_add_const_of_locallyFinite hlf, mLaplacian_add_of_locallyFinite hlf,
      mLaplacian_add_of_locallyFinite hlf, mLaplacian_add_of_locallyFinite hlf,
      mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul, mLaplacian_const_mul, mLaplacian_const_mul,
      hgB, hgA, hq, hQ]
    by_cases hxD : x ∈ D
    · rw [hwD x hx hxD]
      by_cases hxE : x ∈ E
      · simp only [hxE, ↓reduceIte]
        linarith
      · simp only [hxE, ↓reduceIte]
        linarith
    · simp only [hE x hx hxD, ↓reduceIte]
      have := hwpos x hx hxD
      linarith
  have hf : f a ≤ 0 := le_zero_of_subharmonic_of_nonpos_off hcons hlf hA hf0 hsub a
  simp only [f, Q] at hf
  rw [hsymmA a]
  linarith

end MatedCRT
