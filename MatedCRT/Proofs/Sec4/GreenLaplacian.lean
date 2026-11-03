import MatedCRT.Steps.Sec4.ObstacleSpecialization

/-!
# The Laplacians of the Green's kernel and of the normalized exit time

Deterministic potential theory on a finite set `A` of a symmetric, locally finite multigraph on `ℤ` in which
`a ∼ a + 1` for every `a` (so that every vertex of `A` is joined to `Aᶜ` by a path):

* `le_zero_of_subharmonic`: the maximum principle (a subharmonic function on `A` vanishing off `A` is `≤ 0`);
* `exists_laplacian_eq`, `exists_nonneg_laplacian_eq`: the Dirichlet problem `Δv = r` on `A`, `v = 0` off `A`, is
  solvable (injectivity of the restricted Laplacian, by the maximum principle), with `v ≥ 0` when `r ≤ 0`;
* `kernel_symm_of_laplacian`: if `Δ G(·, b) = -δ_b` on `A` and `G(·, b) = 0` off `A` for every `b`, then
  `G(a, b) deg(a) = G(b, a) deg(b)` (the discrete divergence theorem, Lemma A.1);
* `greenKernel_laplacian_of_firstStep`, `normExitTime_laplacian_of_firstStep`: eq:discrete-normalized-green-laplacian
  (line 804) and eq:discrete-normalized-exit-laplacian (line 790) from the first-variable identity
  `Δ G_A(·, b) = -δ_b` on `A` (eq:discrete-green-laplacian, line 797).
-/

namespace MatedCRT

open Set Classical

section General

variable {α : Type*} {m : α → α → ℕ}

/-- `Δ(u + v) = Δu + Δv` on a locally finite multigraph. -/
theorem mLaplacian_add_of_locallyFinite (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (u v : α → ℝ) (a : α) :
    mLaplacian m (fun x => u x + v x) a = mLaplacian m u a + mLaplacian m v a := by
  have hu : (Function.support fun b => (m a b : ℝ) * (u b - u a)).Finite :=
    (hlf a).subset fun b hb h => hb (by simp [h])
  have hv : (Function.support fun b => (m a b : ℝ) * (v b - v a)).Finite :=
    (hlf a).subset fun b hb h => hb (by simp [h])
  have hrw : ∀ b, (m a b : ℝ) * (u b + v b - (u a + v a)) =
      (m a b : ℝ) * (u b - u a) + (m a b : ℝ) * (v b - v a) := fun b => by ring
  simp only [mLaplacian, hrw]
  rw [finsum_add_distrib hu hv, mul_add]

/-- `Δ ∑_i F_i = ∑_i Δ F_i` on a locally finite multigraph. -/
theorem mLaplacian_finset_sum (hlf : ∀ a, {b | m a b ≠ 0}.Finite) {ι : Type*} (s : Finset ι) (F : ι → α → ℝ)
    (a : α) : mLaplacian m (fun x => ∑ i ∈ s, F i x) a = ∑ i ∈ s, mLaplacian m (F i) a := by
  induction s using Finset.induction_on with
  | empty => simp [mLaplacian]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [mLaplacian_add_of_locallyFinite hlf (F i) (fun x => ∑ j ∈ s, F j x), ih]

/-- Nonpositive terms with a nonnegative finite sum vanish. -/
theorem eq_zero_of_finsum_nonneg {f : α → ℝ} (hf : (Function.support f).Finite) (hle : ∀ c, f c ≤ 0)
    (hsum : 0 ≤ ∑ᶠ c, f c) (b : α) : f b = 0 := by
  have hs : (Function.support fun c => -f c).Finite := hf.subset fun c hc => neg_ne_zero.1 hc
  have h1 : -f b ≤ ∑ᶠ c, -f c := single_le_finsum b hs fun c => neg_nonneg.2 (hle c)
  rw [finsum_neg_distrib] at h1
  linarith [hle b]

end General

section MaximumPrinciple

variable {m : ℤ → ℤ → ℕ} {A : Set ℤ}

/-- At a subharmonic global maximum, the right neighbour has the same value. -/
theorem succ_eq_of_subharmonic_max (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    {x : ℤ → ℝ} {b : ℤ} (hsub : 0 ≤ mLaplacian m x b) (hmax : ∀ c, x c ≤ x b) : x (b + 1) = x b := by
  have hdeg : (0 : ℝ) < ((mdeg m b : ℕ) : ℝ)⁻¹ :=
    inv_pos.2 (Nat.cast_pos.2 (mdeg_pos_of_ne_zero hlf (hcons b)))
  unfold mLaplacian at hsub
  have hsum := (mul_nonneg_iff_of_pos_left hdeg).1 hsub
  have hf : (Function.support fun c => (m b c : ℝ) * (x c - x b)).Finite :=
    (hlf b).subset fun c hc h => hc (by simp [h])
  have h0 := eq_zero_of_finsum_nonneg hf
    (fun c => mul_nonpos_iff.2 (Or.inl ⟨Nat.cast_nonneg _, sub_nonpos.2 (hmax c)⟩)) hsum (b + 1)
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (by exact_mod_cast h) (hcons b)
  · linarith

/-- **Maximum principle**: a function vanishing off the finite set `A` and subharmonic on `A` is `≤ 0`. -/
theorem le_zero_of_subharmonic (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hA : A.Finite) {x : ℤ → ℝ} (hx0 : ∀ a ∉ A, x a = 0) (hsub : ∀ a ∈ A, 0 ≤ mLaplacian m x a) (a : ℤ) :
    x a ≤ 0 := by
  by_contra hpos'
  have hpos : 0 < x a := not_le.1 hpos'
  have haA : a ∈ A := by
    by_contra h
    rw [hx0 a h] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨a₀, ha₀, hmax⟩ := hA.toFinset.exists_max_image x ⟨a, hA.mem_toFinset.2 haA⟩
  rw [Set.Finite.mem_toFinset] at ha₀
  have hM : 0 < x a₀ := hpos.trans_le (hmax a (hA.mem_toFinset.2 haA))
  have hglob : ∀ c, x c ≤ x a₀ := fun c => by
    by_cases hc : c ∈ A
    · exact hmax c (hA.mem_toFinset.2 hc)
    · rw [hx0 c hc]
      exact hM.le
  have key : ∀ j : ℕ, a₀ + j ∈ A ∧ x (a₀ + j) = x a₀ := by
    intro j
    induction j with
    | zero => simpa using ha₀
    | succ j ih =>
      have h1 : x (a₀ + j + 1) = x (a₀ + j) :=
        succ_eq_of_subharmonic_max hcons hlf (hsub _ ih.1) fun c => (hglob c).trans_eq ih.2.symm
      have h2 : x (a₀ + ↑(j + 1)) = x a₀ := by
        push_cast
        rw [← add_assoc, h1, ih.2]
      refine ⟨?_, h2⟩
      by_contra h
      rw [hx0 _ h] at h2
      exact absurd h2 hM.ne
  exact (Set.infinite_of_injective_forall_mem (f := fun j : ℕ => a₀ + j) (fun i j h => by simpa using h)
    fun j => (key j).1) hA

/-- The extension by `0` of a function on `A`. -/
noncomputable def extendByZero (A : Set ℤ) (x : A → ℝ) : ℤ → ℝ :=
  fun z => if h : z ∈ A then x ⟨z, h⟩ else 0

theorem extendByZero_of_not_mem {x : A → ℝ} {z : ℤ} (hz : z ∉ A) : extendByZero A x z = 0 := by
  simp [extendByZero, hz]

theorem extendByZero_coe (x : A → ℝ) (a : A) : extendByZero A x a = x a := by
  simp [extendByZero]

/-- The Laplacian of the extension by `0`, restricted to `A`, as a linear map. -/
noncomputable def restrictedLaplacian (m : ℤ → ℤ → ℕ) (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (A : Set ℤ) :
    (A → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun x a := mLaplacian m (extendByZero A x) a
  map_add' x y := by
    funext a
    have : extendByZero A (x + y) = fun z => extendByZero A x z + extendByZero A y z := by
      funext z
      unfold extendByZero
      split_ifs <;> simp
    simp only [Pi.add_apply]
    rw [this, mLaplacian_add_of_locallyFinite hlf]
  map_smul' c x := by
    funext a
    have : extendByZero A (c • x) = fun z => c * extendByZero A x z := by
      funext z
      unfold extendByZero
      split_ifs <;> simp
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [this, mLaplacian_const_mul]

theorem restrictedLaplacian_injective (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hA : A.Finite) : Function.Injective (restrictedLaplacian m hlf A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hharm : ∀ a ∈ A, mLaplacian m (extendByZero A x) a = 0 := fun a ha => congrFun hx ⟨a, ha⟩
  have h0 : ∀ a ∉ A, extendByZero A x a = 0 := fun a ha => extendByZero_of_not_mem ha
  have hle := le_zero_of_subharmonic hcons hlf hA h0 fun a ha => (hharm a ha).ge
  have hge := le_zero_of_subharmonic hcons hlf hA (x := fun z => (-1) * extendByZero A x z)
    (fun a ha => by simp [h0 a ha]) fun a ha => by
      rw [mLaplacian_const_mul, hharm a ha]
      simp
  funext a
  have h1 := hle a
  have h2 := hge a
  rw [extendByZero_coe] at h1 h2
  simp only [Pi.zero_apply]
  linarith

/-- The Dirichlet problem `Δv = r` on `A`, `v = 0` off `A`, is solvable. -/
theorem exists_laplacian_eq (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hA : A.Finite) (r : ℤ → ℝ) : ∃ v : ℤ → ℝ, (∀ a ∉ A, v a = 0) ∧ ∀ a ∈ A, mLaplacian m v a = r a := by
  have := hA.to_subtype
  obtain ⟨x, hx⟩ :=
    (LinearMap.injective_iff_surjective.1 (restrictedLaplacian_injective hcons hlf hA)) fun a => r a
  exact ⟨extendByZero A x, fun a ha => extendByZero_of_not_mem ha, fun a ha => congrFun hx ⟨a, ha⟩⟩

/-- The solution of `Δv = r ≤ 0` on `A`, `v = 0` off `A`, is nonnegative. -/
theorem exists_nonneg_laplacian_eq (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hA : A.Finite) (r : ℤ → ℝ) (hr : ∀ a ∈ A, r a ≤ 0) :
    ∃ v : ℤ → ℝ, (∀ a ∉ A, v a = 0) ∧ (∀ a ∈ A, mLaplacian m v a = r a) ∧ ∀ a, 0 ≤ v a := by
  obtain ⟨v, h0, hv⟩ := exists_laplacian_eq hcons hlf hA r
  refine ⟨v, h0, hv, fun a => ?_⟩
  have := le_zero_of_subharmonic hcons hlf hA (x := fun z => (-1) * v z) (fun a ha => by simp [h0 a ha])
    (fun a ha => by
      rw [mLaplacian_const_mul, hv a ha]
      linarith [hr a ha]) a
  linarith

end MaximumPrinciple

section Symmetry

variable {m : ℤ → ℤ → ℕ} {A : Set ℤ}

/-- If `Δ G(·, b) = -δ_b` on `A` and `G(·, b) = 0` off `A` for every `b`, then `G(a,b) deg(a) = G(b,a) deg(b)`
(discrete divergence theorem, Lemma A.1). -/
theorem kernel_symm_of_laplacian (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hA : A.Finite) {G : ℤ → ℤ → ℝ} (hG0 : ∀ x ∉ A, ∀ b, G x b = 0)
    (hR1 : ∀ b, ∀ a ∈ A, mLaplacian m (fun x => G x b) a = -(if a = b then 1 else 0)) (a b : ℤ) :
    G a b * (mdeg m a : ℝ) = G b a * (mdeg m b : ℝ) := by
  have hsupp : ∀ c, (Function.support fun x => G x c).Finite := fun c =>
    hA.subset fun x hx => by
      by_contra h
      exact hx (hG0 x h c)
  have key : ∀ c d, ∑ᶠ x, G x c * mLaplacian m (fun y => G y d) x * (mdeg m x : ℝ) =
      -(G d c * (mdeg m d : ℝ)) := by
    intro c d
    rw [finsum_eq_single _ d]
    · by_cases hd : d ∈ A
      · rw [hR1 d d hd]
        simp
      · rw [hG0 d hd c]
        simp
    · intro x hx
      by_cases hxA : x ∈ A
      · rw [hR1 d x hxA]
        simp [hx]
      · rw [hG0 x hxA c]
        simp
  have := discreteDivergenceTheorem ℤ m hsymm hlf (fun x => G x b) (fun x => G x a) (hsupp b) (hsupp a)
  rw [key b a, key a b] at this
  linarith

/-- eq:discrete-normalized-green-laplacian (line 804) from eq:discrete-green-laplacian (line 797). -/
theorem greenKernel_laplacian_of_firstStep (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite)
    (hR1 : ∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0)) :
    ∀ o ∈ A, ∀ b ∈ A, mLaplacian m (greenKernel m A o) b = -((mdeg m o : ℝ)⁻¹ * if b = o then 1 else 0) := by
  intro o _ b hb
  have hG0 : ∀ x ∉ A, ∀ c, greenFn m A x c = 0 := fun x hx c => greenFn_eq_zero_of_not_mem m hx c
  have hdeg : ∀ y, (mdeg m y : ℝ) ≠ 0 := fun y => Nat.cast_ne_zero.2 (mdeg_pos_of_ne_zero hlf (hcons y)).ne'
  have hsym : greenKernel m A o = fun y => (mdeg m o : ℝ)⁻¹ * greenFn m A y o := by
    funext y
    have h := kernel_symm_of_laplacian hsymm hlf hA hG0 hR1 o y
    unfold greenKernel
    rw [div_eq_iff (hdeg y), mul_assoc, ← h, mul_comm (greenFn m A o y), ← mul_assoc, inv_mul_cancel₀ (hdeg o),
      one_mul]
  rw [hsym, mLaplacian_const_mul, hR1 o b hb]
  ring

/-- eq:discrete-normalized-exit-laplacian (line 790) from eq:discrete-green-laplacian (line 797). -/
theorem normExitTime_laplacian_of_firstStep (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hA : A.Finite)
    (hR1 : ∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0)) :
    ∀ a ∈ A, mLaplacian m (normExitTime m A) a = -(mdeg m a : ℝ)⁻¹ := by
  intro a ha
  have hq : normExitTime m A = fun x => ∑ b ∈ hA.toFinset, (mdeg m b : ℝ)⁻¹ * greenFn m A x b := by
    funext x
    unfold normExitTime
    rw [tsum_subtype A (fun b => greenKernel m A x b), tsum_eq_sum (s := hA.toFinset) ?_]
    · refine Finset.sum_congr rfl fun b hb => ?_
      rw [Set.indicator_of_mem (hA.mem_toFinset.1 hb)]
      unfold greenKernel
      ring
    · intro b hb
      exact Set.indicator_of_notMem (fun h => hb (hA.mem_toFinset.2 h)) _
  have hterm : ∀ b ∈ hA.toFinset, mLaplacian m (fun x => (mdeg m b : ℝ)⁻¹ * greenFn m A x b) a =
      -((mdeg m b : ℝ)⁻¹ * if a = b then 1 else 0) := fun b _ => by
    rw [mLaplacian_const_mul, hR1 b a ha]
    ring
  rw [hq, mLaplacian_finset_sum hlf, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  simp [mul_ite, ha]

end Symmetry

end MatedCRT
