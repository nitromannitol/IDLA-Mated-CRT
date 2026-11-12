import MatedCRT.FirstPass.Derived.GreenKernelSuperLevelFlux

/-!
# Lower bounds for the Green kernel from a Harnack inequality and an energy bound

Deterministic core of the proof of Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville
Brownian motion*, Lemma 4.4. For simple random walk on a symmetric, locally finite multigraph `m` on `ℤ`
(consecutive integers adjacent) killed on exiting a finite set `B`, let `g = g_B(x, ·)` be the normalized Green kernel
with pole `x ∈ A ⊆ B`.

* `greenKernel_le_pole`: `g` is maximal at its pole.
* `le_greenKernel_of_outer_boundary`: the minimum principle on `A`. If `τ ≤ g` at every vertex outside `A` adjacent
  to `A`, then `τ ≤ g` on `A`; this is the step (4.17) of the proof of ibid. Lemma 4.4.
* `le_greenKernel_of_harnack_of_energy_le`: the bound (4.16) of the proof of ibid. Lemma 4.4. Suppose the Harnack
  bound (4.13) `g(a) ≤ C₁ g(y)` holds at every vertex `a ∈ A` adjacent to `B \ A`, with `C₁ ≥ 1`, and some `h = 1` on
  `A`, `0` off `B` has `L · E(h) ≤ C₂`, `C₂ > 0`, where `E(h) = ½ ∑_{a, b ∈ S} m(a, b) (h(a) - h(b))²` (the
  resistance bound (4.15) of ibid. Lemma 4.2 with `L = log(r/s)`, by the Dirichlet principle). Then
  `g(y) ≥ L / (C₁ C₂) - 1`. The proof combines the bound (4.14) in energy form,
  `MatedCRT.one_le_mul_energy_greenKernel`, with `t = C₁ g(y)`.
* `le_greenKernel_of_harnack_of_energy_le_of_mem`: the same at every vertex of a set `D` containing the inner
  boundary of `A` on which `max_D g ≤ C₁ min_D g` (in ibid., `D = V𝒢^ε(∂B_s(z))`).
-/

namespace MatedCRT

open Finset Classical

variable {m : ℤ → ℤ → ℕ}

/-- **The Green kernel is maximal at its pole**: `g_B(x, y) ≤ g_B(x, x)` for every `y`. -/
theorem greenKernel_le_pole (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (B : Finset ℤ) (x y : ℤ) :
    greenKernel m ↑B x y ≤ greenKernel m ↑B x x := by
  by_cases hyB : y ∈ B
  · by_cases hyx : y = x
    · rw [hyx]
    · exact greenKernel_le_of_inner_boundary hsymm hlf hcons (A := {x}) x (Finset.mem_singleton_self x)
        (greenKernel_nonneg_pole m _ x x)
        (fun a ha _ _ _ _ => by rw [Finset.mem_singleton.1 ha]) y hyB (by simpa using hyx)
  · rw [greenKernel_symm_pole hsymm hlf hcons B.finite_toSet x y,
      greenKernel_eq_zero_of_not_mem m (Finset.mem_coe.not.2 hyB) x]
    exact greenKernel_nonneg_pole m _ x x

/-- **Minimum principle for the Green kernel on a set containing the pole**. If `x ∈ A ⊆ B` and `τ ≤ g_B(x, b)` at
every vertex `b ∉ A` adjacent to a vertex of `A`, then `τ ≤ g_B(x, ·)` on `A`: the kernel is harmonic on `A \ {x}`
and maximal at `x`. -/
theorem le_greenKernel_of_outer_boundary (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B : Finset ℤ} (hAB : A ⊆ B) (x : ℤ) (hxA : x ∈ A) {τ : ℝ}
    (hτ : ∀ a ∈ A, ∀ b, b ∉ A → m a b ≠ 0 → τ ≤ greenKernel m ↑B x b) :
    ∀ y ∈ A, τ ≤ greenKernel m ↑B x y := by
  -- `τ ≤ g(x)`: an edge leaves `A`, and the kernel is maximal at its pole
  have hτx : τ ≤ greenKernel m ↑B x x := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      escape_of_adjacent_succ hcons A.finite_toSet (↑A) subset_rfl ⟨x, Finset.mem_coe.2 hxA⟩
    exact (hτ a (Finset.mem_coe.1 ha) b (fun h => hb (Finset.mem_coe.2 h)) hab).trans
      (greenKernel_le_pole hsymm hlf hcons B x b)
  have hmin := nonpos_of_lapSum_nonneg hlf (U := ↑(A.erase x)) (Finset.finite_toSet _)
    (escape_of_adjacent_succ hcons (Finset.finite_toSet _)) (w := fun y => τ - greenKernel m ↑B x y)
    (fun a ha => ?_) (fun a ha b hab hbU => ?_)
  · intro y hyA
    by_cases hyx : y = x
    · rw [hyx]
      exact hτx
    · have hy := hmin y (by rw [Finset.mem_coe, Finset.mem_erase]; exact ⟨hyx, hyA⟩)
      linarith
  · rw [Finset.mem_coe, Finset.mem_erase] at ha
    have hl := lapSum_greenKernel_source hsymm hlf hcons B.finite_toSet x (a := a)
      (Finset.mem_coe.2 (hAB ha.2))
    simp only [ha.1, ↓reduceIte, neg_zero] at hl
    have heq : lapSum hlf (fun y => τ - greenKernel m ↑B x y) a =
        -lapSum hlf (fun y => greenKernel m ↑B x y) a := by
      unfold lapSum
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [heq, hl, neg_zero]
  · rw [Finset.mem_coe, Finset.mem_erase] at ha hbU
    show τ - greenKernel m ↑B x b ≤ 0
    by_cases hbx : b = x
    · rw [hbx]
      linarith
    · have hbA : b ∉ A := fun h => hbU ⟨hbx, h⟩
      have := hτ a ha.2 b hbA hab
      linarith

/-- **The bound (4.16) of Berestycki-Gwynne** (proof of Lemma 4.4), deterministic form. Let `x ∈ A ⊆ B ⊆ S` be
finite, with `S` containing the neighbours of every vertex of `B`. Suppose the Harnack bound `g_B(x, a) ≤ C₁ g_B(x, y)`
holds at every vertex `a ∈ A` adjacent to `B \ A`, with `C₁ ≥ 1`, and that some `h` equal to `1` on `A` and `0` off
`B` has `L · ½ ∑_{a, b ∈ S} m(a, b) (h(a) - h(b))² ≤ C₂` with `C₂ > 0` (a lower bound `R(A ↔ Bᶜ) ≥ L / C₂` on the
effective resistance). Then `g_B(x, y) ≥ L / (C₁ C₂) - 1`. -/
theorem le_greenKernel_of_harnack_of_energy_le (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B S : Finset ℤ} (hAB : A ⊆ B) (hBS : B ⊆ S)
    (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) (x : ℤ) (hxA : x ∈ A) {C₁ C₂ L : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 0 < C₂)
    {y : ℤ} (hharn : ∀ a ∈ A, ∀ b ∈ B, b ∉ A → m a b ≠ 0 →
      greenKernel m ↑B x a ≤ C₁ * greenKernel m ↑B x y)
    {h : ℤ → ℝ} (h1 : ∀ a ∈ A, h a = 1) (h0 : ∀ a, a ∉ B → h a = 0)
    (hE : L * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) ≤ C₂) :
    L / (C₁ * C₂) - 1 ≤ greenKernel m ↑B x y := by
  have hg : 0 ≤ greenKernel m ↑B x y := greenKernel_nonneg_pole m _ x y
  have h1E := one_le_mul_energy_greenKernel hsymm hlf hcons hAB hBS hS x hxA
    (t := C₁ * greenKernel m ↑B x y) (mul_nonneg (by linarith) hg) hharn h1 h0
  set E := (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2 with hEdef
  set g := greenKernel m ↑B x y with hgdef
  have hC : 0 < C₁ * C₂ := mul_pos (by linarith) hC₂
  have hC₂C : C₂ ≤ C₁ * C₂ := le_mul_of_one_le_left hC₂.le hC₁
  have hgC : 0 ≤ g * (C₁ * C₂) := mul_nonneg hg hC.le
  rw [div_sub_one hC.ne', div_le_iff₀ hC]
  rcases le_or_gt L 0 with hL | hL
  · linarith
  · have hLE : L ≤ (C₁ * g + 1) * C₂ := by
      calc L = L * 1 := (mul_one L).symm
        _ ≤ L * ((C₁ * g + 1) * E) := mul_le_mul_of_nonneg_left h1E hL.le
        _ = (C₁ * g + 1) * (L * E) := by ring
        _ ≤ (C₁ * g + 1) * C₂ := mul_le_mul_of_nonneg_left hE (by positivity)
    nlinarith

/-- **The bound (4.16) of Berestycki-Gwynne on a Harnack set** (proof of Lemma 4.4). Let `D` contain every vertex of
`A` adjacent to `B \ A`, and suppose `g_B(x, a) ≤ C₁ g_B(x, a')` for all `a, a' ∈ D`, with `C₁ ≥ 1` (the bound (4.13),
`max_D g ≤ C₁ min_D g`). If some `h` equal to `1` on `A` and `0` off `B` has `L · E(h) ≤ C₂`, `C₂ > 0`, then
`g_B(x, y) ≥ L / (C₁ C₂) - 1` for every `y ∈ D`. -/
theorem le_greenKernel_of_harnack_of_energy_le_of_mem (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B S : Finset ℤ} (hAB : A ⊆ B)
    (hBS : B ⊆ S) (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) (x : ℤ) (hxA : x ∈ A) {C₁ C₂ L : ℝ} (hC₁ : 1 ≤ C₁)
    (hC₂ : 0 < C₂) {D : Set ℤ} (hD : ∀ a ∈ A, ∀ b ∈ B, b ∉ A → m a b ≠ 0 → a ∈ D)
    (hharn : ∀ a ∈ D, ∀ a' ∈ D, greenKernel m ↑B x a ≤ C₁ * greenKernel m ↑B x a')
    {h : ℤ → ℝ} (h1 : ∀ a ∈ A, h a = 1) (h0 : ∀ a, a ∉ B → h a = 0)
    (hE : L * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) ≤ C₂) :
    ∀ y ∈ D, L / (C₁ * C₂) - 1 ≤ greenKernel m ↑B x y := fun y hy =>
  le_greenKernel_of_harnack_of_energy_le hsymm hlf hcons hAB hBS hS x hxA hC₁ hC₂
    (fun a ha b hb hbA hab => hharn a (hD a ha b hb hbA hab) y hy) h1 h0 hE

end MatedCRT
