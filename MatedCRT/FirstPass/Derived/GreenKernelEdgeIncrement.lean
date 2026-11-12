import MatedCRT.Proofs.Sec5.StoppedPoleFiniteComparison

/-!
# The Green flow is a unit flow; increments of the Green kernel across an edge

For simple random walk on a symmetric, locally finite multigraph `m` on `ℤ` (consecutive integers adjacent) killed
on exiting a finite set `S`, the normalized Green kernel `g_S(x, ·)` is the voltage of a unit current flow from `x`:
`θ(u, v) = g_S(x, u) - g_S(x, v)`.

* `sum_flux_greenKernel` (Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*,
  Lemma 3.5 for the Green flow): for every finite `F ⊆ S`, the flux of `θ` out of `F` is `1` if `x ∈ F` and `0`
  otherwise.
* `greenKernel_sub_le_one_of_adj`, `abs_greenKernel_sub_le_one_of_adj` (ibid., Lemma 3.7): across every edge `u ∼ v`,
  `|g_S(x, u) - g_S(x, v)| ≤ 1`. This is the bound `δ ≤ 1` on the error term of ibid. Lemma 3.4, used in the proofs
  of ibid. Lemmas 4.4 and 5.4 (Lemmas 2.16 and 2.14 of the paper).

The proof of Lemma 3.7 applies the flux identity to the super-level set `F = {y ∈ S : g_S(x, y) ≥ g_S(x, u)}`: every
edge leaving `F` carries a nonnegative flow, and the total is at most `1`.
-/

namespace MatedCRT

open Finset Classical

variable {m : ℤ → ℤ → ℕ}

/-- The Laplacian of the Green kernel in its second variable: `lapSum g_S(x, ·) (a) = -δ_{ax}` for `a ∈ S`. -/
theorem lapSum_greenKernel_source {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) (x : ℤ)
    {a : ℤ} (ha : a ∈ S) :
    lapSum hlf (fun y => greenKernel m S x y) a = -(if a = x then 1 else 0) := by
  have hfun : (fun y => greenKernel m S x y) = fun y => greenKernel m S y x :=
    funext fun y => greenKernel_symm_pole hsymm hlf hcons hS x y
  rw [hfun, lapSum_greenKernel_point hlf hcons hS x ha]
  by_cases h : a = x
  · subst h
    have hdeg : (mdeg m a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (mdeg_ne_zero_of_ne_zero hlf (hcons a))
    simp only [↓reduceIte]
    field_simp
  · simp only [h, ↓reduceIte, neg_zero, mul_zero, zero_div]

/-- **Unit flux of the Green flow** (Berestycki-Gwynne Lemma 3.5 for `θ(u, v) = g_S(x, u) - g_S(x, v)`). For a
finite `S`, a finite `F ⊆ S` and a source `x`, the flux of the Green flow out of `F` is `1` if `x ∈ F` and `0`
otherwise. -/
theorem sum_flux_greenKernel (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) (x : ℤ) (F : Finset ℤ)
    (hF : (F : Set ℤ) ⊆ S) :
    ∑ a ∈ F, ∑ b ∈ (nbrs hlf a).filter (· ∉ F),
        (m a b : ℝ) * (greenKernel m S x a - greenKernel m S x b) = if x ∈ F then 1 else 0 := by
  have hflux := sum_lapSum_eq_flux hlf hsymm F (fun y => greenKernel m S x y)
  have hlap : ∑ a ∈ F, lapSum hlf (fun y => greenKernel m S x y) a = -(if x ∈ F then 1 else 0) := by
    rw [Finset.sum_congr rfl fun a ha => lapSum_greenKernel_source hsymm hlf hcons hS x (hF ha),
      Finset.sum_neg_distrib, Finset.sum_ite_eq' F x (fun _ => (1 : ℝ))]
  have hneg : ∀ a ∈ F, ∑ b ∈ (nbrs hlf a).filter (· ∉ F),
      (m a b : ℝ) * (greenKernel m S x a - greenKernel m S x b) =
      -∑ b ∈ (nbrs hlf a).filter (· ∉ F), (m a b : ℝ) * (greenKernel m S x b - greenKernel m S x a) := by
    intro a _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have key : ∑ a ∈ F, ∑ b ∈ (nbrs hlf a).filter (· ∉ F),
      (m a b : ℝ) * (greenKernel m S x b - greenKernel m S x a) = -(if x ∈ F then 1 else 0) := by
    rw [← hlap, hflux]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_congr (Finset.filter_congr_decidable _ _ _).symm fun b _ => rfl
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, key, neg_neg]

/-- **Increments of the Green kernel across an edge** (Berestycki-Gwynne Lemma 3.7). For a finite `S`, a source `x`
and an edge `u ∼ v` (`m u v ≠ 0`), `g_S(x, u) - g_S(x, v) ≤ 1`. -/
theorem greenKernel_sub_le_one_of_adj (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) (x : ℤ) {u v : ℤ} (huv : m u v ≠ 0) :
    greenKernel m S x u - greenKernel m S x v ≤ 1 := by
  set g : ℤ → ℝ := fun y => greenKernel m S x y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => greenKernel_nonneg_pole m S x y
  have hgS : ∀ y, y ∉ S → g y = 0 := fun y hy => by
    simp only [hg]
    rw [greenKernel_symm_pole hsymm hlf hcons hS x y]
    exact greenKernel_eq_zero_of_not_mem m hy x
  by_cases hle : g u ≤ g v
  · change g u - g v ≤ 1
    linarith
  push Not at hle
  have hu_pos : 0 < g u := lt_of_le_of_lt (hg0 v) hle
  have huS : u ∈ S := by
    by_contra hu
    rw [hgS u hu] at hu_pos
    exact lt_irrefl 0 hu_pos
  set F : Finset ℤ := hS.toFinset.filter (fun y => g u ≤ g y) with hFdef
  have hFS : (F : Set ℤ) ⊆ S := fun y hy => by
    simp only [hFdef, Finset.coe_filter, Set.Finite.mem_toFinset] at hy
    exact hy.1
  have huF : u ∈ F := by
    simp only [hFdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨huS, le_rfl⟩
  have hvF : v ∉ F := by
    simp only [hFdef, Finset.mem_filter, Set.Finite.mem_toFinset, not_and, not_le]
    exact fun _ => hle
  -- every edge leaving `F` carries a nonnegative flow
  have hterm : ∀ a ∈ F, ∀ b ∈ (nbrs hlf a).filter (· ∉ F), 0 ≤ (m a b : ℝ) * (g a - g b) := by
    intro a ha b hb
    have haF := ha
    simp only [hFdef, Finset.mem_filter, Set.Finite.mem_toFinset] at haF
    have hbF : b ∉ F := (Finset.mem_filter.1 hb).2
    have hgb : g b < g u := by
      by_cases hbS : b ∈ S
      · by_contra hc
        push Not at hc
        exact hbF (by simp only [hFdef, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hbS, hc⟩)
      · rw [hgS b hbS]
        exact hu_pos
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [haF.2])
  have hflux := sum_flux_greenKernel hsymm hlf hcons hS x F hFS
  have hsum_le : ∑ a ∈ F, ∑ b ∈ (nbrs hlf a).filter (· ∉ F), (m a b : ℝ) * (g a - g b) ≤ 1 := by
    have : ∑ a ∈ F, ∑ b ∈ (nbrs hlf a).filter (· ∉ F), (m a b : ℝ) * (g a - g b) =
        if x ∈ F then 1 else 0 := hflux
    rw [this]
    split_ifs <;> norm_num
  have hvmem : v ∈ (nbrs hlf u).filter (· ∉ F) :=
    Finset.mem_filter.2 ⟨(mem_nbrs hlf).2 huv, hvF⟩
  have hinner : (m u v : ℝ) * (g u - g v) ≤
      ∑ b ∈ (nbrs hlf u).filter (· ∉ F), (m u b : ℝ) * (g u - g b) :=
    Finset.single_le_sum (f := fun b => (m u b : ℝ) * (g u - g b)) (hterm u huF) hvmem
  have houter : ∑ b ∈ (nbrs hlf u).filter (· ∉ F), (m u b : ℝ) * (g u - g b) ≤
      ∑ a ∈ F, ∑ b ∈ (nbrs hlf a).filter (· ∉ F), (m a b : ℝ) * (g a - g b) :=
    Finset.single_le_sum (f := fun a => ∑ b ∈ (nbrs hlf a).filter (· ∉ F), (m a b : ℝ) * (g a - g b))
      (fun a ha => Finset.sum_nonneg (hterm a ha)) huF
  have hm1 : (1 : ℝ) ≤ m u v := by exact_mod_cast Nat.one_le_iff_ne_zero.2 huv
  have hdiff : 0 ≤ g u - g v := by linarith
  have hmul := mul_le_mul_of_nonneg_right hm1 hdiff
  change g u - g v ≤ 1
  linarith

/-- **The error term of the resistance comparison is at most one** (Berestycki-Gwynne Lemma 3.7):
`|g_S(x, u) - g_S(x, v)| ≤ 1` for every edge `u ∼ v`. -/
theorem abs_greenKernel_sub_le_one_of_adj (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) (x : ℤ) {u v : ℤ} (huv : m u v ≠ 0) :
    |greenKernel m S x u - greenKernel m S x v| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, greenKernel_sub_le_one_of_adj hsymm hlf hcons hS x huv⟩
  have h := greenKernel_sub_le_one_of_adj hsymm hlf hcons hS x (u := v) (v := u) (by rwa [hsymm])
  linarith

end MatedCRT
