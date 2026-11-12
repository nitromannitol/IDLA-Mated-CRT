import MatedCRT.FirstPass.Derived.GreenKernelEdgeIncrement
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import LatticeProb.Network.UnitFluxEnergyBound

/-!
# The Green flow out of a super-level set of the Green kernel

For simple random walk on a symmetric, locally finite multigraph `m` on `ℤ` (consecutive integers adjacent) killed
on exiting a finite set `B`, let `g = g_B(x, ·)` be the normalized Green kernel with pole `x ∈ B`, let `t ≥ 0` and let
`F = {y ∈ B : g(y) > t}` be a super-level set containing `x`. Let `S` be a finite set containing `B` and every
neighbour of a vertex of `B`. This file verifies, for the conductances `c(a, b) = m(a, b)` and the potential `g`,
the hypotheses of Thomson's argument bounding the effective resistance from `F` to the complement of `B` by `t + 1`:

* `sum_mul_sub_greenKernel_eq_zero`: `g` is harmonic on `B` off the pole;
* `sum_flux_ite_greenKernel`: the flux of the Green flow out of `F` is `1` (Berestycki-Gwynne, *Random walks on
  mated-CRT planar maps and Liouville Brownian motion*, Lemma 3.5);
* `greenKernel_superLevel_edge`: across an edge `a ∼ b` leaving `F`, `g(b) ≤ g(a) ≤ t + 1` (ibid., Lemma 3.7);
* `greenKernel_superLevel_unitFlux`: the four facts together, in the form of the energy bound
  `1 ≤ (t + 1) · E(h)` for every `h = 1` on `F` and `0` off `B`;
* `one_le_mul_energy_greenKernel_superLevel`: that energy bound, from `LatticeProb.one_le_mul_energy_of_unitFlux`;
* `greenKernel_le_of_inner_boundary`: the maximum principle on `B \ A` for a pole `x ∈ A`;
* `one_le_mul_energy_greenKernel`: the bound (4.14) in the proof of ibid. Lemma 4.4, in energy form. If `x ∈ A ⊆ B`,
  `t ≥ 0` and `g_B(x, a) ≤ t` at every vertex `a ∈ A` adjacent to `B \ A`, then every `h = 1` on `A` and `0` off `B`
  has `1 ≤ (t + 1) · E(h)`, `E(h) = ½ ∑_{a, b ∈ S} m(a, b) (h(a) - h(b))²`. By the Dirichlet principle this is
  `R(A ↔ Bᶜ) ≤ t + 1`, that is, ibid. Lemma 3.4 with the error term `δ ≤ 1` of ibid. Lemma 3.7.
-/

namespace MatedCRT

open Finset Classical

variable {m : ℤ → ℤ → ℕ}

/-- A sum of `m(a, b) F(b)` over a finite set containing the neighbours of `a` is the sum over the neighbours. -/
theorem sum_mul_eq_sum_nbrs_of_subset (hlf : IsLocallyFiniteMult m) {a : ℤ} {S : Finset ℤ}
    (hS : nbrs hlf a ⊆ S) (F : ℤ → ℝ) :
    ∑ b ∈ S, (m a b : ℝ) * F b = ∑ b ∈ nbrs hlf a, (m a b : ℝ) * F b := by
  refine (Finset.sum_subset hS fun b _ hb => ?_).symm
  simp only [mem_nbrs, not_not] at hb
  simp [hb]

/-- **Harmonicity of the Green kernel off the pole**: for `a ∈ B`, `a ≠ x` and a finite `S` containing the neighbours
of `a`, `∑_{b ∈ S} m(a, b) (g_B(x, a) - g_B(x, b)) = 0`. -/
theorem sum_mul_sub_greenKernel_eq_zero (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B : Finset ℤ} (x : ℤ) {a : ℤ} (ha : a ∈ B) (hax : a ≠ x)
    {S : Finset ℤ} (hS : nbrs hlf a ⊆ S) :
    ∑ b ∈ S, (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b) = 0 := by
  have h := lapSum_greenKernel_source hsymm hlf hcons B.finite_toSet x (a := a) (Finset.mem_coe.2 ha)
  simp only [hax, ↓reduceIte, neg_zero] at h
  unfold lapSum at h
  have hsub := sum_mul_eq_sum_nbrs_of_subset hlf hS
    (fun b => greenKernel m ↑B x a - greenKernel m ↑B x b)
  rw [hsub]
  have hneg : ∑ b ∈ nbrs hlf a, (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b) =
      -∑ b ∈ nbrs hlf a, (m a b : ℝ) * (greenKernel m ↑B x b - greenKernel m ↑B x a) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hneg, h, neg_zero]

/-- **Unit flux of the Green flow, summed over a neighbourhood** (Berestycki-Gwynne Lemma 3.5). For finite
`F ⊆ B` containing the pole `x`, and a finite `S` containing the neighbours of every vertex of `F`,
`∑_{a ∈ F} ∑_{b ∈ S \ F} m(a, b) (g_B(x, a) - g_B(x, b)) = 1`. -/
theorem sum_flux_ite_greenKernel (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B F S : Finset ℤ} (hFB : F ⊆ B)
    (hS : ∀ a ∈ F, nbrs hlf a ⊆ S) (x : ℤ) (hx : x ∈ F) :
    ∑ a ∈ F, ∑ b ∈ S,
      (if b ∈ F then 0 else (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b)) = 1 := by
  have h := sum_flux_greenKernel hsymm hlf hcons B.finite_toSet x F (Finset.coe_subset.2 hFB)
  simp only [hx, ↓reduceIte] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h1 : ∑ b ∈ S, (if b ∈ F then 0 else (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b)) =
      ∑ b ∈ nbrs hlf a,
        (if b ∈ F then 0 else (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b)) := by
    refine (Finset.sum_subset (hS a ha) fun b _ hb => ?_).symm
    simp only [mem_nbrs, not_not] at hb
    simp [hb]
  rw [h1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hbF : b ∈ F <;> simp [hbF]

/-- **The Green kernel across an edge leaving a super-level set** (Berestycki-Gwynne Lemma 3.7). Let
`F = {y ∈ B : g_B(x, y) > t}` with `t ≥ 0`. If `a ∈ F`, `b ∉ F` and `a ∼ b`, then
`g_B(x, b) ≤ g_B(x, a) ≤ t + 1`. -/
theorem greenKernel_superLevel_edge (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B : Finset ℤ} (x : ℤ) {t : ℝ} (ht : 0 ≤ t) {a b : ℤ}
    (ha : a ∈ B.filter (fun y => t < greenKernel m ↑B x y))
    (hb : b ∉ B.filter (fun y => t < greenKernel m ↑B x y)) (hab : m a b ≠ 0) :
    greenKernel m ↑B x b ≤ greenKernel m ↑B x a ∧ greenKernel m ↑B x a ≤ t + 1 := by
  rw [Finset.mem_filter] at ha
  have hgb : greenKernel m ↑B x b ≤ t := by
    by_cases hbB : b ∈ B
    · exact not_lt.1 fun h => hb (Finset.mem_filter.2 ⟨hbB, h⟩)
    · rw [greenKernel_symm_pole hsymm hlf hcons B.finite_toSet x b,
        greenKernel_eq_zero_of_not_mem m (Finset.mem_coe.not.2 hbB) x]
      exact ht
  have hedge := greenKernel_sub_le_one_of_adj hsymm hlf hcons B.finite_toSet x hab
  exact ⟨by linarith [ha.2], by linarith⟩

/-- **The super-level sets of the Green kernel satisfy the unit-flux hypotheses** (the input of the bound (4.14) in
the proof of Berestycki-Gwynne Lemma 4.4). Let `x ∈ F = {y ∈ B : g_B(x, y) > t}` with `t ≥ 0`, and let `S ⊇ B` be
finite and contain the neighbours of every vertex of `B`. For `c(a, b) = m(a, b)` and `g = g_B(x, ·)`: `g` vanishes
off `B`, is harmonic on `B \ F`, carries unit flux out of `F`, and `g(b) ≤ g(a) ≤ t + 1` across every edge `a ∼ b`
leaving `F`. -/
theorem greenKernel_superLevel_unitFlux (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B S : Finset ℤ} (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) (x : ℤ) {t : ℝ}
    (ht : 0 ≤ t) (hx : x ∈ B.filter (fun y => t < greenKernel m ↑B x y)) :
    (∀ a, a ∉ B → greenKernel m ↑B x a = 0) ∧
    (∀ a ∈ B, a ∉ B.filter (fun y => t < greenKernel m ↑B x y) →
      ∑ b ∈ S, (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b) = 0) ∧
    (∑ a ∈ B.filter (fun y => t < greenKernel m ↑B x y), ∑ b ∈ S,
      (if b ∈ B.filter (fun y => t < greenKernel m ↑B x y) then 0
        else (m a b : ℝ) * (greenKernel m ↑B x a - greenKernel m ↑B x b)) = 1) ∧
    (∀ a ∈ B.filter (fun y => t < greenKernel m ↑B x y), ∀ b ∈ S,
      b ∉ B.filter (fun y => t < greenKernel m ↑B x y) → (m a b : ℝ) ≠ 0 →
      greenKernel m ↑B x b ≤ greenKernel m ↑B x a ∧ greenKernel m ↑B x a ≤ t + 1) := by
  refine ⟨fun a ha => ?_, fun a ha haF => ?_, ?_, fun a ha b _ hb hab => ?_⟩
  · rw [greenKernel_symm_pole hsymm hlf hcons B.finite_toSet x a]
    exact greenKernel_eq_zero_of_not_mem m (Finset.mem_coe.not.2 ha) x
  · exact sum_mul_sub_greenKernel_eq_zero hsymm hlf hcons x ha (fun h => haF (h ▸ hx)) (hS a ha)
  · exact sum_flux_ite_greenKernel hsymm hlf hcons (Finset.filter_subset _ _)
      (fun a ha => hS a (Finset.mem_of_mem_filter a ha)) x hx
  · exact greenKernel_superLevel_edge hsymm hlf hcons x ht ha hb (by exact_mod_cast hab)

/-- **Energy bound for a super-level set of the Green kernel**. With `x ∈ F = {y ∈ B : g_B(x, y) > t}`, `t ≥ 0`, and
`S ⊇ B` finite containing the neighbours of every vertex of `B`, every `h` equal to `1` on `F` and `0` off `B` has
`1 ≤ (t + 1) · ½ ∑_{a, b ∈ S} m(a, b) (h(a) - h(b))²` (Thomson's argument with the Green flow). -/
theorem one_le_mul_energy_greenKernel_superLevel (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B S : Finset ℤ} (hBS : B ⊆ S) (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) (x : ℤ)
    {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ B.filter (fun y => t < greenKernel m ↑B x y)) {h : ℤ → ℝ}
    (h1 : ∀ a ∈ B.filter (fun y => t < greenKernel m ↑B x y), h a = 1) (h0 : ∀ a, a ∉ B → h a = 0) :
    1 ≤ (t + 1) * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) := by
  obtain ⟨hg, hharm, hflux, hFK⟩ := greenKernel_superLevel_unitFlux hsymm hlf hcons hS x ht hx
  exact LatticeProb.one_le_mul_energy_of_unitFlux (Finset.filter_subset _ _) hBS
    (c := fun a b => (m a b : ℝ)) (g := fun y => greenKernel m ↑B x y)
    (fun a b => by simp only [hsymm a b]) (fun a b => Nat.cast_nonneg _) hg hharm hflux (by linarith) hFK h1 h0

/-- **Maximum principle for the Green kernel off a set containing the pole**. If `x ∈ A`, `t ≥ 0` and
`g_B(x, a) ≤ t` at every `a ∈ A` adjacent to a vertex of `B \ A`, then `g_B(x, ·) ≤ t` on `B \ A`. -/
theorem greenKernel_le_of_inner_boundary (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B : Finset ℤ} (x : ℤ) (hxA : x ∈ A) {t : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ a ∈ A, ∀ b ∈ B, b ∉ A → m a b ≠ 0 → greenKernel m ↑B x a ≤ t) :
    ∀ y ∈ B, y ∉ A → greenKernel m ↑B x y ≤ t := by
  have hmax := nonpos_of_lapSum_nonneg hlf (U := ↑(B \ A)) (Finset.finite_toSet _)
    (escape_of_adjacent_succ hcons (Finset.finite_toSet _)) (w := fun y => greenKernel m ↑B x y - t)
    (fun a ha => ?_) (fun a ha b hab hbU => ?_)
  · intro y hyB hyA
    have hy := hmax y (by rw [Finset.mem_coe, Finset.mem_sdiff]; exact ⟨hyB, hyA⟩)
    linarith
  · rw [Finset.mem_coe, Finset.mem_sdiff] at ha
    have hax : a ≠ x := fun h => ha.2 (h ▸ hxA)
    have hl := lapSum_greenKernel_source hsymm hlf hcons B.finite_toSet x (a := a) (Finset.mem_coe.2 ha.1)
    simp only [hax, ↓reduceIte, neg_zero] at hl
    have heq : lapSum hlf (fun y => greenKernel m ↑B x y - t) a = lapSum hlf (fun y => greenKernel m ↑B x y) a := by
      unfold lapSum
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [heq, hl]
  · rw [Finset.mem_coe, Finset.mem_sdiff] at ha hbU
    show greenKernel m ↑B x b - t ≤ 0
    by_cases hbB : b ∈ B
    · have hbA : b ∈ A := by
        by_contra hbA
        exact hbU ⟨hbB, hbA⟩
      have := hbd b hbA a ha.1 ha.2 (by rwa [hsymm])
      linarith
    · rw [greenKernel_symm_pole hsymm hlf hcons B.finite_toSet x b,
        greenKernel_eq_zero_of_not_mem m (Finset.mem_coe.not.2 hbB) x]
      linarith

/-- **The bound (4.14) of Berestycki-Gwynne, in energy form** (proof of Lemma 4.4, from Lemmas 3.4 and 3.7). Let
`x ∈ A ⊆ B` be finite, `t ≥ 0`, and suppose `g_B(x, a) ≤ t` at every vertex `a ∈ A` adjacent to `B \ A`. Let
`S ⊇ B` be finite and contain the neighbours of every vertex of `B`. Then every `h` equal to `1` on `A` and `0` off
`B` has `1 ≤ (t + 1) · ½ ∑_{a, b ∈ S} m(a, b) (h(a) - h(b))²`, that is, `R(A ↔ Bᶜ) ≤ t + 1`. -/
theorem one_le_mul_energy_greenKernel (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B S : Finset ℤ} (hAB : A ⊆ B) (hBS : B ⊆ S)
    (hS : ∀ a ∈ B, nbrs hlf a ⊆ S) (x : ℤ) (hxA : x ∈ A) {t : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ a ∈ A, ∀ b ∈ B, b ∉ A → m a b ≠ 0 → greenKernel m ↑B x a ≤ t) {h : ℤ → ℝ}
    (h1 : ∀ a ∈ A, h a = 1) (h0 : ∀ a, a ∉ B → h a = 0) :
    1 ≤ (t + 1) * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, (m a b : ℝ) * (h a - h b) ^ 2) := by
  have hxB : x ∈ B := hAB hxA
  by_cases hlt : t < greenKernel m ↑B x x
  · -- the super-level set `{g > t}` lies in `A` by the maximum principle
    have hle := greenKernel_le_of_inner_boundary hsymm hlf hcons x hxA ht hbd
    refine one_le_mul_energy_greenKernel_superLevel hsymm hlf hcons hBS hS x ht
      (Finset.mem_filter.2 ⟨hxB, hlt⟩) (fun a ha => h1 a ?_) h0
    rw [Finset.mem_filter] at ha
    by_contra haA
    exact absurd (hle a ha.1 haA) (not_le.2 ha.2)
  · -- otherwise use the flux out of `{x}`; the Green kernel is maximal at its pole
    push Not at hlt
    have hpole : ∀ y, greenKernel m ↑B x y ≤ greenKernel m ↑B x x := by
      intro y
      by_cases hyB : y ∈ B
      · by_cases hyx : y = x
        · rw [hyx]
        · exact greenKernel_le_of_inner_boundary hsymm hlf hcons (A := {x}) x (Finset.mem_singleton_self x)
            (greenKernel_nonneg_pole m _ x x)
            (fun a ha _ _ _ _ => by rw [Finset.mem_singleton.1 ha]) y hyB (by simpa using hyx)
      · rw [greenKernel_symm_pole hsymm hlf hcons B.finite_toSet x y,
          greenKernel_eq_zero_of_not_mem m (Finset.mem_coe.not.2 hyB) x]
        exact greenKernel_nonneg_pole m _ x x
    refine LatticeProb.one_le_mul_energy_of_unitFlux (F := {x}) (Finset.singleton_subset_iff.2 hxB) hBS
      (c := fun a b => (m a b : ℝ)) (g := fun y => greenKernel m ↑B x y)
      (fun a b => by simp only [hsymm a b]) (fun a b => Nat.cast_nonneg _) (fun a ha => ?_)
      (fun a ha haF => ?_) ?_ (by linarith) (fun a ha b _ _ _ => ?_) (fun a ha => ?_) h0
    · rw [greenKernel_symm_pole hsymm hlf hcons B.finite_toSet x a]
      exact greenKernel_eq_zero_of_not_mem m (Finset.mem_coe.not.2 ha) x
    · exact sum_mul_sub_greenKernel_eq_zero hsymm hlf hcons x ha (by simpa using haF) (hS a ha)
    · exact sum_flux_ite_greenKernel hsymm hlf hcons (Finset.singleton_subset_iff.2 hxB)
        (fun a ha => hS a (by rw [Finset.mem_singleton.1 ha]; exact hxB)) x (Finset.mem_singleton_self x)
    · rw [Finset.mem_singleton.1 ha]
      exact ⟨hpole b, by linarith⟩
    · rw [Finset.mem_singleton.1 ha]
      exact h1 x hxA

end MatedCRT
