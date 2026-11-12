import MatedCRT.FirstPass.Derived.GreenFlowEnergy

/-!
# Minimum principle for the killed Green function on an inner boundary

For a finite set `B ⊆ ℤ`, a pole `x ∈ A ⊆ B`, the function `v ↦ G_B(v, x)` is harmonic on
`B ∖ {x}` (eq:discrete-green-laplacian) and `G_B(x, x) = max_v G_B(v, x)`
(`greenFn_le_greenFn_diag`). Its minimum over `A` is therefore attained on the inner boundary of
`A`, the set of vertices of `A` having a neighbour outside `A`: a minimiser in the interior of
`A ∖ {x}` forces all its neighbours to be minimisers, and the right-most minimiser has the neighbour
`y + 1` (the walk is connected by the path `k ~ k + 1`), which then must lie outside `A`.
If the pole itself is a minimiser, the Green function is constant on `A` and the right-most point of
`A` is on the inner boundary.

This is the minimum principle used for `min_{∂A} g_B(x, ·)` in the proof of
[BG20, Lem. 5.5] (the lower half of Lemma 3.4 there).
-/

namespace MatedCRT

open Finset

variable {m : ℤ → ℤ → ℕ}

/-- **Minimum principle on the inner boundary.** For a finite set `B`, `x ∈ A ⊆ B`, the function
`v ↦ G_B(v, x)` attains its minimum over `A` at a point `y ∈ A` having a neighbour outside `A`. -/
theorem exists_mem_innerBoundary_greenFn_le (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {B A : Set ℤ} (hB : B.Finite) (hAB : A ⊆ B) {x : ℤ}
    (hx : x ∈ A) :
    ∃ y ∈ A, (∃ z, z ∉ A ∧ m y z ≠ 0) ∧ ∀ v ∈ A, greenFn m B y x ≤ greenFn m B v x := by
  have hA : A.Finite := hB.subset hAB
  obtain ⟨v₀, hv₀A, hv₀min⟩ :=
    Set.exists_min_image A (fun v => greenFn m B v x) hA ⟨x, hx⟩
  by_cases hxmin : ∀ w ∈ A, greenFn m B x x ≤ greenFn m B w x
  · obtain ⟨y, hyA, hymax⟩ := Set.exists_max_image A id hA ⟨x, hx⟩
    refine ⟨y, hyA, ⟨y + 1, fun h => ?_, hcons y⟩, fun v hv => ?_⟩
    · have := hymax (y + 1) h
      simp only [id] at this
      omega
    · exact (greenFn_le_greenFn_diag hlf hcons hB y x).trans (hxmin v hv)
  · set M : Set ℤ := {v | v ∈ A ∧ ∀ w ∈ A, greenFn m B v x ≤ greenFn m B w x} with hM
    have hMfin : M.Finite := hA.subset fun v hv => hv.1
    obtain ⟨y, hyM, hymax⟩ := Set.exists_max_image M id hMfin ⟨v₀, hv₀A, hv₀min⟩
    obtain ⟨hyA, hymin⟩ := hyM
    have hyx : y ≠ x := by
      rintro rfl
      exact hxmin hymin
    by_cases hout : ∃ z, z ∉ A ∧ m y z ≠ 0
    · exact ⟨y, hyA, hout, hymin⟩
    · exfalso
      have hout' : ∀ z, z ∉ A → m y z = 0 := fun z hz =>
        by_contra fun h => hout ⟨z, hz, h⟩
      let S : Finset ℤ := hB.toFinset.biUnion fun a => (hlf a).toFinset
      have hS : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∈ S := by
        intro a ha b hb
        simp only [S, Finset.mem_biUnion, Set.Finite.mem_toFinset]
        exact ⟨a, ha, hb⟩
      have hpois := sum_mul_greenFn_sub_eq_ite hlf hcons hB x hS y (hAB hyA)
      have h0 : (if y = x then (mdeg m x : ℝ) else 0) = 0 := by simp [hyx]
      rw [h0] at hpois
      have hnonpos : ∀ b ∈ S,
          (m y b : ℝ) * (greenFn m B y x - greenFn m B b x) ≤ 0 := by
        intro b _
        by_cases hmb : m y b = 0
        · simp [hmb]
        · have hbA : b ∈ A := by
            by_contra hb
            exact hmb (hout' b hb)
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
            (sub_nonpos.2 (hymin b hbA))
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hpois (y + 1)
        (hS y (hAB hyA) (y + 1) (hcons y))
      have hsub : greenFn m B y x - greenFn m B (y + 1) x = 0 :=
        (mul_eq_zero.1 hzero).resolve_left (by exact_mod_cast hcons y)
      have heq : greenFn m B y x = greenFn m B (y + 1) x := sub_eq_zero.1 hsub
      have hy1A : y + 1 ∈ A := by
        by_contra h
        exact hcons y (hout' _ h)
      have hy1M : y + 1 ∈ M := ⟨hy1A, fun w hw => by rw [← heq]; exact hymin w hw⟩
      have := hymax (y + 1) hy1M
      simp only [id] at this
      omega

end MatedCRT
