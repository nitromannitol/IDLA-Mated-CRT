import MatedCRT.Proofs.Sec5.StoppedPoleFiniteComparison

/-!
# Minimum principle along consecutive edges for the floor (task fp-S5d-5-1, floor note Part I, Step 8.2)

Step 8.2 of `notes/fp-gaps/CHATGPT-z5-floor.md` applies the finite-set minimum principle to the degree-normalized killed Green
function `g_{B_ρ}(0,·)`, which is superharmonic on the finite set `A^ε` (including at its source). The library lemma
`MatedCRT.nonneg_of_lapSum_nonpos` (Proofs/Infra/DiscretePotential.lean) needs `A^ε` connected; here the propagation is done
along the consecutive edges `m k (k+1) ≠ 0` (which hold for every mesh and outcome, `MatedCRTEnv.mult_succ_ne_zero`), so no
connectivity of `A^ε` is needed. The argument is that of `nonneg_of_lapSum_nonpos`: a minimizer of a function with
`lapSum ≤ 0` has all its neighbours at the same value; walking from a minimizer to the right stays among minimizers until it
leaves the finite set, and the first exit point lies in the outer vertex boundary, where the function is nonnegative.
-/

open Set Finset

namespace MatedCRT

namespace FloorProof

variable {m : ℤ → ℤ → ℕ}

/-- Minimum principle on a finite set `V` of integers with consecutive edges: if `lapSum v ≤ 0` on `V` and `v ≥ 0` on the outer
vertex boundary of `V`, then `v ≥ 0` on `V`. -/
theorem nonneg_of_lapSum_nonpos_consecutive (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {V : Set ℤ} (hV : V.Finite) {v : ℤ → ℝ} (hsup : ∀ a ∈ V, lapSum hlf v a ≤ 0)
    (hb : ∀ b ∈ vBoundary m V, 0 ≤ v b) : ∀ a ∈ V, 0 ≤ v a := by
  by_contra hneg
  obtain ⟨a₁, ha₁V, ha₁⟩ : ∃ a₁ ∈ V, v a₁ < 0 := by
    by_contra h'
    exact hneg fun a ha => not_lt.1 (fun hlt => h' ⟨a, ha, hlt⟩)
  obtain ⟨a₀, ha₀, hmin⟩ := hV.toFinset.exists_min_image v ⟨a₁, hV.mem_toFinset.2 ha₁V⟩
  have ha₀V : a₀ ∈ V := hV.mem_toFinset.1 ha₀
  have hmin' : ∀ x ∈ V, v a₀ ≤ v x := fun x hx => hmin x (hV.mem_toFinset.2 hx)
  have hneg0 : v a₀ < 0 := lt_of_le_of_lt (hmin' a₁ ha₁V) ha₁
  -- a minimizer has all its neighbours in `V` with the same value
  have hstep : ∀ x ∈ V, v x = v a₀ → ∀ y, m x y ≠ 0 → y ∈ V ∧ v y = v a₀ := by
    intro x hx hxv y hy
    have hterm : ∀ b ∈ nbrs hlf x, 0 ≤ (m x b : ℝ) * (v b - v x) := by
      intro b hbm
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      rcases mem_vClosure_of_mem_nbrs hlf hx hbm with hbV | hbB
      · linarith [hmin' b hbV]
      · linarith [hb b hbB]
    have hsum0 : ∑ b ∈ nbrs hlf x, (m x b : ℝ) * (v b - v x) = 0 := by
      have h := hsup x hx
      unfold lapSum at h
      exact le_antisymm h (Finset.sum_nonneg hterm)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum0 y ((mem_nbrs hlf).2 hy)
    have hmpos : (m x y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hvy : v y = v x := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hmpos
      · linarith
    have hyV : y ∈ V := by
      by_contra hyV
      have hyB : y ∈ vBoundary m V := ⟨hyV, x, hx, hy⟩
      linarith [hb y hyB]
    exact ⟨hyV, by linarith⟩
  -- walking to the right from `a₀` stays among minimizers
  have hwalk : ∀ k : ℕ, a₀ + (k : ℤ) ∈ V ∧ v (a₀ + (k : ℤ)) = v a₀ := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using ha₀V, by simp⟩
    | succ k ih =>
      have e : a₀ + ((k + 1 : ℕ) : ℤ) = a₀ + (k : ℤ) + 1 := by push_cast; ring
      rw [e]
      exact hstep (a₀ + (k : ℤ)) ih.1 ih.2 (a₀ + (k : ℤ) + 1) (hcons (a₀ + (k : ℤ)))
  have hinj : Function.Injective (fun k : ℕ => a₀ + (k : ℤ)) := by
    intro i j hij
    have h2 : a₀ + (i : ℤ) = a₀ + (j : ℤ) := hij
    exact Nat.cast_injective (add_left_cancel h2)
  have hrange : Set.range (fun k : ℕ => a₀ + (k : ℤ)) ⊆ V := by
    rintro _ ⟨k, rfl⟩
    exact (hwalk k).1
  exact (Set.infinite_range_of_injective hinj) (hV.subset hrange)

/-- The lapSum of a function shifted by a constant is unchanged. -/
theorem lapSum_sub_const (hlf : IsLocallyFiniteMult m) (u : ℤ → ℝ) (L : ℝ) (a : ℤ) :
    lapSum hlf (fun b => u b - L) a = lapSum hlf u a := by
  unfold lapSum
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The killed Green kernel with source `0` is superharmonic on its domain, including at the source
(`lapSum_greenKernel_point`, Proofs/Sec5/StoppedPoleFiniteComparison.lean:93): `lapSum (g_S(0,·)) ≤ 0` on `S`. -/
theorem lapSum_greenKernel_source_nonpos (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {S : Set ℤ} (hS : S.Finite) {a : ℤ} (ha : a ∈ S) :
    lapSum hlf (fun x => greenKernel m S 0 x) a ≤ 0 := by
  have hfun : (fun x => greenKernel m S 0 x) = (fun x => greenKernel m S x 0) :=
    funext fun x => greenKernel_symm_pole hsymm hlf hcons hS 0 x
  rw [hfun, lapSum_greenKernel_point hlf hcons hS 0 ha]
  have h1 : (mdeg m a : ℝ) * (-(if a = 0 then (1 : ℝ) else 0)) ≤ 0 := by
    split_ifs <;> simp
  exact div_nonpos_iff.2 (Or.inr ⟨h1, Nat.cast_nonneg _⟩)

end FloorProof

end MatedCRT
