import MatedCRT.FirstPass.Derived.GreenTypicalTruncLog
import MatedCRT.FirstPass.Derived.InteriorCellGeometry

/-!
# Expected exit time bounded by an integral against the LQG area measure (BG20, Lemma 5.8, (5.45))

Assembly of the proof of (5.38) in Berestycki–Gwynne (2020), Lemma 5.8, on the intersection of four events, all at
the same `ε`: the Green kernel bound of Lemma 5.4 on `V^ε(B_ρ)` (exponent `β`, constant `C`); the count (5.41) of the
vertices whose cells meet `B_{ε^β}(η(a))` (at most `K`); the crude bound of Lemma 5.6, `G_{B_ρ} ≤ M` on `V^ε(B_ρ)`; and
the upper half of (A.21) of Lemma A.5 for the domain `D` (exponents `α₁, b`). For `a` an interior vertex of
`D ⊆ B_ρ`, the near/typical split (5.39)–(5.44) with the truncated logarithmic kernel
`f_a = truncLogKernel C ε^{-β} (η(a))` as typical bound, followed by Lemma A.5 applied to `f_a` (nonnegative, bounded
by `C (log ε^{-β} + 1)` and `C ε^{-β}`-Lipschitz, both at most `ε^{-b}`), gives

`E^a τ_A ≤ K M + 6 ε⁻¹ ∫_{B_{ε^{α₁}}(D)} f_a dμ_h + ε^{-1+α₁}`, `A = V^ε(D) \ V^ε(∂D)`,

the second line of (5.45). The points `w_k ∈ H_k ∩ D` of Lemma A.4 are `η(k)` for interior vertices (E3b) and an
arbitrary point of `H_k ∩ D` for the others; the typical sum over `A` is at most the sum over `V^ε(D)` since `f_a ≥ 0`.

* `sum_interior_le_tsum_cellVertices`: the comparison of the sums over `A` and over `V^ε(D)`;
* `expectedExitTime_le_integral_truncLogKernel`: the bound above.
-/

open HarmonicBalls

namespace MatedCRT

open Set Metric MeasureTheory Filter LatticeProb.TruncatedLog

namespace ExitTimeIntegralBound

/-- For a nonnegative `g`, the degree-weighted sum of `g(η(b))` over the interior vertices of `D` is at most the
degree-weighted sum of `g(w_k)` over all vertices `k ∈ V^ε(D)`, for a choice of points `w_k ∈ H_k ∩ D` (Lemma A.4):
`w_k = η(k)` for interior vertices (their position lies in `D`), an arbitrary point of `H_k ∩ D` otherwise. -/
theorem sum_interior_le_tsum_cellVertices (m : ℤ → ℤ → ℕ) {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε)
    (hη : Continuous η) {D : Set ℂ} (hA : (interiorCellVertices ε η D).Finite)
    (hV : (cellVertices ε η D).Finite) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∃ w : ℤ → ℂ, (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ D) ∧
      ∑ b ∈ hA.toFinset, (mdeg m b : ℝ) * g (vertexPoint ε η b) ≤
        ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (w k) := by
  classical
  let w : ℤ → ℂ := fun k => if k ∈ interiorCellVertices ε η D then vertexPoint ε η k
    else if h : (cell ε η k ∩ D).Nonempty then h.some else 0
  have hwA : ∀ k ∈ interiorCellVertices ε η D, w k = vertexPoint ε η k := fun k hk => by
    simp only [w, hk, ite_true]
  refine ⟨w, fun k hk => ?_, ?_⟩
  · by_cases hkA : k ∈ interiorCellVertices ε η D
    · rw [hwA k hkA]
      exact ⟨Lemma68C12Geom.vertexPoint_mem_cell hε k,
        InteriorCellGeometry.vertexPoint_mem_of_mem_interiorCellVertices hε hη hkA⟩
    · have hne : (cell ε η k ∩ D).Nonempty := hk
      have hw : w k = hne.some := by simp only [w, hkA, hne, ite_false, dite_true]
      rw [hw]
      exact hne.some_mem
  · have htsum := Finset.tsum_subtype' hV.toFinset fun k => (matedDeg m k : ℝ) * g (w k)
    rw [hV.coe_toFinset] at htsum
    rw [htsum]
    have hsum : ∑ b ∈ hA.toFinset, (mdeg m b : ℝ) * g (vertexPoint ε η b) =
        ∑ b ∈ hA.toFinset, (matedDeg m b : ℝ) * g (w b) :=
      Finset.sum_congr rfl fun b hb => by rw [hwA b (hA.mem_toFinset.1 hb)]; rfl
    rw [hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      ((Set.Finite.toFinset_subset_toFinset (hs := hA) (ht := hV)).2 sdiff_subset)
      fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (hg _)

/-- **BG20 (5.45), deterministic form.** Let `η` be continuous and proper, `ε > 0`, `D ⊆ B_ρ`, and `a` an interior
vertex of `D`. Assume, at this `ε`:
* `hev`: the Green kernel bound of Lemma 5.4 on `V^ε(B_ρ)` with exponent `β` and constant `C ≥ 0`;
* `hY`: at most `K` vertices have cells meeting `B_{ε^β}(η(a))` ((5.41));
* `hM`: `G_{B_ρ}(a', b) ≤ M` on `V^ε(B_ρ)` (Lemma 5.6);
* `hA5`: the upper half of (A.21) (Lemma A.5) on `D`, for nonnegative test functions bounded by `ε^{-b}` and
  `ε^{-b}`-Lipschitz, with exponent `α₁`;
* `hbd`, `hlip`: `C (log ε^{-β} + 1) ≤ ε^{-b}` and `C ε^{-β} ≤ ε^{-b}` (true for small `ε` when `β < b`).
Then `E^a τ_A ≤ K M + 6 ε⁻¹ ∫_{B_{ε^{α₁}}(D)} truncLogKernel C ε^{-β} (η(a)) dμ + ε^{-1+α₁}` for
`A = V^ε(D) \ V^ε(∂D)`. -/
theorem expectedExitTime_le_integral_truncLogKernel {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε β C ρ K M α₁ b : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ}
    (hε : 0 < ε) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {D : Set ℂ}
    (hDρ : D ⊆ ball 0 ρ) (hC : 0 ≤ C) (h1 : 1 ≤ ε ^ (-β))
    (hbd : C * (Real.log (ε ^ (-β)) + 1) ≤ ε ^ (-b)) (hlip : C * ε ^ (-β) ≤ ε ^ (-b))
    (hev : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ε ^ β ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b ≤
        C * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) + C)
    {a : ℤ} (ha : a ∈ interiorCellVertices ε η D)
    (hY : ∀ s : Finset ℤ,
      (s : Set ℤ) ⊆ cellVertices ε η (ball (vertexPoint ε η a) (ε ^ β)) → (s.card : ℝ) ≤ K)
    (hM0 : 0 ≤ M)
    (hM : ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) a b ≤ M)
    (hdeg : ∀ b ∈ interiorCellVertices ε η D, 0 < mdeg m b)
    (hA5 : ∀ g : ℂ → ℝ, (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) →
      (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
      ∀ w : ℤ → ℂ, (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ D) →
      ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (w k) ≤
        6 * ε⁻¹ * ∫ x in thickening (ε ^ α₁) D, g x ∂μ + ε ^ (-1 + α₁)) :
    expectedExitTime m (interiorCellVertices ε η D) a ≤ ENNReal.ofReal (K * M +
      (6 * ε⁻¹ * ∫ x in thickening (ε ^ α₁) D, truncLogKernel C (ε ^ (-β)) (vertexPoint ε η a) x ∂μ +
        ε ^ (-1 + α₁))) := by
  have hA : (interiorCellVertices ε η D).Finite :=
    InteriorCellGeometry.interiorCellVertices_finite_of_subset_ball hη hp hε hDρ
  have hB : (interiorCellVertices ε η (ball 0 ρ)).Finite :=
    InteriorCellGeometry.interiorCellVertices_finite_of_subset_ball hη hp hε Subset.rfl
  have hAB : interiorCellVertices ε η D ⊆ interiorCellVertices ε η (ball 0 ρ) :=
    InteriorCellGeometry.interiorCellVertices_subset_of_subset_isOpen hη isOpen_ball hDρ
  have hAρ : interiorCellVertices ε η D ⊆ cellVertices ε η (ball 0 ρ) := fun k hk => (hAB hk).1
  have hV : (cellVertices ε η D).Finite :=
    (S5c.cellVertices_ball_finite hη hp hε 0 ρ).subset fun k ⟨x, hx, hxD⟩ => ⟨x, hx, hDρ hxD⟩
  have ha' := hAρ ha
  have hsplit := GreenTypicalTruncLog.expectedExitTime_le_near_truncLogKernel hlf hcons hA hB hAB hε hAρ hev
    ha' (fun s hs => hY s (hs.trans inter_subset_right)) hM0 (fun b hb => hM a ha' b (hAρ hb.1)) hdeg
  set f : ℂ → ℝ := truncLogKernel C (ε ^ (-β)) (vertexPoint ε η a)
  have hf0 : ∀ x, 0 ≤ f x := fun x => truncLogKernel_nonneg _ _ _ _
  obtain ⟨w, hw, hle⟩ := sum_interior_le_tsum_cellVertices m hε.le hη hA hV hf0
  have hMpos : 0 < ε ^ (-β) := Real.rpow_pos_of_pos hε _
  have hfA5 := hA5 f (fun x => ⟨hf0 x, by
      rw [abs_of_nonneg (hf0 x)]
      exact (truncLogKernel_le hC h1 _ _).trans hbd⟩)
    (fun x y => (abs_truncLogKernel_sub_le hC hMpos _ x y).trans
      (mul_le_mul_of_nonneg_right hlip (norm_nonneg _))) w hw
  refine hsplit.trans (ENNReal.ofReal_le_ofReal ?_)
  linarith

end ExitTimeIntegralBound

end MatedCRT
