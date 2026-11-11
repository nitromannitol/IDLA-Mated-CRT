import Mathlib

/-!
# FIRST PASS, Lemma 5.3: density transfer of a floor (B1 plumbing; pure topology)

A lower bound `b ≤ f q` holding on the points `q ∈ D ∩ S` of a dense set `D` extends to `b ≤ f x` for all
`x ∈ closure S`, when `f` is continuous on `closure S`. For an open `S` this needs only `D` dense. This is the step that
lets an infimum over countably many points replace an infimum over a closed set.

Note: the naive reduction "inf over the compact core = inf over rational points of {infDist > δ/2}" is false in
general (counterexample `L = ball 0 r`, `δ/2 = r`: the core is `{0}` and `{infDist > δ/2}` is empty). The reduction goes
through open sets `S_s = {x ∈ ball 0 ρ | s < infDist x Lᶜ}` with rational `0 < s < δ/2`, whose closures lie in `L`.
-/

namespace MatedCRT.S5c

open Set Topology Metric

/-- **Density transfer**: a lower bound on a dense part of `S` is a lower bound on `closure S`. -/
theorem le_of_le_on_dense_subset {f : ℂ → ℝ} {S D : Set ℂ} {b : ℝ}
    (hf : ContinuousOn f (closure S)) (hSD : S ⊆ closure (D ∩ S))
    (hb : ∀ q ∈ D ∩ S, b ≤ f q) : ∀ x ∈ closure S, b ≤ f x := by
  have hsub : D ∩ S ⊆ closure S ∩ f ⁻¹' Ici b := fun q hq =>
    ⟨subset_closure hq.2, hb q hq⟩
  have hclosed : IsClosed (closure S ∩ f ⁻¹' Ici b) :=
    hf.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  intro x hx
  have hcl : closure S ⊆ closure (D ∩ S) := closure_minimal hSD isClosed_closure
  exact (closure_minimal hsub hclosed (hcl hx)).2

/-- **Density transfer on an open set**: for open `S` and dense `D`, a lower bound on `D ∩ S` is a lower bound on
`closure S`. -/
theorem le_of_le_on_rat_points {f : ℂ → ℝ} {S D : Set ℂ} {b : ℝ} (hD : Dense D) (hSo : IsOpen S)
    (hf : ContinuousOn f (closure S)) (hb : ∀ q ∈ D ∩ S, b ≤ f q) : ∀ x ∈ closure S, b ≤ f x :=
  le_of_le_on_dense_subset hf (fun x hx => by
    rw [inter_comm]
    exact hD.open_subset_closure_inter hSo hx) hb

end MatedCRT.S5c
