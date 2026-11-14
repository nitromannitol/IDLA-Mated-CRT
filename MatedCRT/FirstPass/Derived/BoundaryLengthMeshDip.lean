import MatedCRT.FirstPass.Derived.BoundaryLengthFirstCrossing

/-!
# Mesh dips and mated-CRT edges

A first dip below a cell minimum produces an edge to the cell containing
that dip. A bound on its left endpoint also locates the neighboring vertex.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A mesh dip below a cell minimum, with no earlier dip, produces a later
adjacent vertex whose position is beyond any bound on the dip cell's left endpoint. -/
theorem exists_bmAdjacent_after_of_mesh_dip {ε b : ℝ} (hε : 0 < ε)
    {X : ℝ → ℝ} (hX : Continuous X) (j : ℤ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (ε * j + (n : ℝ) * ε) (ε * j + ((n : ℝ) + 1) * ε))
    (hdip : X t < sInf (X '' Icc (ε * j - ε) (ε * j)))
    (hbefore : ∀ u ∈ Icc (ε * j) (ε * j + (n : ℝ) * ε),
      sInf (X '' Icc (ε * j - ε) (ε * j)) ≤ X u)
    (hb : b < ε * j + (n : ℝ) * ε) :
    ∃ k : ℤ, j < k ∧ b < ε * k ∧ bmAdjacent ε X j k := by
  let k : ℤ := j + (n : ℤ) + 1
  have hjk : j < k := by dsimp [k]; omega
  have hleft : ε * k - ε = ε * j + (n : ℝ) * ε := by
    dsimp [k]
    push_cast
    ring
  have hright : ε * k = ε * j + ((n : ℝ) + 1) * ε := by
    dsimp [k]
    push_cast
    ring
  refine ⟨k, hjk, ?_, bmAdjacent_of_first_crossing hε hX hjk ?_ hdip.le ?_⟩
  · rw [hright]
    nlinarith
  · rw [hleft, hright]
    exact ht
  · simpa only [hleft] using hbefore

end MatedCRT
