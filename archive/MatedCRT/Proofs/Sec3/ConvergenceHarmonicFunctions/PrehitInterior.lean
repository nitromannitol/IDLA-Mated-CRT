import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExcursionHitOrder

/-! # Interior membership before a boundary hit -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A nearest-neighbour path started in `I` remains there up to its first
hit of `B` if every edge from `I` stays in `I` or enters `B`. -/
theorem mem_before_hit_of_neighbours
    (m : ℤ → ℤ → ℕ) (I B : Set ℤ) (x : ℕ → ℤ)
    (hstart : x 0 ∈ I)
    (hstep : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hnb : ∀ v ∈ I, ∀ w, m v w ≠ 0 → w ∈ I ∪ B) :
    ∀ n : ℕ, (n : ℕ∞) < vHitTime B x → x n ∈ I := by
  intro n
  induction n with
  | zero => intro _; exact hstart
  | succ n ih =>
    intro hn
    have hn' : (n : ℕ∞) < vHitTime B x := by
      exact (show (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ n).trans_lt hn
    have hi := ih hn'
    have hnot : x (n + 1) ∉ B := by
      have h := (natCast_lt_vExitTime_iff.1 hn) (n + 1) le_rfl
      simpa only [Set.mem_compl_iff] using h
    rcases hstep n with heq | hedge
    · simpa only [heq] using hi
    · exact (hnb (x n) hi _ hedge).resolve_right hnot

/-- The large-excursion hit-order implication for a nearest-neighbour path.
The restart cell is assumed to lie in the outer disk's interior cells. -/
theorem outer_hit_le_target_hit_of_large_excursion_of_neighbours
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hd : 0 < d) (hη : Continuous η)
    (m : ℤ → ℤ → ℕ) (x : ℕ → ℤ) (k : ℕ)
    (hstart : x k ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R))
    (hstep : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hnb : ∀ v ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R),
      ∀ w, m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R) ∪
        cellVertices ε η (sphere (vertexPoint ε η (x k)) R))
    (hlo : (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ))
    (hdiam : ∀ a ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η a) ≤ d)
    (hfin : vHitTime (cellVertices ε η (sphere z (r + 3 * d)))
      (pathShift k x) ≠ ⊤)
    (hfar : R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x k))) :
    vHitTime (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) ≤
      vHitTime (cellVertices ε η (sphere z (r + 3 * d))) (pathShift k x) := by
  apply outer_hit_le_target_hit_of_large_excursion hε hm hd hη x k hlo hdiam hfin ?_ hfar
  apply mem_before_hit_of_neighbours m _ _ (pathShift k x)
  · simpa only [pathShift, Nat.zero_add] using hstart
  · intro n
    simpa only [pathShift, show n + 1 + k = n + k + 1 by omega] using hstep (n + k)
  · exact hnb

end MatedCRT

#print axioms MatedCRT.mem_before_hit_of_neighbours
#print axioms MatedCRT.outer_hit_le_target_hit_of_large_excursion_of_neighbours
