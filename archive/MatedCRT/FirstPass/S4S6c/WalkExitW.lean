import MatedCRT.FirstPass.S4S6c.FrontierSeparation

/-!
# The walk exits the window `V(U)` almost surely

Input (walk-law form of the Step `WalkExitsStep`, `Proofs/Sec6/ConstantOrderLowerBound/Model.lean`): for an open set `O`,
`srwLaw m a {vExitTime (interiorCellVertices ε η O) = ⊤} = 0`, i.e. the walk leaves the interior cell vertices of `O`.
Geometry: if `U ⊆ O`, every frontier point `p` of `O` lies at distance `≥ r` from `U`, and every cell meeting the frontier
of `O` has diameter `< r`, then the walk leaves the closed-cell window `V(U) = meetVerts cell U` as well, so the exit
from `V(U)` is almost surely finite (`ae_vExitTime_meetVerts_ne_top`).

The concrete geometry for `O = K + B_{2r}`, `U = K + B_r` (`K` a set in `ℂ`): `le_dist_of_frontier_thickening`.
-/

open MeasureTheory Set Metric Topology
open scoped ENNReal

namespace MatedCRT
namespace WalkExitW

/-- A frontier point of `K + B_{2r}` is at distance `≥ r` from every point of `K + B_r`. -/
lemma le_dist_of_frontier_thickening {K : Set ℂ} {r : ℝ} {p q : ℂ}
    (hp : p ∈ frontier (thickening (2 * r) K)) (hq : q ∈ thickening r K) : r ≤ dist p q := by
  rw [frontier, isOpen_thickening.interior_eq] at hp
  have hpO : p ∉ thickening (2 * r) K := hp.2
  rw [mem_thickening_iff] at hpO hq
  obtain ⟨k, hk, hqk⟩ := hq
  have hpk : 2 * r ≤ dist p k := by
    by_contra h
    push Not at h
    exact hpO ⟨k, hk, h⟩
  linarith [dist_triangle p q k]

/-- **Exit from the closed-cell window** (walk-law form). Let `O` be open and `U ⊆ O`. If the walk leaves the interior cell
vertices of `O` a.s. (`hWE`), every frontier point of `O` is at distance `≥ r` from `U` (`hsep`) and every cell meeting the
frontier of `O` has diameter `< r` (`hdiam`), then the walk a.s. leaves `V(U) = meetVerts cell U` at some time. -/
theorem ae_vExitTime_meetVerts_ne_top {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε r : ℝ} {O U : Set ℂ} (a : ℤ)
    (hcl : ∀ v : ℤ, IsClosed (cell ε η v)) (hUO : U ⊆ O)
    (hsep : ∀ p ∈ frontier O, ∀ q ∈ U, r ≤ dist p q)
    (hdiam : ∀ v : ℤ, (cell ε η v ∩ frontier O).Nonempty → ∀ p ∈ cell ε η v, ∀ q ∈ cell ε η v, dist p q < r)
    (hWE : srwLaw m a {x | vExitTime (interiorCellVertices ε η O) x = ⊤} = 0) :
    ∀ᵐ x ∂srwLaw m a, vExitTime (FrontierSeparation.meetVerts (cell ε η) U) x ≠ ⊤ := by
  rw [measure_eq_zero_iff_ae_notMem] at hWE
  filter_upwards [hWE] with x hx
  intro htop
  have hint : ∃ n, x n ∉ interiorCellVertices ε η O := by
    by_contra hcon
    push Not at hcon
    apply hx
    show vExitTime (interiorCellVertices ε η O) x = ⊤
    have hnot : ¬ ∃ n, x n ∉ interiorCellVertices ε η O := fun ⟨n, hn⟩ => hn (hcon n)
    simp [vExitTime, hnot]
  obtain ⟨n, hn⟩ := hint
  have hmeet : x n ∉ FrontierSeparation.meetVerts (cell ε η) U := by
    intro hmem
    obtain ⟨q, hq1, hqU⟩ := hmem
    rw [(hcl (x n)).closure_eq] at hq1
    by_cases hfr : (cell ε η (x n) ∩ frontier O).Nonempty
    · obtain ⟨p, hp1, hp2⟩ := hfr
      exact absurd (hdiam (x n) ⟨p, hp1, hp2⟩ p hp1 q hq1) (not_lt.2 (hsep p hp2 q hqU))
    · apply hn
      show x n ∈ cellVertices ε η O \ cellVertices ε η (frontier O)
      exact Set.mem_sdiff_of_mem (show (cell ε η (x n) ∩ O).Nonempty from ⟨q, hq1, hUO hqU⟩)
        (fun h => hfr (show (cell ε η (x n) ∩ frontier O).Nonempty from h))
  have hex : ∃ k, x k ∉ FrontierSeparation.meetVerts (cell ε η) U := ⟨n, hmeet⟩
  have hne : vExitTime (FrontierSeparation.meetVerts (cell ε η) U) x ≠ ⊤ := by
    simp [vExitTime, hex]
  exact hne htop

#print axioms MatedCRT.WalkExitW.ae_vExitTime_meetVerts_ne_top
#print axioms MatedCRT.WalkExitW.le_dist_of_frontier_thickening

end WalkExitW
end MatedCRT
