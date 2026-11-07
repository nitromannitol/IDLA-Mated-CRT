import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusIteration
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! # Nested exit regions and first hits of their boundaries -/

namespace MatedCRT

open Set MeasureTheory

/-- Exit times are monotone in the domain for every path. -/
theorem vExitTime_mono_domain {I J : Set ℤ} (hIJ : I ⊆ J) (x : ℕ → ℤ) :
    vExitTime I x ≤ vExitTime J x := by
  by_contra h
  have hlt : vExitTime J x < vExitTime I x := lt_of_not_ge h
  have hfin : vExitTime J x ≠ ⊤ := ne_top_of_lt hlt
  have hj : vExitTime J x = ((vExitTime J x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  have hmem : x (vExitTime J x).toNat ∈ I := mem_of_lt_vExitTime (hj ▸ hlt)
  exact apply_vExitTime_not_mem hj (hIJ hmem)

/-- When the exit vertex belongs to a boundary disjoint from the interior,
the first boundary hit equals the exit time. -/
theorem vHitTime_eq_vExitTime_of_exit_mem
    {I B : Set ℤ} {x : ℕ → ℤ} (hdisj : Disjoint I B)
    (hfin : vExitTime I x ≠ ⊤) (hboundary : vExitPosition I x ∈ B) :
    vHitTime B x = vExitTime I x := by
  have hk : vExitTime I x = ((vExitTime I x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  rw [hk]
  unfold vHitTime
  rw [vExitTime_eq_natCast_iff]
  constructor
  · intro h
    have hnotB := (natCast_lt_vExitTime_iff.1 h) (vExitTime I x).toNat le_rfl
    exact hnotB hboundary
  · intro j hj
    have hj' : (j : ℕ∞) < vExitTime I x := by rw [hk]; exact_mod_cast hj
    have hin := mem_of_lt_vExitTime hj'
    exact fun hB => (Set.disjoint_left.1 hdisj) hin hB

/-- If a walk starts in a region and its neighbours leave only through a
disjoint boundary, first boundary hit and first exit agree almost surely on
the event that the exit is finite. -/
theorem ae_vHitTime_eq_vExitTime_of_neighbours
    {m : ℤ → ℤ → ℕ} {I B : Set ℤ} {a : ℤ} (ha : a ∈ I)
    (hdisj : Disjoint I B)
    (hnb : ∀ a ∈ I, ∀ b, m a b ≠ 0 → b ∈ I ∪ B) :
    ∀ᵐ x ∂srwLaw m a, vExitTime I x ≠ ⊤ → vHitTime B x = vExitTime I x := by
  have hadj : ∀ᵐ x ∂srwLaw m a, ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (WalkSteps.srwLaw_nonadjacent_null m n a)] with x hx
    exact Classical.not_not.1 hx
  filter_upwards [srwLaw_ae_start m a, hadj] with x h0 hadj hfin
  apply vHitTime_eq_vExitTime_of_exit_mem hdisj hfin
  unfold vExitPosition
  induction hk : vExitTime I x using ENat.recTopCoe with
  | top => exact absurd hk hfin
  | coe k =>
    rw [ENat.toNat_natCast]
    have hout : x k ∉ I := apply_vExitTime_not_mem hk
    cases k with
    | zero => exact absurd (h0 ▸ ha) hout
    | succ j =>
      have hin : x j ∈ I := mem_of_lt_vExitTime (by rw [hk]; exact_mod_cast Nat.lt_succ_self j)
      rcases hadj j with h | h
      · exact absurd (h ▸ hin) hout
      · exact (hnb (x j) hin _ h).resolve_left hout

/-- Boundary hits of nested interiors occur in the order of the interiors. -/
theorem vHitTime_le_of_nested_exit_regions
    {I J B C : Set ℤ} {x : ℕ → ℤ} (hIJ : I ⊆ J)
    (hIB : Disjoint I B) (hJC : Disjoint J C)
    (hIfin : vExitTime I x ≠ ⊤) (hJfin : vExitTime J x ≠ ⊤)
    (hIexit : vExitPosition I x ∈ B) (hJexit : vExitPosition J x ∈ C) :
    vHitTime B x ≤ vHitTime C x := by
  rw [vHitTime_eq_vExitTime_of_exit_mem hIB hIfin hIexit,
    vHitTime_eq_vExitTime_of_exit_mem hJC hJfin hJexit]
  exact vExitTime_mono_domain hIJ x

/-- For a disk, its interior cells are disjoint from the cells meeting its
boundary circle. -/
theorem disjoint_interiorCellVertices_sphere
    (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Disjoint (interiorCellVertices ε η (Metric.ball z r))
      (cellVertices ε η (Metric.sphere z r)) := by
  apply Set.disjoint_left.2
  intro a ha hb
  exact ha.2 (by simpa [frontier_ball z (ne_of_gt hr)] using hb)

/-- A walk leaving disk-interior cells through their boundary has the same
first exit and circle-cell hitting times. -/
theorem ae_sphereCellHit_eq_diskInteriorExit
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hr : 0 < r) (ha : a ∈ interiorCellVertices ε η (Metric.ball z r))
    (hnb : ∀ a ∈ interiorCellVertices ε η (Metric.ball z r), ∀ b,
      m a b ≠ 0 → b ∈ interiorCellVertices ε η (Metric.ball z r) ∪
        cellVertices ε η (Metric.sphere z r)) :
    ∀ᵐ x ∂srwLaw m a,
      vExitTime (interiorCellVertices ε η (Metric.ball z r)) x ≠ ⊤ →
      vHitTime (cellVertices ε η (Metric.sphere z r)) x =
        vExitTime (interiorCellVertices ε η (Metric.ball z r)) x :=
  ae_vHitTime_eq_vExitTime_of_neighbours ha (disjoint_interiorCellVertices_sphere ε η z hr) hnb

end MatedCRT
