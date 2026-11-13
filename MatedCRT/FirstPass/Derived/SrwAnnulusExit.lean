import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import LatticeProb.LQG.ChainAnnulusCrossing

/-!
# The walk started in an annulus meets one of its two circles almost surely

Let `m` be a locally finite multiplicity with consecutive edges, let `cell k` be preconnected and nonempty for
every vertex `k`, and let adjacent vertices have intersecting cells. If the set of vertices whose cell lies in the
open annulus `a < ‖· - c‖ < b` is finite, then simple random walk started at a vertex of that set almost surely
visits a vertex whose cell meets the circle of radius `a` or of radius `b` around `c`.

Proof: the walk leaves the finite set almost surely (`ExitNull68.exit_null_of_finite`), its steps are stays or edges
(`ae_srwStep_legal`), so consecutive cells meet, and a chain of connected sets that leaves the annulus meets one of
its circles (`LatticeProb.LQG.exists_le_index_meets_circle_of_notMem_annulusCells`).
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- A path whose exit time from `A` is finite has a point outside `A`. -/
theorem exists_notMem_of_vExitTime_ne_top {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x ≠ ⊤) :
    ∃ n, x n ∉ A := by
  by_contra hcon
  apply h
  unfold vExitTime
  simp only [hcon, ↓reduceDIte]

/-- **Almost sure meeting of an annulus boundary.** -/
theorem ae_srwLaw_exists_meets_circle {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {cell : ℤ → Set ℂ} (hJ : ∀ k, IsPreconnected (cell k))
    (hne : ∀ k, (cell k).Nonempty) (hmeet : ∀ j k, m j k ≠ 0 → (cell j ∩ cell k).Nonempty)
    {c : ℂ} {a b : ℝ} (hF : (LatticeProb.LQG.annulusCells cell c a b).Finite) {x : ℤ}
    (hx : x ∈ LatticeProb.LQG.annulusCells cell c a b) :
    ∀ᵐ ξ ∂srwLaw m x, ∃ i, ∃ p ∈ cell (ξ i), dist p c = a ∨ dist p c = b := by
  have hexit : ∀ᵐ ξ ∂srwLaw m x, vExitTime (LatticeProb.LQG.annulusCells cell c a b) ξ ≠ ⊤ :=
    ae_iff.mpr (by simpa using ExitNull68.exit_null_of_finite hlf hcons hF x)
  filter_upwards [srwLaw_ae_start m x, FrontierSeparation.ae_srwStep_legal m x, hexit] with ξ h0 hstep hfin
  obtain ⟨n, hn⟩ := exists_notMem_of_vExitTime_ne_top hfin
  have hξ : ∀ i, (cell (ξ i) ∩ cell (ξ (i + 1))).Nonempty := by
    intro i
    rcases hstep i with h | h
    · rw [h, Set.inter_self]
      exact hne _
    · exact hmeet _ _ h
  have h0' : ξ 0 ∈ LatticeProb.LQG.annulusCells cell c a b := by
    rw [h0]
    exact hx
  obtain ⟨i, -, p, hp, hd⟩ := LatticeProb.LQG.exists_le_index_meets_circle_of_notMem_annulusCells hJ hξ h0'
    (hne (ξ 0)) hn
  exact ⟨i, p, hp, hd⟩

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.ae_srwLaw_exists_meets_circle
