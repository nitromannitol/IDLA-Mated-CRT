import MatedCRT.FirstPass.S5c.InteriorBall
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.Derived.InteriorCellGeometry
import MatedCRT.FirstPass.Derived.ExitCouplingNoShortTravel

/-!
# From the exit time lower tail to the no-short-travel input

The exit-within-`g`-steps probability of the walk from the interior vertices `w` of a ball, used in the
no-short-travel estimate for the coupling of the stopped walks (Berestycki–Gwynne (2020), Proposition 6.12,
Step 2), follows from the exit time lower tail (Lemma 6.11): the exit time from the interior vertices of
`B_{2 δ'}(η(w))` is at least the exit time from the vertices of `B_{δ'}(η(w))`, as soon as the cells meeting
`B_{δ'}(η(w))` have diameter below `δ'`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingHq

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- **Exit from a doubled ball.** If the cells meeting `B_s(z)` have diameter at most `d < s`, the vertices of
`B_s(z)` are interior vertices of `B_{2 s}(z)`, so the walk exits the interior vertices of `B_{2 s}(z)` before
time `g` only if it exits the vertices of `B_s(z)` before time `g`. -/
theorem srwLaw_exitInterior_lt_le (mult : ℤ → ℤ → ℕ) (a : ℤ) {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {s d : ℝ}
    (hs : 0 < s) (hd : d < s)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball z s).Nonempty → ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    (g : ℕ∞) :
    srwLaw mult a {X | vExitTime (interiorCellVertices ε η (ball z (2 * s))) X < g} ≤
      srwLaw mult a {X | vExitTime (cellVertices ε η (ball z s)) X < g} := by
  have h2 : 2 * s / 2 = s := by ring
  have hsub : cellVertices ε η (ball z s) ⊆ interiorCellVertices ε η (ball z (2 * s)) := by
    have := S5c.cellVertices_half_ball_subset_interior (ε := ε) (η := η) (z := z) (r := 2 * s) (d := d)
      (by linarith) (by rw [h2]; exact hd) (by rw [h2]; exact hdiam)
    rwa [h2] at this
  refine measure_mono fun X hX => ?_
  exact lt_of_le_of_lt (GreenTest68.vExitTime_le_of_subset hsub X) hX

/-- **The no-short-travel input from the exit time lower tail.** Let `ψ ≥ 0`, `T ≥ g`, and suppose that every
vertex `x` of `B_{R₁}` satisfies `P_x[τ_{B_{δ'}(η(x))} < T] ≤ ψ` (Lemma 6.11, with `T = ε⁻¹ δ'^χ`). If the cells
meeting `B_{ρ₁}` have diameter at most `d < δ'`, and `ρ₀ + δ' ≤ ρ₁`, `ρ₀ ≤ R₁`, then every interior vertex `w`
of `B_{ρ₀}` satisfies `P_w[τ_{B_{2 δ'}(η(w))} < g] ≤ ψ` for the exit time of the interior vertices. -/
theorem srwLaw_exitInterior_lt_le_of_exitTimeLower (mult : ℤ → ℤ → ℕ) {ε : ℝ} (hε : 0 ≤ ε) {η : ℝ → ℂ}
    (hη : Continuous η) {ρ₀ R₁ ρ₁ δ' d T ψ : ℝ} {g : ℕ} (hδ' : 0 < δ') (hd : d < δ')
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ₁).Nonempty → ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k,
      dist x y ≤ d)
    (hρ₁ : ρ₀ + δ' ≤ ρ₁) (hR₁ : ρ₀ ≤ R₁) (hg : (g : ℝ) ≤ T)
    (h611 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) R₁),
      srwLaw mult x {X | (vExitTime (cellVertices ε η (ball (vertexPoint ε η x) δ')) X : ℝ≥0∞) <
        ENNReal.ofReal T} ≤ ENNReal.ofReal ψ) :
    ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ₀),
      srwLaw mult w {X | vExitTime (interiorCellVertices ε η
        (ball (vertexPoint ε η w) (2 * δ'))) X < (g : ℕ∞)} ≤ ENNReal.ofReal ψ := by
  intro w hw
  have hwp : vertexPoint ε η w ∈ ball (0 : ℂ) ρ₀ := InteriorCellGeometry.vertexPoint_mem_of_mem_interiorCellVertices hε hη hw
  have hwc : w ∈ cellVertices ε η (ball (0 : ℂ) R₁) := by
    have h1 : w ∈ cellVertices ε η (ball (0 : ℂ) ρ₀) := hw.1
    exact Set.Nonempty.mono (inter_subset_inter_right _ (ball_subset_ball hR₁)) h1
  have hdiam' : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η w) δ').Nonempty → ∀ x ∈ cell ε η k,
      ∀ y ∈ cell ε η k, dist x y ≤ d := by
    intro k hk
    refine hdiam k (Set.Nonempty.mono (inter_subset_inter_right _ fun p hp => ?_) hk)
    rw [mem_ball] at hp hwp ⊢
    calc dist p 0 ≤ dist p (vertexPoint ε η w) + dist (vertexPoint ε η w) 0 := dist_triangle _ _ _
      _ < δ' + ρ₀ := add_lt_add hp hwp
      _ ≤ ρ₁ := by linarith
  refine (srwLaw_exitInterior_lt_le mult w hδ' hd hdiam' (g : ℕ∞)).trans (le_trans (measure_mono ?_) (h611 w hwc))
  intro X hX
  have h1 : (vExitTime (cellVertices ε η (ball (vertexPoint ε η w) δ')) X : ℝ≥0∞) < ((g : ℕ∞) : ℝ≥0∞) :=
    ENat.toENNReal_lt.2 hX
  have h2 : ((g : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal T := by
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hg
  exact lt_of_lt_of_le h1 h2

end ExitCouplingHq
end MatedCRT
