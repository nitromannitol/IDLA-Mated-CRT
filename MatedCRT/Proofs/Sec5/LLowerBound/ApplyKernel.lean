import MatedCRT.Proofs.Sec5.LLowerBound.LocalData
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Core
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer

/-!
# Applying the Green-kernel estimate on a smaller ball

The centre and all cells used in the local Green-sum argument lie in a fixed
ambient ball when the radius is smaller than the distance to its boundary.
-/

namespace MatedCRT

open Set Metric

/-- The discrete cluster lies in the interior vertex set, without requiring
that the interior vertex set be connected. -/
theorem matedDiscreteCluster_subset_ballInterior {m : ℤ → ℤ → ℕ}
    {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    matedDiscreteCluster m ε η ρ t ⊆ ballInterior ε η ρ := by
  intro a ha
  by_contra haV
  have haW : a ∈ cellVertices ε η (closedBall 0 ρ) :=
    Sec7.cellVertices_mono ball_subset_closedBall ha.1
  have hle := Sec7.matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior
    (m := m) (η := η) (ρ := ρ) hε ht haW haV
  exact (not_lt_of_ge hle) ha.2

/-- A ball centred inside a concentric ball is contained in a larger ball. -/
theorem ball_subset_ball_of_norm_add {z : ℂ} {r ρ : ℝ}
    (h : ‖z‖ + r ≤ ρ) : ball z r ⊆ ball 0 ρ := by
  intro x hx
  rw [mem_ball, dist_zero_right]
  have hx' : ‖x - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hx
  have ht := norm_add_le (x - z) z
  have heq : x - z + z = x := sub_add_cancel x z
  rw [heq] at ht
  linarith

/-- A uniform diameter bound in an ambient ball applies to every cell meeting
a smaller ball inside it. -/
theorem cell_diam_local_of_ambient {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {r ρ d : ℝ}
    (hball : ball z r ⊆ ball 0 ρ)
    (hsmall : ∀ b ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η b) ≤ d) :
    ∀ b ∈ cellVertices ε η (ball z r), diam (cell ε η b) ≤ d := by
  intro b hb
  exact hsmall b (ConstantOrderDiv.cellVertices_mono' hball hb)

/-- Restrict the logarithmic part of Lemma 2.16 to a smaller ball around a
vertex, using a fixed margin from the ambient sphere. -/
theorem green_lower_on_smaller_ball {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {ρ ω C R r : ℝ} {a : ℤ}
    (hgreen : ConstantOrderDiv.GreenLowerAt m ε η ρ ω C)
    (ha : a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω)))
    (hρ : 0 ≤ ρ) (hmargin : ‖vertexPoint ε η a‖ + R ≤ ρ)
    (hεR : ε ^ ω ≤ R) (hr : r ≤ R / 3) :
    ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) r),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
        else min (R / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) R)) a b := by
  intro b hb
  exact (hgreen a ha R hεR (ConstantOrderDiv.le_infDist_sphere hρ hmargin) b
    (ConstantOrderDiv.cellVertices_mono' (ball_subset_ball hr) hb)).2

end MatedCRT
