import MatedCRT.Proofs.Sec5.LLowerBound.LocalData
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Core
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer

/-!
# Applying the Green-kernel estimate on a smaller ball

The centre and all cells used in the local Green-sum argument lie in a fixed
ambient ball when the radius is smaller than the distance to its boundary.
-/

namespace MatedCRT

open MeasureTheory Set Metric

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

/-- The local witnesses follow uniformly from the Green and counting events,
an ambient cell-diameter bound, and two lower bounds on the ball mass. -/
theorem localData_of_green_counting {m : ℤ → ℤ → ℕ} {μ : Measure ℂ}
    {η : ℝ → ℂ} {ε δ ρ ρ' R r d C ω α β : ℝ} {A : Set ℤ} {a : ℤ}
    (hη : IsAreaParametrized μ η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hβ : 0 < β) (hA : A.Finite) (ha : a ∈ A)
    (hdist : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η A)))
    (hpoint : vertexPoint ε η a ∈ ball 0 ρ)
    (hρ' : 0 ≤ ρ') (hsep : ρ + R ≤ ρ') (hεmargin : ρ ≤ ρ' - ε ^ ω)
    (hεR : ε ^ ω ≤ R) (hR : R ≤ δ / 2) (hr : r ≤ R / 3)
    (hR0 : 0 ≤ R) (hgap : r + d < R) (hd : d ≤ δ / 4)
    (hC : 0 < C) (hinv : Real.exp (3 / 2 * C) ≤ ε⁻¹)
    (hscale : Real.exp (3 / 2 * C) * (r + d) ≤ R)
    (hgreen : ConstantOrderDiv.GreenLowerAt m ε η ρ' ω C)
    (hcount : ConstantOrderDiv.CountingAt ε η μ ρ' α β)
    (hsmall : ∀ b ∈ cellVertices ε η (ball 0 (ρ + δ / 2)),
      diam (cell ε η b) ≤ d)
    (herr : ε ^ α ≤ (μ (ball (vertexPoint ε η a) r)).toReal / 2)
    (hmass : ε ^ (1 / 4 : ℝ) ≤ (μ (ball (vertexPoint ε η a) r)).toReal / 4) :
    ∃ (D Cset : Set ℤ) (α' M : ℝ), Cset.Finite ∧ D ⊆ Cset ∧ Cset ⊆ A ∧
      (∀ b ∈ D, (1 / 2 : ℝ) ≤ greenKernel m Cset a b) ∧
      ε⁻¹ * M - ε ^ (-1 + α') ≤ (D.ncard : ℝ) ∧
      ε ^ α' ≤ M / 2 ∧ ε ^ (1 / 4 : ℝ) ≤ M / 4 := by
  have hp : ‖vertexPoint ε η a‖ < ρ := by simpa [mem_ball_zero_iff] using hpoint
  have har : a ∈ cellVertices ε η (ball 0 (ρ' - ε ^ ω)) :=
    ⟨_, ConstantOrderDiv.vertexPoint_mem_cell hε.le η a,
      ball_subset_ball hεmargin hpoint⟩
  have hmargin : ‖vertexPoint ε η a‖ + R ≤ ρ' := by linarith
  have hrR : r ≤ R := by linarith
  apply localData_of_geometry_and_counting (ρ := ρ') hη hε hε1 hδ hβ hA ha hdist hR hrR
    hgap hd hC hinv hscale
  · exact cell_diam_local_of_ambient (ball_subset_ball_of_norm_add (by linarith)) hsmall
  · exact green_lower_on_smaller_ball hgreen har hρ' hmargin hεR hr
  · exact ball_subset_ball_of_norm_add (by linarith)
  · intro E f w hE hf hl hw
    exact (hcount E f w hE hf hl hw).1
  · exact herr
  · exact hmass

end MatedCRT
