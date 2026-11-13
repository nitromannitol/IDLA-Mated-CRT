import MatedCRT.FirstPass.Derived.ExitCouplingGlue
import MatedCRT.FirstPass.Derived.InteriorCellGeometry

/-!
# Equicontinuity of the laws of the stopped walks: the cell geometry

This is the geometric instantiation of `levyProkhorovEDist_stoppedInterp_le` for the mated-CRT map
(Berestycki–Gwynne (2020), Proposition 6.12, Steps 1–2).  Let `z ∈ ℂ`, `δ ∈ (0,1)`, and suppose every
cell of a vertex whose cell meets `B_δ(z)` lies within `r0` of its vertex point `η(εk)`, with
`2 r0 + δ < √δ`.  Then every vertex of `V^ε(B_δ(z))` is an interior vertex of `B_{√δ}(z)`, and two such
vertices are at distance at most `2 δ + 2 r0` as embedded points.  With `A' = V^ε(B_{√δ}(z)) \ V^ε(∂B_{√δ}(z))`
and `A = V^ε(B_{ρ0}) \ V^ε(∂B_{ρ0})` for `B_{√δ}(z) ⊆ B_{ρ0}`, the laws of the walks from two vertices of
`V^ε(B_δ(z))` stopped at their exit time from `A` are then at Lévy–Prokhorov distance at most `r`, as soon as
the exit positions from `A'` are within `c` in total variation, the walks are good (quick exit from `A'`,
small oscillation up to the exit from `A`) outside probability `p`, and `c + p + p ≤ r`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingCells

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingEvents MatedCRT.ExitCouplingGlue
open MatedCRT.FirstPass36 (FiniteExitData)

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {ε : ℝ} {η : ℝ → ℂ}

/-- Vertices whose cells meet `B_δ(z)` are interior vertices of `B_{√δ}(z)` when all their cells lie
within `r0` of the vertex points and `2 r0 + δ < √δ`. -/
lemma cellVertices_subset_interiorCellVertices {z : ℂ} {δ r0 : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcell : ∀ v ∈ cellVertices ε η (ball z δ), ∀ p ∈ cell ε η v, dist (vertexPoint ε η v) p ≤ r0)
    (hr0 : 2 * r0 + δ < Real.sqrt δ) :
    cellVertices ε η (ball z δ) ⊆ interiorCellVertices ε η (ball z (Real.sqrt δ)) := by
  intro v hv
  have hδs : δ < Real.sqrt δ := (Real.lt_sqrt hδ.le).2 (by nlinarith)
  obtain ⟨p, hpc, hpb⟩ := hv
  refine ⟨⟨p, hpc, ball_subset_ball hδs.le hpb⟩, ?_⟩
  rintro ⟨q, hqc, hqf⟩
  have hqs : dist q z = Real.sqrt δ := mem_sphere.1 (frontier_ball_subset_sphere hqf)
  have h1 := hcell v ⟨p, hpc, hpb⟩ q hqc
  have h2 := hcell v ⟨p, hpc, hpb⟩ p hpc
  have h3 : dist p z < δ := mem_ball.1 hpb
  have h4 := dist_triangle q (vertexPoint ε η v) z
  have h5 := dist_triangle (vertexPoint ε η v) p z
  rw [dist_comm q (vertexPoint ε η v)] at h4
  linarith

/-- Two vertices of `V^ε(B_δ(z))` are at embedded distance at most `2 δ + 2 r0`. -/
lemma dist_vertexPoint_le {z : ℂ} {δ r0 : ℝ}
    (hcell : ∀ v ∈ cellVertices ε η (ball z δ), ∀ p ∈ cell ε η v, dist (vertexPoint ε η v) p ≤ r0)
    {x y : ℤ} (hx : x ∈ cellVertices ε η (ball z δ)) (hy : y ∈ cellVertices ε η (ball z δ)) :
    dist (vertexPoint ε η x) (vertexPoint ε η y) ≤ 2 * δ + 2 * r0 := by
  obtain ⟨p, hpc, hpb⟩ := hx
  obtain ⟨q, hqc, hqb⟩ := hy
  have h1 := hcell x ⟨p, hpc, hpb⟩ p hpc
  have h2 := hcell y ⟨q, hqc, hqb⟩ q hqc
  have h3 : dist p z < δ := mem_ball.1 hpb
  have h4 : dist q z < δ := mem_ball.1 hqb
  have h5 := dist_triangle (vertexPoint ε η x) p z
  have h6 := dist_triangle (vertexPoint ε η y) q z
  have h7 := dist_triangle (vertexPoint ε η x) z (vertexPoint ε η y)
  rw [dist_comm z (vertexPoint ε η y)] at h7
  linarith

/-- **Berestycki–Gwynne (2020), Proposition 6.12, Steps 1–2, for the mated-CRT map.**  For vertices `x, y`
of `V^ε(B_δ(z))`, the Lévy–Prokhorov edistance (local uniform metric) between the laws of the interpolated
walks from `x` and from `y`, stopped at their exit time from the interior vertices of `B_{ρ0}`, is at
most `r`, given the total variation bound `c` for the exit positions from the interior vertices of
`B_{√δ}(z)`, the bound `p` on the probability of a bad walk and the cell radius `r0`. -/
theorem levyProkhorovEDist_stoppedWalk_le {mult : ℤ → ℤ → ℕ} (hη : Continuous η) {z : ℂ}
    {δ r0 c ρ0 κ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcell : ∀ v ∈ cellVertices ε η (ball z δ), ∀ p ∈ cell ε η v, dist (vertexPoint ε η v) p ≤ r0)
    (hr0 : 2 * r0 + δ < Real.sqrt δ) (hball : ball z (Real.sqrt δ) ⊆ ball (0 : ℂ) ρ0)
    (hA' : FiniteExitData mult (interiorCellVertices ε η (ball z (Real.sqrt δ))))
    {x y : ℤ} (hx : x ∈ cellVertices ε η (ball z δ)) (hy : y ∈ cellVertices ε η (ball z δ))
    (hTV : ∀ T : Set ℤ,
      |(srwLaw mult x).real {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T} -
        (srwLaw mult y).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T}| ≤ c)
    {m : ℝ≥0} (hm : 0 < m) (ρt : ℝ≥0) (T0 r : ℝ≥0) {p : ℝ≥0∞}
    (hr : (T0 : ℝ) * (2 * κ + (2 * δ + 2 * r0)) + Real.exp (-(T0 : ℝ)) < r)
    (hbx : srwLaw mult x (walkGood (vertexPoint ε η) m
      (interiorCellVertices ε η (ball z (Real.sqrt δ))) (interiorCellVertices ε η (ball (0 : ℂ) ρ0))
      ρt κ x)ᶜ ≤ p)
    (hby : srwLaw mult y (walkGood (vertexPoint ε η) m
      (interiorCellVertices ε η (ball z (Real.sqrt δ))) (interiorCellVertices ε η (ball (0 : ℂ) ρ0))
      ρt κ y)ᶜ ≤ p)
    (hap : ENNReal.ofReal c + p + p ≤ r) :
    levyProkhorovEDist
      ((srwLaw mult x).map
        (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0))))
      ((srwLaw mult y).map
        (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η (ball (0 : ℂ) ρ0)))) ≤ r := by
  have hsub := cellVertices_subset_interiorCellVertices hδ hδ1 hcell hr0
  exact levyProkhorovEDist_stoppedInterp_le hA'
    (InteriorCellGeometry.interiorCellVertices_subset_of_subset_isOpen hη isOpen_ball hball)
    (hsub hx) (hsub hy) (srwLaw_exitPosition_le_add_of_abs_le mult _ x y hTV) (vertexPoint ε η) hm ρt
    (dist_vertexPoint_le hcell hx hy) T0 r hr hbx hby hap

end ExitCouplingCells
end MatedCRT
