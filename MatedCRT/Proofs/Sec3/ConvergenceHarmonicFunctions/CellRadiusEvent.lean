import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryData
import MatedCRT.Proofs.Sec7.CrudeUpperBound.PolyHighProb

/-! # Cell-radius event from the cell-size estimate -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology Tightness _root_.HarmonicBalls

/-- On a bounded target set inside the comparison disk, the cell-size estimate
controls every point in every cell meeting the target by its marked vertex. -/
theorem cellRadius_polyHighProb_of_cellSize (𝒮 : SpaceFillingSLEModel)
    (h28 : CellSizeEstimateStmt 𝒮) {γ ζ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {K : Set ℂ} (hK : K ⊆ ball 0 ρ) :
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) K,
      ∀ p ∈ cell ε (S.η ω) a,
        dist (vertexPoint ε (S.η ω) a) p ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)} := by
  have hcont : ∀ᵐ ω ∂S.P, Continuous (S.η ω) := by
    filter_upwards [hS.isAreaParametrized] with ω hω
    exact hω.1
  refine polyHighProb_mono_ae (h28 γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS) hcont ?_
  intro ε hε ω hsize hη a ha p hp
  obtain ⟨q, hqa, hqK⟩ := ha
  have hmeet : (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := ⟨q, hqa, hK hqK⟩
  have hb : Bornology.IsBounded (cell ε (S.η ω) a) := (isCompact_Icc.image hη).isBounded
  exact (dist_le_diam_of_mem hb (vertexPoint_mem_cell hε a) hp).trans (hsize a hmeet).2

/-- A disk whose open ball is inside `B(0, ρ)` has closure inside every
strictly larger comparison ball. -/
theorem closedBall_subset_larger_ball {r ρ ρ' : ℝ} {z : ℂ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hball : ball z r ⊆ ball 0 ρ) : closedBall z r ⊆ ball 0 ρ' := by
  have hc := closure_mono hball
  rw [closure_ball z hr.ne', closure_ball (0 : ℂ) hρ.ne'] at hc
  exact hc.trans (closedBall_subset_ball hρρ')

/-- The cell-radius event is polynomially likely on the closed target disk,
including its boundary cells, after enlarging the comparison disk. -/
theorem closedBall_cellRadius_polyHighProb_of_cellSize (𝒮 : SpaceFillingSLEModel)
    (h28 : CellSizeEstimateStmt 𝒮) {γ ζ ρ ρ' r : ℝ} {z : ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hρ'1 : ρ' < 1) (hr : 0 < r)
    (hball : ball z r ⊆ ball 0 ρ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r),
      ∀ p ∈ cell ε (S.η ω) a,
        dist (vertexPoint ε (S.η ω) a) p ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)} :=
  cellRadius_polyHighProb_of_cellSize 𝒮 h28 hγ hγ2 hζ hζ1 (hρ.trans hρρ') hρ'1 S hS
    (closedBall_subset_larger_ball hr hρ hρρ' hball)

end MatedCRT
