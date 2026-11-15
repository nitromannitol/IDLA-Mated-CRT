import MatedCRT.FirstPass.Derived.CellDiameterEvent
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeCells
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! # Local mesh bounds for embedded edges -/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology

namespace MatedCRT

/-- If a vertex lies in a disk and its cell meets a second cell, a local cell
mesh bound controls the distance between the two embedded vertices. -/
theorem vertexPoint_dist_le_of_maxCellDiam_le
    {ε R d : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 ≤ ε)
    (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hmesh : FirstPass.Derived.maxCellDiam ε η R ≤ ENNReal.ofReal d)
    {j k : ℤ} (hj : vertexPoint ε η j ∈ ball (0 : ℂ) R)
    (hmeet : (cell ε η j ∩ cell ε η k).Nonempty) :
    dist (vertexPoint ε η j) (vertexPoint ε η k) ≤ 2 * d := by
  have hcell := CellDiameterEvent.cell_dist_le_of_maxCellDiam_le hη hd0
    (ρ₁ := R + 1) (by simpa only [add_sub_cancel_right] using hmesh)
  have hjcell := Sec7.vertexPoint_mem_own_cell hε η j
  have hjball : vertexPoint ε η j ∈ ball (0 : ℂ) (R + 1) :=
    ball_subset_ball (by linarith) hj
  have hjbound := hcell j ⟨vertexPoint ε η j, hjcell, hjball⟩
  obtain ⟨z, hzj, hzk⟩ := hmeet
  have hzdist := hjbound z hzj (vertexPoint ε η j) hjcell
  have hzball : z ∈ ball (0 : ℂ) (R + 1) := by
    rw [mem_ball] at hj ⊢
    linarith [dist_triangle z (vertexPoint ε η j) (0 : ℂ)]
  exact Sec7.vertexPoint_dist_le_of_cells_meet hε ⟨z, hzj, hzk⟩ hjbound
    (hcell k ⟨z, hzk, hzball⟩)

/-- Along positive meshes tending to zero, the probability that an edge with
one endpoint in a fixed disk has a macroscopic embedded length tends to zero. -/
theorem tendsto_measure_long_local_edges_of_valid
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R a : ℝ) (ha : 0 < a) :
    Tendsto (fun n => S.P {ω | ∃ j k : ℤ,
      S.mult (ε n) ω j k ≠ 0 ∧ vertexPoint (ε n) (⇑(η' ω)) j ∈ ball (0 : ℂ) R ∧
      a < dist (vertexPoint (ε n) (⇑(η' ω)) j) (vertexPoint (ε n) (⇑(η' ω)) k)})
      atTop (𝓝 0) := by
  let d : ℝ := min (a / 4) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; linarith [min_le_right (a / 4) (1 / 2 : ℝ)]
  have hda : 2 * d < a := by dsimp [d]; linarith [min_le_left (a / 4) (1 / 2 : ℝ)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (FirstPass.Derived.hdiam_of_isValid hS hae hε0 R d hd) (fun _ => zero_le) ?_
  intro n
  apply measure_mono_ae
  filter_upwards [hae, adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hη hmeet
  rintro ⟨j, k, hjk, hj, hlong⟩
  by_contra hnot
  have hmesh : FirstPass.Derived.maxCellDiam (ε n) (⇑(η' ω)) R ≤ ENNReal.ofReal d :=
    not_lt.mp hnot
  have hc := hmeet (ε n) (hε n) j k hjk
  rw [← hη] at hc
  have hbound := vertexPoint_dist_le_of_maxCellDiam_le (η' ω).continuous (hε n).le
    hd.le hd1 hmesh hj hc
  linarith

end MatedCRT
end
