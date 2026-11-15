import MatedCRT.FirstPass.Derived.LocalMeshSubsequence

/-! # Joint local mesh and edge bounds along a subsequence -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- A single deterministic subsequence gives both vanishing local cell diameters
and uniform decay of edges starting in the fixed disk. -/
theorem exists_subseq_local_mesh_and_edges_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      Tendsto (fun n => FirstPass.Derived.maxCellDiam (ε (φ n)) (⇑(η' ω)) R)
        atTop (𝓝 0) ∧
      ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, ∀ j k : ℤ,
        S.mult (ε (φ n)) ω j k ≠ 0 →
        vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ ball (0 : ℂ) R →
        dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
          (vertexPoint (ε (φ n)) (⇑(η' ω)) k) < a := by
  obtain ⟨φ, hφ, hφae⟩ := exists_subseq_maxCellDiam_tendsto_zero hS hae hε0 R
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae, hae, adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hlim hη hmeet
  refine ⟨hlim, ?_⟩
  intro a ha
  let d : ℝ := min (a / 4) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; linarith [min_le_right (a / 4) (1 / 2 : ℝ)]
  have hda : 2 * d < a := by dsimp [d]; linarith [min_le_left (a / 4) (1 / 2 : ℝ)]
  have hsmall := (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.mpr hd)
  filter_upwards [hsmall] with n hn
  intro j k hjk hj
  have hc := hmeet (ε (φ n)) (hε (φ n)) j k hjk
  rw [← hη] at hc
  have hb := vertexPoint_dist_le_of_maxCellDiam_le (η' ω).continuous (hε (φ n)).le
    hd.le hd1 hn.le hj hc
  linarith

end MatedCRT
end
