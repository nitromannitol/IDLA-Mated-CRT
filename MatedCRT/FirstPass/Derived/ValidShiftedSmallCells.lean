import MatedCRT.Proofs.Infra.MatingOfTrees
import LatticeProb.Topology.ProperCurveSmallCells

/-! # Small shifted cells in valid environments -/

set_option autoImplicit false

open Set MeasureTheory Filter Metric

namespace MatedCRT

/-- On one event, every compact set meets only small shifted cells as the mesh tends to zero.
The mesh threshold may depend on the sample, compact set and requested diameter. -/
theorem MatedCRTEnv.IsValid.ae_shiftedCell_diam_small
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ K : Set ℂ, IsCompact K → ∀ d : ℝ, 0 < d →
      ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ∀ θ : ℝ, ∀ k : ℤ,
        ((S.η ω '' uIcc (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ))) ∩ K).Nonempty →
          diam (S.η ω '' uIcc (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ))) ≤ d := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω harea hproper
  let f : C(ℝ, ℂ) := ⟨S.η ω, harea.1⟩
  have hf : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr ⟨f.continuous, hproper⟩
  intro K hK d hd
  obtain ⟨δ, hδ, hsmall⟩ :=
    LatticeProb.exists_diam_shiftedCompactCell_le_of_isProperMap f hf hK hd
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ θ k hmeet
  simpa only [LatticeProb.coe_shiftedCompactCell, f, ContinuousMap.coe_mk] using
    hsmall ε hε hεδ θ k (by simpa only [LatticeProb.coe_shiftedCompactCell, f, ContinuousMap.coe_mk] using hmeet)

end MatedCRT
