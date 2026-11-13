import MatedCRT.FirstPass.Derived.LargestExitTimeFactor
import MatedCRT.FirstPass.Derived.CoreExitTimeOfBlocks
import MatedCRT.FirstPass.S1S2S8SA

/-!
# The scaling of `m_ε` from the lower bound on the annealed exit-time distribution

eq:meps-scaling (Berestycki-Gwynne arXiv:2003.10320 (1.8)) states `C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹`, where `m_ε` is the lower
median of the annealed distribution function `F_ε` of the exit time of the embedded walk `η(X^{0,ε})` from `B_{1/2}`.
The upper half of the distribution bounds, `1/2 ≤ F_ε(c₂ ε⁻¹)`, follows from Lemmas 2.17 and 2.18 (`mεCdf_upper`).
Hence, given Lemmas 2.17 and 2.18, eq:meps-scaling is equivalent to the lower half: there is `c₁ = c₁(γ) > 0` such that
for every valid environment `F_ε(c₁ ε⁻¹) < 1/2` for all small `ε`, i.e. the walk started at `a^ε_0` stays in `B_{1/2}`
for `c₁ ε⁻¹` steps with annealed probability more than `1/2` (BG20 Proposition 6.5 at `z = 0`).

## Main results

* `mεCdf_lower_of_mepsScalingInput`: the lower half follows from eq:meps-scaling.
* `mepsScalingInput_of_lower`, `mepsScalingInput_iff_lower`: eq:meps-scaling from the lower half and Lemmas 2.17
  and 2.18, and the equivalence.
* `mepsScalingInput_of_lower_of_blockDegree`: the same with Lemma 2.18 from the Green kernel upper bound, the crude
  Green function bound, the cell size estimate and the block degree estimate (A.43), and Lemma 2.17 from the volume
  growth (Lemma 2.7).
* `CertifiedReferenceModelCore.of_blockDegree_of_lower`: the certified reference model core from its conjuncts other
  than 3, 14 and 16, the crude Green function bound, the block degree estimate and the lower half.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- **The lower half of the distribution bounds from eq:meps-scaling.** If `C⁻¹ ε⁻¹ ≤ m_ε`, then
`F_ε(c₁ ε⁻¹) < 1/2` with `c₁ = C⁻¹ / 2`: below the lower median the distribution function is below `1/2`. -/
theorem mεCdf_lower_of_mepsScalingInput {𝒮 : SpaceFillingSLEModel} (h : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2 := by
  obtain ⟨C, hC1, hS⟩ := h γ hγ hγ2
  have hCi : 0 < C⁻¹ := inv_pos.2 (one_pos.trans hC1)
  refine ⟨C⁻¹ / 2, half_pos hCi, fun Ω _ S hSv => ?_⟩
  obtain ⟨ε₀, hε₀, hb⟩ := hS Ω S hSv
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  have hlt : C⁻¹ / 2 * ε⁻¹ < S.mε ε :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right (half_lt_self hCi) hεi) (hb ε hε hεε₀).1
  by_contra hge
  have hm := medianOf_le_of_half_le (mul_pos (half_pos hCi) hεi).le (not_lt.1 hge)
  rw [← S.mε_eq_medianOf_mεCdf] at hm
  exact absurd hlt (not_lt.2 hm)

/-- **eq:meps-scaling from the lower half** (BG20 (1.8)). Given Lemmas 2.18 and 2.17, if for every `γ ∈ (0, 2)`
there is `c₁ = c₁(γ) > 0` with `F_ε(c₁ ε⁻¹) < 1/2` for every valid environment and all small `ε`, then
`C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹`: the upper half `1/2 ≤ F_ε(c₂ ε⁻¹)` is `mεCdf_upper`. -/
theorem mepsScalingInput_of_lower {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2) :
    MepsScalingInput 𝒮 := by
  refine mepsScalingInput_of_cdf_bounds fun γ hγ hγ2 => ?_
  obtain ⟨c₁, hc₁, hl⟩ := hlow γ hγ hγ2
  obtain ⟨c₂, hc₂, hu⟩ := mεCdf_upper h218 h217 hγ hγ2
  refine ⟨c₁, c₂, hc₁, hc₂, fun Ω _ S hSv => ?_⟩
  obtain ⟨ε₁, hε₁, h1⟩ := hl Ω S hSv
  obtain ⟨ε₂, hε₂, h2⟩ := hu Ω S hSv
  exact ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεm =>
    ⟨h1 ε hε (hεm.trans_le (min_le_left _ _)), h2 ε hε (hεm.trans_le (min_le_right _ _))⟩⟩

/-- **eq:meps-scaling is equivalent to the lower half**, given Lemmas 2.18 and 2.17. -/
theorem mepsScalingInput_iff_lower {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) :
    MepsScalingInput 𝒮 ↔ ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2 :=
  ⟨fun h _ hγ hγ2 => mεCdf_lower_of_mepsScalingInput h hγ hγ2, mepsScalingInput_of_lower h218 h217⟩

/-- **eq:meps-scaling from the lower half and the block degree estimate.** Lemma 2.18 follows from the Green kernel
upper bound (Lemma 5.4), the crude Green function bound (Lemma 5.6), the cell size estimate (Lemma 2.8) and the block
degree estimate (A.43) (`exitTimeUpperBoundStmt_of_blockDegree`), and Lemma 2.17 from the volume growth (Lemma 2.7,
`volumeGrowthStmt_holds`). -/
theorem mepsScalingInput_of_lower_of_blockDegree {𝒮 : SpaceFillingSLEModel}
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h215 : GreenFunctionCrudeBoundStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)})
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2) :
    MepsScalingInput 𝒮 :=
  mepsScalingInput_of_lower
    (FirstPass.Derived.exitTimeUpperBoundStmt_of_blockDegree h214 h215 hcell hblock)
    (firstPass_2_17 FirstPass.Derived.volumeGrowthStmt_holds) hlow

end MatedCRT

namespace MatedCRT.FirstPass.Derived

/-- **The certified reference model core from the block degree estimate and the lower half of the exit-time
distribution bounds.** The conjuncts of `CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) other than 3
(eq:meps-scaling), 14 (Lemma 2.18) and 16 (BG20 Proposition 5.1), in the same order, together with the crude Green
function bound (Lemma 5.6), the block degree estimate (A.43) and the lower half `F_ε(c₁ ε⁻¹) < 1/2` of the
distribution bounds, give the core: conjunct 3 is `mepsScalingInput_of_lower_of_blockDegree`, and the rest is
`CertifiedReferenceModelCore.of_blockDegree`. -/
theorem CertifiedReferenceModelCore.of_blockDegree_of_lower {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h5 : MatedCRT.CellSizeEstimateStmt 𝒮) (h6 : MatedCRT.CountingMeasureConvergenceStmt 𝒮)
    (h7 : MatedCRT.DegreeMeasureConvergenceStmt 𝒮) (h8 : MatedCRT.FrozenConeScalingLaw 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRT.MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)})
    (hlow : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRT.MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_blockDegree h1 h2
    (MatedCRT.mepsScalingInput_of_lower_of_blockDegree h12 h215 h5 hblock hlow) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h15 h17 h215 hblock

end MatedCRT.FirstPass.Derived
