import MatedCRT.FirstPass.S3i.LensFlooredGood
import MatedCRT.FirstPass.S3i.LensFlooredQuenched

/-!
# The quenched lens step from the floored uniform boundary estimate (MQ-li-9)

`quenchedLensStep_of_flooredUniform` derives, from
`FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮` (S3i/LensFloored.lean) and the cell-size and scaling inputs
(`CellSizeEstimateStmt`, `MepsScalingInput`), the exact `QuenchedLensStep 𝒮`.
The lens exponent is `b = min (1 / (2 + γ) ^ 2) β` (MQ-li-9 step 1), so `b ≤ β`; the quenched bounds are the closed
floored form `quenchedBoundsOnGoodFlooredStmt_closed` (S3i/LensFlooredQuenched.lean), which takes `ε ≤ 1` and `b ≤ β`.
The exit input is the theorem `srwLaw_vExitTime_lt_top_fp36` (as in `quenchedBoundsOnGoodStmt_closed`).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The floored quenched bound on the good environment: the statement of `QuenchedBoundsOnGoodStmt` (S3i/LensStep.lean:29)
for `FP36GoodEnvFloored`, with the additional hypotheses `ε ≤ 1` and `b ≤ β`. -/
def QuenchedBoundsOnGoodFlooredStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω},
    0 < ε → ε ≤ 1 → 0 < b → b ≤ β → 0 < ν → 0 < A → 0 < r → ρ₀ < ρ₁ → 0 < S.mε ε →
    64 * ε ^ b ≤ ε ^ (b / 2) → closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ →
    FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω →
    let μ := srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
    μ {x | ¬ SameWalkGood S r z ε ω x} = 0 ∧
    μ {x | SameWalkGood S r z ε ω x ∧
      ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
      ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2))

/-- `QuenchedBoundsOnGoodFlooredStmt`, proved from the almost-sure exit input (the floored form of
`quenchedBoundsOnGoodStmt_closed`). -/
theorem quenchedBoundsOnGoodFlooredStmt_closed : QuenchedBoundsOnGoodFlooredStmt := by
  intro Ω _ S ρ₀ ρ₁ b ν A β r ε z y ω hε hε1 hb hβb hν hA hr hρ hmpos hscale houter hgood
  exact quenchedBoundsOnGood_fp36_of_exit_floored srwLaw_vExitTime_lt_top_fp36 hε hε1 hb hβb hν hA hr hρ
    hmpos hscale houter hgood

/-- **The quenched lens step from the floored uniform boundary estimate**. -/
theorem quenchedLensStep_of_flooredUniform {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (hU : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    QuenchedLensStep 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨β, b, hβ0, hb, hbβ, hcommon⟩ := commonGood_fp36_floored h28 hm hU γ hγ0 hγ2
  refine ⟨b, hb, fun ρ hρ0 hρ1 Ω _ S hS r z hr hball ψ H χ y hadm => ?_⟩
  obtain ⟨hρρ₀, hρ₀ρ₁, hρ₁1, ν, A, κ, C₁, ε₀, hν, hA, hκ, hC₁, hε₀, hε₀1, G, hG⟩ :=
    hcommon ρ hρ0 hρ1 Ω S hS r z hr hball y hadm.2.2.2
  refine ⟨κ, ν, A * (96 : ℝ) ^ ν, ε₀, hκ, hν, mul_nonneg hA.le (Real.rpow_nonneg (by norm_num) _), hε₀,
    G, C₁, hC₁, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hmpos, -, hscale, hcl, hPG, hgood⟩ := hG ε hε hεε₀
  refine ⟨hPG, fun ω hω => ?_⟩
  obtain ⟨h0, hfar⟩ := quenchedBoundsOnGoodFlooredStmt_closed hε (hεε₀.le.trans hε₀1) hb hbβ hν hA hr hρ₀ρ₁
    hmpos hscale hcl (hgood ω hω)
  exact ⟨(le_of_eq h0).trans zero_le, hfar⟩

end FirstPass36
end MatedCRT
