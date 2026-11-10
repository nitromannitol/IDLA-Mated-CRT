import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S3i.GoodEvent

/-!
# Lemma 8 and the closed annealed Lemma 3.6 (plan CHATGPT-221, section 8 and "Final change"; owner q4, task H8)

Route: the BE/lens route (operator note 11:27 UTC; the annulus route with `hgms` is dropped).
* `QuenchedBoundsOnGoodStmt`: plan Lemma 7 (section 7, `quenchedBoundsOnGood_fp36`, z12, `S3i/QuenchedBounds.lean`),
  as a named input with the plan's exact type, until it lands.
* `quenchedLensStep_of_BE`: plan Lemma 8. From `FrozenOneSidedBoundaryContinuity 𝒮` (the BE input), `CellSizeEstimateStmt`
  and `MepsScalingInput`, the exact `QuenchedLensStep 𝒮`: the exponent `b = 1/(2+γ)^2` and the good event come from
  `commonGood_fp36` (Lemma 3, `GoodEvent.lean`), the two quenched bounds from Lemma 7 with `C = A * 96^ν`.
* `firstPass_3_6_annealed_closed`: the final change of `firstPass_3_6_annealed` (`Proof.lean:262`, not edited): `hLens`
  is replaced by `quenchedLensStep_of_BE`, so the conclusion is unchanged and no `hLens` argument remains.

Terminology: quenched law `srwLaw` and exit time (Armstrong-Kuusi-Mourrat); Liouville-type boundary input (BE), GMS (3.31).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Lemma 7 of the plan (section 7), a named input until `quenchedBoundsOnGood_fp36` (z12) lands.** On a good environment
`FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω`, with `ε` small: the walk from the start vertex leaves the disc with probability one
(first estimate: exactly zero), and the far-exit event has quenched mass at most `A 96^ν ε^{νb/2}`. -/
def QuenchedBoundsOnGoodStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω},
    0 < ε → 0 < b → 0 < ν → 0 < A → 0 < r → ρ₀ < ρ₁ → 0 < S.mε ε →
    64 * ε ^ b ≤ ε ^ (b / 2) → closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ →
    FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω →
    let μ := srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
    μ {x | ¬ SameWalkGood S r z ε ω x} = 0 ∧
      μ {x | SameWalkGood S r z ε ω x ∧
        ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
        ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2))

/-- **Lemma 8 of the plan (section 8): the exact `QuenchedLensStep` from the BE input.** The exponent `b` is the
gamma-only `1/(2+γ)^2` of `commonGood_fp36` (not the `b` returned by the BE input). -/
theorem quenchedLensStep_of_BE {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hQB : QuenchedBoundsOnGoodStmt) :
    FrozenOneSidedBoundaryContinuity 𝒮 → QuenchedLensStep 𝒮 := by
  intro hBE γ hγ0 hγ2
  obtain ⟨b, hb, hcommon⟩ := commonGood_fp36 h28 hm hBE γ hγ0 hγ2
  refine ⟨b, hb, fun ρ hρ0 hρ1 Ω _ S hS r z hr hball ψ H χ y hadm => ?_⟩
  obtain ⟨hρρ₀, hρ₀ρ₁, hρ₁1, ν, A, κ, C₁, ε₀, hν, hA, hκ, hC₁, hε₀, G, hG⟩ :=
    hcommon ρ hρ0 hρ1 Ω S hS r z hr hball y hadm.2.2.2
  refine ⟨κ, ν, A * (96 : ℝ) ^ ν, ε₀, hκ, hν, mul_nonneg hA.le (Real.rpow_nonneg (by norm_num) _), hε₀,
    G, C₁, hC₁, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hmpos, -, hscale, hcl, hPG, hgood⟩ := hG ε hε hεε₀
  refine ⟨hPG, fun ω hω => ?_⟩
  obtain ⟨h0, hfar⟩ := hQB hε hb hν hA hr hρ₀ρ₁ hmpos hscale hcl (hgood ω hω)
  exact ⟨(le_of_eq h0).trans zero_le, hfar⟩

/-- **Corrected Lemma 3.6, annealed clause, closed (final change of `firstPass_3_6_annealed`, plan "Final change").**
`firstPass_3_6_annealed` (`S3i/Proof.lean:262`, unchanged) with `hLens` replaced by `quenchedLensStep_of_BE`. The only
remaining named input of the quenched route is `hQB` (Lemma 7, z12). -/
theorem firstPass_3_6_annealed_closed {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBE : FrozenOneSidedBoundaryContinuity 𝒮)
    (hQB : QuenchedBoundsOnGoodStmt) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed h211 h28 hm hexc h32 hBE (fun hBE' => quenchedLensStep_of_BE h28 hm hQB hBE')

#print axioms MatedCRT.FirstPass36.quenchedLensStep_of_BE
#print axioms MatedCRT.FirstPass36.firstPass_3_6_annealed_closed

end FirstPass36
end MatedCRT
