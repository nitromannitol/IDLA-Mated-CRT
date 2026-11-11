import MatedCRT.FirstPass.S3t.Defs
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity
import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-!
# Truncated quenched laws: the path-set hypotheses of Step 2 (fp-S3t-path-continuity, z2)

Step 2 (`MatedCRT.TruncatedLaws.quenched_integral_tendsto_of_bl_of_ae_continuous`, `S3t/BLExtension.lean`) is stated on a
path set `𝒞 : Set (ℝ≥0 → ℂ)` with two hypotheses:

* `hW𝒞 : ∀ ε ω, ∀ᵐ a ∂(μ ε ω), W ε ω a ∈ 𝒞` (the quenched walk paths lie in `𝒞`);
* `hX𝒞 : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, X ω b ∈ 𝒞` (the Brownian limit paths lie in `𝒞`).

For the instance used by the continuum-under-discrete Step 5 (`S3t/ContinuumUnderDiscrete.lean`), with
`𝒞 = {w | Continuous w}`, `W ε ω a = interpolatedWalk ε (S.η ω) (S.mε ε) a` on the walk laws `srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)`,
and `X ω b = rescaledLBMPath (S.clock ω) S.m₀ b` on `ν = planarBrownianMotion y`, both hypotheses are discharged here.

* `hW𝒞` needs no hypothesis: every interpolated walk is continuous (`MatedCRT.continuous_interpolatedWalk`).
* `hX𝒞` uses only the clock field `MatedCRTEnv.IsValid.isLQGClock`: for almost every `ω`, almost every Brownian
  path `b` has `S.clock ω b` a time-change clock (`IsTimeChangeClock`: continuous, strictly increasing, `0 ↦ 0`,
  `→ ∞`), and then the rescaled LBM path is continuous (`MatedCRT.continuous_rescaledLBMPath`).

Positivity of `S.m₀` is not needed for either: continuity of `t ↦ m.toNNReal * t` holds for every real `m`.
-/

open MeasureTheory Filter Set HarmonicBalls
open scoped NNReal

namespace MatedCRT.TruncatedLaws

/-- An interpolated walk, the quenched path of Step 2 (`W`), is a continuous path for every walk `x` and every data
`ε`, `mε`, `η`: the piecewise linear interpolation has no jumps at the integer times `n / mε`. -/
theorem interpolatedWalk_mem_continuousPaths (ε mε : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) :
    interpolatedWalk ε η mε x ∈ {w : ℝ≥0 → ℂ | Continuous w} :=
  MatedCRT.continuous_interpolatedWalk ε mε η x

/-- `hW𝒞` for an arbitrary walk law: `μ`-almost every walk has continuous interpolated path. -/
theorem ae_interpolatedWalk_mem_continuousPaths (μ : Measure (ℕ → ℤ)) (ε mε : ℝ) (η : ℝ → ℂ) :
    ∀ᵐ x ∂μ, interpolatedWalk ε η mε x ∈ {w : ℝ≥0 → ℂ | Continuous w} :=
  Eventually.of_forall fun x => interpolatedWalk_mem_continuousPaths ε mε η x

/-- `hW𝒞` in the exact form of the Step 2 binder, for the quenched walk laws `srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)`
and `W ε ω a = interpolatedWalk ε (S.η ω) (S.mε ε) a` (as in `S3t/ContinuumUnderDiscrete.lean`, Step 5). -/
theorem ae_srwLaw_interpolatedWalk_mem_continuousPaths {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (y : ℂ) :
    ∀ ε ω, ∀ᵐ a ∂(srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)),
      interpolatedWalk ε (S.η ω) (S.mε ε) a ∈ {w : ℝ≥0 → ℂ | Continuous w} :=
  fun ε ω => ae_interpolatedWalk_mem_continuousPaths _ ε (S.mε ε) (S.η ω)

/-- `hX𝒞` in the exact form of the Step 2 binder, for the Brownian limit `X ω b = rescaledLBMPath (S.clock ω) S.m₀ b`
under `ν = planarBrownianMotion y`: for `S.P`-almost every `ω`, `planarBrownianMotion y`-almost every Brownian path `b`
gives a continuous rescaled Liouville Brownian motion. The clock is the one of `MatedCRTEnv.IsValid.isLQGClock`. -/
theorem ae_rescaledLBMPath_mem_continuousPaths {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (y : ℂ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {w : ℝ≥0 → ℂ | Continuous w} :=
  by
    filter_upwards [hS.isLQGClock] with ω hω
    filter_upwards [(hω y).2] with b hb
    exact MatedCRT.continuous_rescaledLBMPath hb

#print axioms interpolatedWalk_mem_continuousPaths
#print axioms ae_interpolatedWalk_mem_continuousPaths
#print axioms ae_srwLaw_interpolatedWalk_mem_continuousPaths
#print axioms ae_rescaledLBMPath_mem_continuousPaths

end MatedCRT.TruncatedLaws
