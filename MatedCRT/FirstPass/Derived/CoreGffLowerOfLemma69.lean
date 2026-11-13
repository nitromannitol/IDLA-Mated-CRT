import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.FirstPass.Derived.MepsLowerAssembly
import MatedCRT.FirstPass.Derived.CoreExitTimeOfBlocks

/-!
# The counted forms of Theorems 1.4 and 1.6 with the lower half of (1.8) derived from BG20 Lemma 6.9

The counted forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling` take the lower half `F_ε(c₁ ε⁻¹) < 1/2` of the distribution
bounds of the exit time (Berestycki-Gwynne (1.8)) as a hypothesis. By `mεCdf_lower_of_exitTimeLowerTail` it follows
from the Green kernel lower bound (Lemma 2.13), the exit time upper bound (Lemma 2.18) and the bound on the number of
crossings of the small balls before the exit (Berestycki-Gwynne Lemma 6.9, with `ψ₀` depending only on `ζ`, `ℓ` and
`γ`, as printed). Lemma 2.18 holds as soon as the Green kernel upper bound (Lemma 2.14) does: it follows from
Lemma 2.14, the crude Green function bound, the cell size estimate and the block degree estimate
(`exitTimeUpperBoundStmt_of_blockDegree`), and the last three hold for every model.

Hence the counted forms of Theorems 1.4 and 1.6 hold with the hypothesis `hlow` replaced by Lemma 6.9.

## Main statements

* `MatedCRT.FirstPass.Derived.exitTimeUpperBoundStmt_of_greenKernelUpper`: Lemma 2.18 from Lemma 2.14.
* `MatedCRT.FirstPass.Derived.mεCdf_lower_of_lemma69`: the lower half of (1.8) from Lemmas 2.13, 2.14 and BG20
  Lemma 6.9.
* `MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs_lemma69`,
  `MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs_lemma69`: the counted forms of Theorems 1.4 and 1.6 with
  BG20 Lemma 6.9 in place of the lower half of (1.8).
-/

open MeasureTheory Filter Topology Set Metric
open ProbabilityTheory _root_.MatedCRTHarmonic.MatedCRT
open _root_.MatedCRT.KilledOccupation _root_.HarmonicBalls _root_.MarkovProcess

namespace MatedCRT.FirstPass.Derived

/-- **Lemma 2.18 from the Green kernel upper bound.** The exit time upper bound (Lemma 2.18) follows from the Green
kernel upper bound (Lemma 2.14): `exitTimeUpperBoundStmt_of_blockDegree` with the crude Green function bound
(`greenFunctionCrudeBoundStmt_holds`), the cell size estimate (`cellSizeEstimateStmt_holds`) and the block degree
estimate (`hblock_of_degreeBound degreeBoundInput_holds`), which hold for every model. -/
theorem exitTimeUpperBoundStmt_of_greenKernelUpper {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮) : MatedCRT.ExitTimeUpperBoundStmt 𝒮 :=
  exitTimeUpperBoundStmt_of_blockDegree h12 (MatedCRT.greenFunctionCrudeBoundStmt_holds 𝒮)
    (cellSizeEstimateStmt_holds 𝒮) (hblock_of_degreeBound (MatedCRT.degreeBoundInput_holds 𝒮))

/-- **The lower half of (1.8) from BG20 Lemma 6.9.** For `0 < γ < 2` there is `c₁ > 0` such that, for every valid
environment, `F_ε(c₁ ε⁻¹) < 1/2` for all small `ε`. The inputs are the Green kernel upper bound (Lemma 2.14), the
Green kernel lower bound (Lemma 2.13) and Berestycki-Gwynne Lemma 6.9 (`h632`): for `ℓ > 1` and `ζ ∈ (0,1)` there is
a superpolynomially decaying `ψ₀`, independent of the environment, such that with polynomially high probability the
walk started from any vertex of `B_{ρ-δ}` makes at least `⌊δ^{-(2-ζ)(ℓ-1)}⌋` successive exits from balls of radius
`δ^ℓ` before leaving the ball of radius `δ` about its starting point, except with probability at most `ψ₀(δ)`.
This is `mεCdf_lower_of_exitTimeLowerTail` with Lemma 2.18 supplied by
`exitTimeUpperBoundStmt_of_greenKernelUpper`. -/
theorem mεCdf_lower_of_lemma69 {𝒮 : SpaceFillingSLEModel}
    (h12 : GreenKernelUpperBoundStmt 𝒮) (h13 : GreenKernelLowerBoundStmt 𝒮)
    (h632 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ℓ : ℝ, 1 < ℓ →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2 :=
  mεCdf_lower_of_exitTimeLowerTail h13 (exitTimeUpperBoundStmt_of_greenKernelUpper h12) h632

end MatedCRT.FirstPass.Derived

namespace MatedCRT

section CountedLemma69

/-- The counted form `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling` of Theorem 1.4 with the lower half
`F_ε(c₁ ε⁻¹) < 1/2` of (1.8) supplied by `FirstPass.Derived.mεCdf_lower_of_lemma69` from the Green kernel bounds
`h12`, `h13` and Berestycki-Gwynne Lemma 6.9 (`h632`). Same conclusion. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_lemma69
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (h632 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ℓ : ℝ, 1 < ℓ →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮) (h12 : GreenKernelUpperBoundStmt 𝒮)
    (h13 : GreenKernelLowerBoundStmt 𝒮)
    (h15 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hGFF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → HarmonicBalls.dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (HarmonicBalls.dyadicScale (n k))
            (HarmonicBalls.dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => HarmonicBalls.dyadicScale (n k)) z r
              (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C)
    (hscale : QuantumConeScalingInput) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs_envScaling ν h1 h2
    (FirstPass.Derived.mεCdf_lower_of_lemma69 h12 h13 h632) h10 h11 h12 h13 h15 hGFF hscale

/-- The counted form `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling` of Theorem 1.6 with the lower half
`F_ε(c₁ ε⁻¹) < 1/2` of (1.8) supplied by `FirstPass.Derived.mεCdf_lower_of_lemma69` from the Green kernel bounds
`h12`, `h13` and Berestycki-Gwynne Lemma 6.9 (`h632`). Same conclusion. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_lemma69
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (h632 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ℓ : ℝ, 1 < ℓ →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ)
    (h10 : HasReferenceEnvironments 𝒮)
    (h11 : RandomWalkToLBMStmt 𝒮) (h12 : GreenKernelUpperBoundStmt 𝒮)
    (h13 : GreenKernelLowerBoundStmt 𝒮)
    (h15 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hGFF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → HarmonicBalls.dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (HarmonicBalls.dyadicScale (n k))
            (HarmonicBalls.dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => HarmonicBalls.dyadicScale (n k)) z r
              (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C)
    (hscale : QuantumConeScalingInput) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs_envScaling ν h1 h2
    (FirstPass.Derived.mεCdf_lower_of_lemma69 h12 h13 h632) h10 h11 h12 h13 h15 hGFF hscale

end CountedLemma69

end MatedCRT
