import MatedCRT.FirstPass.Derived.DegreeBoundAssembly
import MatedCRT.FirstPass.Derived.BlockRunningMinTail
import MatedCRT.FirstPass.Derived.RunningMinTailOfBrownian
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.Lemma25Tail

/-!
# The degree bound (GMS19 Lemma 2.6) from the exponential degree tail (GMS19 Lemma 2.5)

For a correlated two-sided Brownian motion, the number of labelled edge ends at a vertex of the ε-mated-CRT map
exceeds `n` with probability at most `c₀ e^{-c₁ n}`, with absolute constants (GMS19 Lemma 2.5, in the raw-degree form
`lemma25Tail_degree_tail` of the copied Bonanno module `MatedCRTHarmonic.MatedCRT.Lemma25Tail`). The law of the
boundary-length pair `S.bm` of a valid environment is the correlated Brownian law
(`MatedCRTEnv.IsValid.isCorrelatedBM2_map_bm`), so the tail holds for `S.bm` (`MatedCRTEnv.IsValid.edgeEndTail`),
and the assembly `MatedCRTEnv.IsValid.polyHighProb_degreeBound_of_edgeEndTail` (covering estimate, deterministic
window, union bound) gives the degree bound eq:degree-bound for every valid environment: `DegreeBoundInput 𝒮` is a
theorem (`degreeBoundInput_holds`).

## Main statements

* `MatedCRT.MatedCRTEnv.IsValid.edgeEndTail`
* `MatedCRT.degreeBoundInput_holds`
* `MatedCRT.FirstPass.Derived.degreeMeasureConvergenceStmt_of_envScaling_derived`
* `MatedCRT.FirstPass.Derived.CertifiedReferenceModelCore.of_runningMinTail_degree_derived`,
  `MatedCRT.FirstPass.Derived.CertifiedReferenceModelCore.of_runningMinTail_law_degree_derived`
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- **Exponential tail of the number of labelled edge ends** of the boundary-length pair of a valid environment
(GMS19 Lemma 2.5): `P[#{labelled edge ends at x} > n] ≤ c₀ e^{-c₁ n}` for every mesh `ε > 0`, vertex `x ∈ ℤ` and
`n ∈ ℕ`, with absolute constants. -/
theorem MatedCRTEnv.IsValid.edgeEndTail {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∃ C₀ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ∀ x : ℤ, ∀ n : ℕ,
      S.P {ω | (n : ℕ∞) < {d : (ℤ × ℤ × Bool) × Bool | MatedCRTHarmonic.MatedCRT.IsEdge ε (S.bm ω) d.1 ∧
        (if d.2 then d.1.2.1 else d.1.1) = x}.encard} ≤ ENNReal.ofReal (C₀ * Real.exp (-(C₁ * n))) := by
  obtain ⟨hlaw, hmeas⟩ := hS.isCorrelatedBM2_map_bm
  refine ⟨MatedCRTHarmonic.MatedCRT.lemma25TailC₀, MatedCRTHarmonic.MatedCRT.lemma25TailC₁,
    MatedCRTHarmonic.MatedCRT.lemma25TailC₁_pos, fun ε hε x n => ?_⟩
  exact (Measure.le_map_apply hmeas.aemeasurable
    {p | (n : ℕ∞) < MatedCRTHarmonic.MatedCRT.lemma25Degree ε p x}).trans
    (MatedCRTHarmonic.MatedCRT.lemma25Tail_degree_tail hlaw hε x n)

/-- **The degree bound eq:degree-bound holds** (GMS19 Lemma 2.6): for every space-filling SLE model, every
`γ ∈ (0, 2)`, `ρ ∈ (0, 1)` and every valid environment, with polynomially high probability as `ε → 0`,
`max_{a ∈ V^ε(B_ρ)} deg^ε(a) ≤ (log ε⁻¹)²`. -/
theorem degreeBoundInput_holds (𝒮 : SpaceFillingSLEModel) : DegreeBoundInput 𝒮 := by
  intro γ _ _ ρ _ hρ1 Ω _ S hS
  exact hS.polyHighProb_degreeBound_of_edgeEndTail hρ1.le hS.edgeEndTail

end MatedCRT

namespace MatedCRT.FirstPass.Derived

/-- `degreeMeasureConvergenceStmt_of_envScaling` with the degree bound supplied by `degreeBoundInput_holds`:
Lemma 2.10 (BG20 Cor. A.6) from the scaling of the environment alone. -/
theorem degreeMeasureConvergenceStmt_of_envScaling_derived {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮) : MatedCRT.DegreeMeasureConvergenceStmt 𝒮 :=
  degreeMeasureConvergenceStmt_of_envScaling hEnv (MatedCRT.degreeBoundInput_holds 𝒮)

/-- `CertifiedReferenceModelCore.of_runningMinTail_derived` with the degree bound supplied by
`degreeBoundInput_holds`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_degree_derived {ν : ℝ → Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_runningMinTail_derived h1 h2 h3 (MatedCRT.degreeBoundInput_holds 𝒮) h9 h10 h11
    h12 h13 h15 h17 h215 hEnv

/-- `CertifiedReferenceModelCore.of_runningMinTail_law_derived` with the degree bound supplied by
`degreeBoundInput_holds`. -/
theorem CertifiedReferenceModelCore.of_runningMinTail_law_degree_derived
    {ν : ℝ → Measure MatedCRT.SLEPathCode} {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h215 : MatedCRT.GreenFunctionCrudeBoundStmt 𝒮)
    (hEnv : MatedCRT.ConeEnvironmentScalingStep 𝒮) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  CertifiedReferenceModelCore.of_runningMinTail_law_derived h1 h2 h3 (MatedCRT.degreeBoundInput_holds 𝒮) h9 h10
    h11 h12 h13 h15 h215 hEnv

end MatedCRT.FirstPass.Derived
