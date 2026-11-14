import MatedCRT.FirstPass.Derived.InterpKernelTightFromScaling
import MatedCRT.FirstPass.S6j.ExitTimeLowerTail
import MatedCRT.FirstPass.S6j.ExitTimeUpperTail

/-!
# The scaling theorems of Berestycki-Gwynne Section 6.4 from the uniform-start invariance principle

`hEqLaw_of_scaling`, `hEqPath_of_scaling` and `isTightMeasureSet_data_interpWalkLaw_of_scaling` take the estimates (6.32)
and (6.36) of Lemmas 6.9 and 6.10 (`h632`, `h636`) as hypotheses. Both follow from the uniform-start form of the
invariance principle for the walk on the mated-CRT map, the named literature input `GMS21UniformStartInput`
(`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`, `ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart`). The forms
below replace the binders `h632` and `h636` by `hN4`. Same conclusions.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MarkovProcess (ContinuousPath)
open MatedCRT.SuccessiveExitGaps

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Equicontinuity in law of the quenched walks (`hEqLaw_of_scaling`) with the estimates (6.32) and (6.36) of BG20 Lemmas 6.9 and 6.10 supplied by the uniform-start invariance principle.** The binders `h632` and `h636` of `hEqLaw_of_scaling` are replaced by the named literature input `hN4`
(`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`, `ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart`). Same conclusion. -/
theorem hEqLaw_of_uniformStart {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hbd : ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω)
          (ball (0 : ℂ) (1 / 2) \ ball (0 : ℂ) (1 / 2 - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X <
            vHitTime (cellVertices ε (S.η ω)
              (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}})
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a :=
  hEqLaw_of_scaling h32 h213 h214 h217 h219 hEnvS (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart hN4) hγ hγ2 (ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart hN4 γ hγ hγ2) hbd hS hae hε0 hε

/-- **Failure of the vertex path laws (`hEqPath_of_scaling`) with the estimates (6.32) and (6.36) supplied by the uniform-start invariance principle.** The binders `h632` and `h636` of `hEqPath_of_scaling` are replaced by the named literature input `hN4`
(`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`, `ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart`). Same conclusion. -/
theorem hEqPath_of_uniformStart {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R L a : ℝ, 0 < L → 0 < a → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ᶠ n in atTop,
      S.P {ω | ∃ j : ℤ, vertexPoint (eps n) (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
        ENNReal.ofReal a <
          ((walkPathLaw S (fun ω => vertexPoint (eps n) (⇑(η' ω))) (S.mε_nonneg (eps n)) (eps n) j ω :
            ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
            (pathModulusFailure (E := ℂ) L δ)} ≤ ENNReal.ofReal a :=
  hEqPath_of_scaling h213 h214 h217 hEnvS (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart hN4) hγ hγ2 (ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart hN4 γ hγ hγ2) hS hae hε0 hε

/-- **Tightness of the pairs (datum, interpolated quenched walk law) with the estimates (6.32) and (6.36) supplied by the uniform-start invariance principle.** The binders `h632` and `h636` of `isTightMeasureSet_data_interpWalkLaw_of_scaling` are replaced by the named literature input `hN4`
(`ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`, `ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart`). Same conclusion. -/
theorem isTightMeasureSet_data_interpWalkLaw_of_uniformStart {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hbd : ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω)
          (ball (0 : ℂ) (1 / 2) \ ball (0 : ℂ) (1 / 2 - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X <
            vHitTime (cellVertices ε (S.η ω)
              (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}})
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0))
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [PolishSpace Data]
    [BorelSpace Data] (D : Ω → Data) (hD : AEMeasurable D S.P) :
    IsTightMeasureSet {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) |
      ∃ n, ν = S.P.map fun ω => (D ω, interpWalkLaw S η' (eps n) ω)} :=
  isTightMeasureSet_data_interpWalkLaw_of_scaling h32 h213 h214 h217 h219 hEnvS (ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart hN4) hγ hγ2 (ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart hN4 γ hγ hγ2) hbd hS hη' hae hε0 hε D hD

end MatedCRT.FirstPass.Derived
