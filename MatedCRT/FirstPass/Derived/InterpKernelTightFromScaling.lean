import MatedCRT.FirstPass.Derived.InterpKernelDataTight
import MatedCRT.FirstPass.Derived.PathEqFromScaling

/-!
# Tightness of the interpolated quenched walk laws from the cone scaling

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Section 6.4 (Propositions 6.1 and 6.2, tightness part).  The tightness theorem
`isTightMeasureSet_data_interpWalkLaw` takes the two equicontinuity-in-law conditions of the quenched walks
(the modulus of the walk laws and the failure of the vertex path laws) as hypotheses; here they are supplied
by `hEqLaw_of_scaling` and `hEqPath_of_scaling`, whose hypotheses (the cone scaling of valid environments,
the exit-time bounds of Section 2, the estimates (6.32) and (6.36) of Lemmas 6.9 and 6.10 and the bound of
Lemma 6.13) stay as hypotheses.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MarkovProcess (ContinuousPath)
open MatedCRT.SuccessiveExitGaps

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Tightness of the pairs (datum, interpolated quenched walk law) from the cone scaling.**  For a valid
environment `S` with embedded curves `η'`, mesh sizes `ε_n → 0` and an almost everywhere measurable random
element `D` of a Polish Borel space, the laws of `(D, P̃^{ε_n})` on `Data × C(ℂ, 𝒫(ContinuousPath ℂ))` form a
tight set.  The two scaling-type inputs of `isTightMeasureSet_data_interpWalkLaw` are the conclusions of
`hEqLaw_of_scaling` and `hEqPath_of_scaling`. -/
theorem isTightMeasureSet_data_interpWalkLaw_of_scaling {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
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
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h636 : ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun s ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2)),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X ≤
              succExit (fun w => interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) (2 * s)))
                ⌊(2 * s) ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ (2 * s))}))
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
  isTightMeasureSet_data_interpWalkLaw hS hη' hae hε0 hε
    (hEqLaw_of_scaling h32 h213 h214 h217 h219 hEnvS h632 hγ hγ2 h636 hbd hS hae hε0 hε)
    (hEqPath_of_scaling h213 h214 h217 hEnvS h632 hγ hγ2 h636 hS hae hε0 hε) D hD

end MatedCRT.FirstPass.Derived
