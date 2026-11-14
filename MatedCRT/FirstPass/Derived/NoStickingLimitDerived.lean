import MatedCRT.FirstPass.Derived.NoStickingLimit
import MatedCRT.FirstPass.Derived.NoStickingEvent
import MatedCRT.FirstPass.Derived.MepsSpeedLower

/-!
# No sticking for a subsequential limit: the packaged statement

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Proposition 6.1, last claim.  `NoStickingLimit.ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law`
takes the window estimate at radius `1/2` and the lower bound of the speed `ε m_ε` as hypotheses; here both are
supplied from the named inputs of the proof:

* the window estimate by `NoStickingEvent.limLimSmall_noSticking` at `ρ = 1/2`, from the explicit exit-time bound
  `h219` (Lemma 2.19) and the event form `h610` of the estimate (6.50) of Lemma 6.10;
* the speed bound by `MepsSpeedLower.exists_le_mul_mε_of_uniformStart`, from `h216`, `h218` (Lemmas 2.16, 2.18) and the
  uniform-start invariance principle `hN4` (Gamsa-Sheffield-Gwynne, Theorem 3.10).

The cone scaling of valid environments is `hEnvS`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace NoStickingLimitDerived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived MatedCRT.NoStickingAllRadii MatedCRT.SuccessiveExitGaps

/-- **No sticking for a subsequential limit of the quenched walk laws**, with the window estimate and the speed
bound supplied from the proof inputs `h216`, `h218`, `h219`, `hN4`, `h610`. -/
theorem ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h610 : ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2)),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X ≤
              succExit (fun w => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) δ))
                ⌊δ ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ δ)}))
    {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν))) :
    ∀ᵐ p ∂ν, ∀ z : ℂ,
      ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        {f : C(ℝ≥0, ℂ) | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0 := by
  obtain ⟨q, hq, ψ, hψ, hLL⟩ := NoStickingEvent.limLimSmall_noSticking h219 hγ hγ2 (ρ := 1 / 2)
    (by norm_num) (by norm_num) h610
  exact NoStickingLimit.ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law hEnvS hγ hγ2 hS hη' hae
    hε0 hε hD hlaw hq hψ hLL
    (MepsSpeedLower.exists_le_mul_mε_of_uniformStart h216 h218 hN4 hγ hγ2 S hS)

end NoStickingLimitDerived
end MatedCRT
