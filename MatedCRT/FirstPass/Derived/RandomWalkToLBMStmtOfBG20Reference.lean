import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20
import MatedCRT.FirstPass.Derived.IdentificationTransfer
import MatedCRT.FirstPass.Derived.InterpWalkLawJointConvergence

/-!
# Theorem 2.11 from Berestycki–Gwynne Theorem 1.2 on one reference environment

Berestycki–Gwynne (2020), Theorem 1.2, is proved for one realization of the mated-CRT map: the one built from a
whole-plane space-filling SLE`_{κ'}` `η` and an independent `γ`-quantum cone `h`. The binder `hBG` of
`randomWalkToLBMStmt_of_bg20` asks for its conclusion in every valid environment on `ℝ` of the model `𝒮`. Here
it is asked on ONE valid environment `S₀`, on any carrier, of any model `𝒮₀` whose normalized space-filling SLE
law is the same `ν` (`hBGref`): the selected-cell walk laws converge to the Liouville Brownian law field
`lbmPathLawField γ (pairJ ⊤ H₀)` uniformly on compact sets, in probability.

The conclusion is first turned into the convergence in law of the pairs `(pairJ ⊤ h, P̃^ε)` to
`(pairJ ⊤ h, lbmPathLawField γ (pairJ ⊤ h))` on the reference (`tendsto_integral_interpWalkLaw_of_selCellLaw`),
which is a statement about bounded test functions and hence about the law of (field, curve, edge multiplicities)
only. That law is the same in every valid environment with the same `ν`
(`tendsto_integral_interpWalkLaw_of_reference`, through the rigidity pair `exists_matingRigidLEOn_full_derived`),
so the convergence holds in every valid environment of `𝒮`, which is the hypothesis `hP1` of
`randomWalkToLBMStmt_of_reference_convergence`. The probability of the event `{∃ z ∈ K, …}` itself is never
transferred: that event need not be measurable.

* `randomWalkToLBMStmt_of_bg20_reference`: `RandomWalkToLBMStmt 𝒮` from `h1 h2 hN4 h10 hBGref`.
* `closed_1_4_quantumConeScaling_coneDimension_bg20ref`, `closed_1_6_quantumConeScaling_coneDimension_bg20ref`:
  Theorems 1.4 and 1.6 in the counted forms `closed_1_4_quantumConeScaling_coneDimension` and
  `closed_1_6_quantumConeScaling_coneDimension`, with `h11` supplied from `hBGref`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRT

/-- **Random walk to Liouville Brownian motion from Berestycki–Gwynne Theorem 1.2 on one reference
environment.** For each `0 < γ < 2`, `hBGref` provides one valid environment `S₀` (any carrier) of a model `𝒮₀`
with the same normalized space-filling SLE law `ν`, measurable versions `H₀`, `η₀` of its field and curve, and the
convergence of its selected-cell walk laws to the Liouville Brownian law field, uniformly on compact sets in
probability (Berestycki–Gwynne (2020), Theorem 1.2). -/
theorem randomWalkToLBMStmt_of_bg20_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    RandomWalkToLBMStmt 𝒮 := by
  obtain ⟨G, hGnull, hG⟩ := exists_matingRigidLEOn_full_derived
  have hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G :=
    fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩
  refine FirstPass.Derived.randomWalkToLBMStmt_of_reference_convergence
    (coneEnvironmentScalingUnderSLE_of_scaling 𝒮 FirstPass.Derived.quantumConeScalingInput_derived
      h2.1 h2.2.1 h2.2.2)
    hN4 h1 h10 hU (LQGMetric.pairJ ⊤) measurable_pairJ_top lbmPathLawField measurable_lbmPathLawField
    (hLBM_lbmPathLawField FirstPass.Derived.lbmLawContinuity_of_isValid) ?_
  intro γ hγ0 hγ2 S hS H hH hrep η' hη'm hη' f
  obtain ⟨𝒮₀, hν₀, Ω₀, _, S₀, hS₀, H₀, hH₀, hrep₀, η₀, hη₀m, hη₀, hconv⟩ := hBGref γ hγ0 hγ2
  exact FirstPass.Derived.tendsto_integral_interpWalkLaw_of_reference h1 hν₀ hU hγ0 hγ2 hS₀ hH₀ hrep₀
    hη₀m hη₀ hS hH hrep hη'm hη' measurable_pairJ_top (measurable_lbmPathLawField γ)
    (fun g => FirstPass.Derived.tendsto_integral_interpWalkLaw_of_selCellLaw (Φ := lbmPathLawField)
      hS₀ measurable_pairJ_top hH₀ hη₀m hη₀ hconv g) f

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the convergence of the
embedded random walk to Liouville Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_bg20_reference`
from Berestycki–Gwynne Theorem 1.2 on one reference environment (`hBGref`). Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_bg20ref
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension ν h1 h2 hN4 h10
    (randomWalkToLBMStmt_of_bg20_reference h1 h2 hN4 h10 hBGref)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the convergence of the
embedded random walk to Liouville Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_bg20_reference`
from Berestycki–Gwynne Theorem 1.2 on one reference environment (`hBGref`). Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_bg20ref
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension ν h1 h2 hN4 h10
    (randomWalkToLBMStmt_of_bg20_reference h1 h2 hN4 h10 hBGref)

end MatedCRT
