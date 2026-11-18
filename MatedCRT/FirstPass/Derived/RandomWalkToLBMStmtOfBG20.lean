import MatedCRT.FirstPass.Derived.QuantumConeScalingDimension
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputsDerived
import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.FirstPass.Derived.MatingRigidityAssembly

/-!
# Convergence of the embedded random walk to Liouville Brownian motion from Berestycki–Gwynne Theorem 1.2

* `exists_matingRigidLEOn_full_derived`: a one-sided mating-rigid set of pairs which is full for every
  `γ`-correlated two-sided Brownian law, `0 < γ < 2`; the four almost sure inputs of
  `exists_matingRigidLEOn_full` are theorems (immediate descent at rational times, Lévy's excursion count,
  polarity of points for the symmetric Cauchy level process, and the cone-time dimension bound).
* `randomWalkToLBMStmt_of_bg20`: `RandomWalkToLBMStmt 𝒮` from the normalized SLE law, the space-filling SLE
  closure properties, the uniform-start invariance principle (Gwynne–Miller–Sheffield, Theorem 3.10), the reference
  environments, and the convergence of the cell walk to Liouville Brownian motion for a valid environment
  (Berestycki–Gwynne 2020, Theorem 1.2, `hBG`). The environment scaling step comes from
  `coneEnvironmentScalingUnderSLE_of_scaling` and the quantum cone scaling theorem.
* `closed_1_4_quantumConeScaling_coneDimension_bg20`, `closed_1_6_quantumConeScaling_coneDimension_bg20`:
  Theorems 1.4 and 1.6 in the counted forms `closed_1_4_quantumConeScaling_coneDimension` and
  `closed_1_6_quantumConeScaling_coneDimension` with `h11` supplied by `randomWalkToLBMStmt_of_bg20`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRT

/-- **A full one-sided mating-rigid set of pairs.** The rigidity set of the triple points of the mating relation
is one-sided mating-rigid and has full measure for every `γ`-correlated two-sided Brownian law, `0 < γ < 2`. -/
theorem exists_matingRigidLEOn_full_derived :
    ∃ G : Set Path2, (∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → μ Gᶜ = 0) ∧
      MatingRigidLEOn G :=
  exists_matingRigidLEOn_full
    (fun _ _ _ _ hμ i q => LatticeProb.CorrelatedBM.ae_rat_descends hμ i q)
    (fun _ _ _ _ hμ => LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord hμ)
    (LatticeProb.CorrelatedBM.hNC_of_cauchyPointPolar LatticeProb.CorrelatedBM.cauchyPointPolarInput)
    (hZ3_of_GHM ghmConeDimInput_derived)

/-- **Random walk to Liouville Brownian motion from Berestycki–Gwynne Theorem 1.2.** The binders of
`randomWalkToLBMStmt_of_cone_inputs_derived` except the environment scaling step `hEnvS`
(`coneEnvironmentScalingUnderSLE_of_scaling` with the quantum cone scaling theorem and the space-filling SLE
closure properties `h2`) and the rigidity pair `hU` (`exists_matingRigidLEOn_full_derived`). -/
theorem randomWalkToLBMStmt_of_bg20 {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    RandomWalkToLBMStmt 𝒮 := by
  obtain ⟨G, hGnull, hG⟩ := exists_matingRigidLEOn_full_derived
  exact randomWalkToLBMStmt_of_cone_inputs_derived
    (coneEnvironmentScalingUnderSLE_of_scaling 𝒮 FirstPass.Derived.quantumConeScalingInput_derived
      h2.1 h2.2.1 h2.2.2)
    hN4 h1 h10 (fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩) hBG

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the convergence of the
embedded random walk to Liouville Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_bg20` from
Berestycki–Gwynne Theorem 1.2 (`hBG`). Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_bg20
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension ν h1 h2 hN4 h10 (randomWalkToLBMStmt_of_bg20 h1 h2 hN4 h10 hBG)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the convergence of the
embedded random walk to Liouville Brownian motion (`h11`) supplied by `randomWalkToLBMStmt_of_bg20` from
Berestycki–Gwynne Theorem 1.2 (`hBG`). Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_bg20
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension ν h1 h2 hN4 h10 (randomWalkToLBMStmt_of_bg20 h1 h2 hN4 h10 hBG)

end MatedCRT
