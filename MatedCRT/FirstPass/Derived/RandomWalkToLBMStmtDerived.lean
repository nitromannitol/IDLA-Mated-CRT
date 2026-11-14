import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Derived.RandomWalkToLBMAssembly
import MatedCRT.FirstPass.Derived.ScalingOfUniformStartHolder
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.WalkFunctionalCompare
import LatticeProb.Prob.SubsequentialWeakLimit

/-!
# Theorem 2.11 (Berestycki-Gwynne Theorem 1.2) from the identification of subsequential limits

`RandomWalkToLBMStmt 𝒮` is derived from

* the scaling theorems of Berestycki-Gwynne Section 6 (tightness of the pairs (datum, interpolated
  quenched walk law); binders `hEnvS`, `hN4` and the SLE-law binders of `ScalingOfUniformStartHolder`),
* the sequential Prokhorov theorem (Lattice-Probability, `exists_subseq_tendsto_integral_of_isTightMeasureSet`)
  and the comparison of integrals of bounded Lipschitz path functionals in the Lévy-Prokhorov distance
  (`WalkFunctionalCompare`), and
* one named identification hypothesis `hid` (Berestycki-Gwynne Sections 7.1-7.4: Lemmas 7.4, 7.6, Proposition
  7.10, Lemmas 7.17, 7.18): there are Polish data `D` of the environment and a measurable law field `Λ` of
  the data such that every subsequential weak limit of the pairs (data, interpolated quenched walk law) is
  the law of `(D, Λ D)`, and `Λ (D ω) z` integrates every bounded Lipschitz path functional as the law of
  the rescaled LBM from `z`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls

/-- **Theorem 2.11 from the identification of subsequential limits.** -/
theorem randomWalkToLBMStmt_of_identification {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hid : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∃ (Data : Type) (_ : TopologicalSpace Data) (_ : MeasurableSpace Data) (_ : PolishSpace Data)
        (_ : BorelSpace Data) (D : Ω → Data) (Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))),
        Measurable D ∧ Measurable Λ ∧
        (∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
          ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
            ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) z : Measure (ContinuousPath ℂ))) ∧
        ∀ (e : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) → StrictMono φ →
          ∀ ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))), IsProbabilityMeasure ν →
          (∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
            Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
              (𝓝 (∫ p, f p ∂ν))) →
          ν = S.P.map fun ω => (D ω, Λ (D ω))) :
    RandomWalkToLBMStmt 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS K _ z _ F hF
  obtain ⟨η', hη', hae⟩ := hS.exists_curveVersion
  obtain ⟨Data, _, _, _, _, D, Λ, hD, hΛ, hY, hlim⟩ := hid γ hγ hγ2 Ω S hS η' hη' hae
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hident : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
          Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
            (𝓝 (∫ ω, f (D ω, Λ (D ω)) ∂S.P)) := by
    intro e he0 he
    have hmeas : ∀ n, AEMeasurable (fun ω => (D ω, interpWalkLaw S η' (e n) ω)) S.P := fun n =>
      hD.aemeasurable.prodMk (aemeasurable_interpWalkLaw hS hη' hae (he0 n))
    have hprob : ∀ n, IsProbabilityMeasure (S.P.map fun ω => (D ω, interpWalkLaw S η' (e n) ω)) :=
      fun n => (Measure.isProbabilityMeasure_map_iff (hmeas n)).2 inferInstance
    have htight := isTightMeasureSet_data_interpWalkLaw_of_uniformStart_holder hEnvS hN4 hγ hγ2 hν
      href hU hS hη' hae he0 he D hD.aemeasurable
    obtain ⟨φ, hφ, ν', hν', hconv⟩ := exists_subseq_tendsto_integral_of_isTightMeasureSet
      (fun n => S.P.map fun ω => (D ω, interpWalkLaw S η' (e n) ω))
      (by
        convert htight using 1
        ext p
        simp only [Set.mem_range, Set.mem_ofPred_eq]
        exact exists_congr fun n => eq_comm)
    have hconv' : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
        Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν')) := fun f =>
      (hconv f).congr fun k => integral_map (hmeas _) f.continuous.aestronglyMeasurable
    have hν'eq := hlim e φ he0 he hφ ν' hν' hconv'
    have hg : Measurable fun ω => (D ω, Λ (D ω)) := hD.prodMk (hΛ.comp hD)
    refine ⟨φ, hφ, fun f => ?_⟩
    have h1 := hconv' f
    rw [hν'eq, integral_map hg.aemeasurable f.continuous.aestronglyMeasurable] at h1
    exact h1
  exact tendstoInProbability_walkIntegral_of_identification hS hη' hae
    (fun e he0 he => hEqLaw_of_uniformStart_holder hEnvS hN4 hγ hγ2 hν href hU hS hae he0 he) hF
    (fun η hη => abs_integral_sub_integral_le_of_pathLevyProkhorovEDist_lt hF hη) z hD hΛ (hY z F hF) hident

end MatedCRT.FirstPass.Derived
