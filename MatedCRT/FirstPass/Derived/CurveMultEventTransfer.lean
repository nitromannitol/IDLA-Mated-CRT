import MatedCRT.FirstPass.Derived.MultOfFieldCurve
import MatedCRT.FirstPass.Derived.FieldCurveJointLaw
import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma

/-!
# Events of the curve and the edge multiplicities have the same probability in every valid environment

Fix a normalized space-filling SLE law `ν`, `0 < γ < 2`, and a one-sided mating-rigid set `G` of pairs of paths that
is full for every `γ`-correlated two-sided Brownian law (`MatingRigidLEOn G`). For two valid environments `S, S'` of
models with law `ν`, on arbitrary carriers, an event that depends on the outcome only through the space-filling curve
and the edge multiplicities of the mated-CRT map has the same probability under `S` and under `S'`:

* `measure_curve_mult_mem_eq_of_valid`: for measurable continuous versions `η', ζ'` of the curves,
  `S.P {(η', S.mult ε) ∈ E} = S'.P {(ζ', S'.mult ε) ∈ E}` for every measurable `E ⊆ C(ℝ, ℂ) × (ℤ → ℤ → ℕ)`;
* `measure_eta_mult_mem_eq_of_valid`: the same for the curves `S.η, S'.η` themselves and every measurable
  `E ⊆ (ℝ → ℂ) × (ℤ → ℤ → ℕ)`.

The proof writes the edge multiplicities as one measurable function of (field, curve), `bmEdgeCount ε (BL (H, η'))`
(`exists_decoder_mult_eq`), and uses that (field, curve) has the same law in every valid environment with the given
space-filling SLE law (`identDistrib_distribution_curveVersion_of_valid`). The rigidity of the mating relation is an
explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT.FirstPass.Derived

/-- **Transfer of events of (curve, edge multiplicities) between valid environments.** Let `S, S'` be valid
environments of models with the same normalized space-filling SLE law `ν` and the same `0 < γ < 2`, `H, H'` measurable
random distributions with a.s. the pairings of their fields, and `η', ζ'` measurable continuous versions of their
curves. On a one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law, for every
`ε` and every measurable set `E` of pairs (curve, edge multiplicity),
`S.P {(η', S.mult ε) ∈ E} = S'.P {(ζ', S'.mult ε) ∈ E}`. -/
theorem measure_curve_mult_mem_eq_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω)
    (ε : ℝ) {E : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ))} (hE : MeasurableSet E) :
    S.P {ω | (η' ω, S.mult ε ω) ∈ E} = S'.P {ω | (ζ' ω, S'.mult ε ω) ∈ E} := by
  obtain ⟨BL, hBLm, hBL⟩ := exists_decoder_mult_eq (ν := ν) hγ0 hγ2 hGnull hG
  let F : LQGMetric.DistC × C(ℝ, ℂ) → C(ℝ, ℂ) × (ℤ → ℤ → ℕ) := fun x =>
    (x.2, bmEdgeCount ε (fun t => (BL x t).1) (fun t => (BL x t).2))
  have hFm : Measurable F :=
    measurable_snd.prodMk (Measurable.of_eval fun j => Measurable.of_eval fun k =>
      (measurable_bmEdgeCount_path ε j k).comp hBLm)
  have hA : {ω | (η' ω, S.mult ε ω) ∈ E} =ᵐ[S.P] (fun ω => (H ω, η' ω)) ⁻¹' (F ⁻¹' E) := by
    filter_upwards [hBL 𝒮 hν Ω S hS H hH hrep η' hη'm hη' ε] with ω hω
    change ((η' ω, S.mult ε ω) ∈ E) =
      ((η' ω, bmEdgeCount ε (fun t => (BL (H ω, η' ω) t).1) (fun t => (BL (H ω, η' ω) t).2)) ∈ E)
    rw [hω]
  have hB : {ω | (ζ' ω, S'.mult ε ω) ∈ E} =ᵐ[S'.P] (fun ω => (H' ω, ζ' ω)) ⁻¹' (F ⁻¹' E) := by
    filter_upwards [hBL 𝒮' hν' Ω' S' hS' H' hH' hrep' ζ' hζ'm hζ' ε] with ω hω
    change ((ζ' ω, S'.mult ε ω) ∈ E) =
      ((ζ' ω, bmEdgeCount ε (fun t => (BL (H' ω, ζ' ω) t).1) (fun t => (BL (H' ω, ζ' ω) t).2)) ∈ E)
    rw [hω]
  have hid := identDistrib_distribution_curveVersion_of_valid hν hν' hγ0 hγ2 hS hS' hH hH' hrep hrep' hη'm hη'
    hζ'm hζ'
  exact (measure_congr hA).trans ((hid.measure_mem_eq (hFm hE)).trans (measure_congr hB).symm)

/-- **Transfer of events of (curve, edge multiplicities) between valid environments, for the curves themselves.**
Let `S, S'` be valid environments of models with the same normalized space-filling SLE law `ν` and the same
`0 < γ < 2`. On a one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law, for
every `ε` and every measurable set `E` of pairs (curve, edge multiplicity),
`S.P {(S.η, S.mult ε) ∈ E} = S'.P {(S'.η, S'.mult ε) ∈ E}`. The measurable versions of the fields and the curves
are supplied by validity. -/
theorem measure_eta_mult_mem_eq_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (ε : ℝ) {E : Set ((ℝ → ℂ) × (ℤ → ℤ → ℕ))} (hE : MeasurableSet E) :
    S.P {ω | (S.η ω, S.mult ε ω) ∈ E} = S'.P {ω | (S'.η ω, S'.mult ε ω) ∈ E} := by
  obtain ⟨H, hHm, hrep⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS
  obtain ⟨H', hH'm, hrep'⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS'
  obtain ⟨_, _, _, _, _, _, _, _, _, η', _, hC, hae⟩ := hS.matingOfTrees
  obtain ⟨_, _, _, _, _, _, _, _, _, ζ', _, hC', hae'⟩ := hS'.matingOfTrees
  have hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := hae.mono fun ω h => h.1
  have hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω := hae'.mono fun ω h => h.1
  let c : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) → (ℝ → ℂ) × (ℤ → ℤ → ℕ) := fun p => (⇑p.1, p.2)
  have hc : Measurable c :=
    (Measurable.of_eval fun t => (continuous_eval_const t).measurable.comp measurable_fst).prodMk
      measurable_snd
  have key := measure_curve_mult_mem_eq_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG
    (hHm.mono (S.fieldSigma_le hS) le_rfl) (hH'm.mono (S'.fieldSigma_le hS') le_rfl) hrep hrep'
    hC.measurable_curves.2.1 hη' hC'.measurable_curves.2.1 hζ' ε (hc hE)
  refine (measure_congr ?_).trans (key.trans (measure_congr ?_))
  · filter_upwards [hη'] with ω hω
    change ((S.η ω, S.mult ε ω) ∈ E) = ((⇑(η' ω), S.mult ε ω) ∈ E)
    rw [hω]
  · filter_upwards [hζ'] with ω hω
    change ((⇑(ζ' ω), S'.mult ε ω) ∈ E) = ((S'.η ω, S'.mult ε ω) ∈ E)
    rw [hω]

end MatedCRT.FirstPass.Derived
