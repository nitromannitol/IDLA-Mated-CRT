import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Proposed.DuplantierMillerSheffieldCone2014

/-!
# Distributional cone scaling through the canonical law

The canonical identification in env-steps.tex:210–296 remains a separate
obligation.  Given the joint law of the distribution and its embedding radius,
the DMS scaling law transfers to the environment's representative.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
open HarmonicBalls

namespace MatedCRT.Sec1

/-- The canonical joint distribution and embedding-radius identification.
This is the remaining internal identification from env-steps.tex:210–296,
not a literature input or the conclusion of the scaling theorem. -/
def CanonicalConeDistributionRadiusLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ b : ℝ, 0 < b →
    ∀ (H : Ω → LQGMetric.DistC) (R : Ω → ℝ), Measurable H → Measurable R →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      (∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (X : Ω' → LQGMetric.DistC) (B B' : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' ∧
        LQGMetric.IsWholePlaneGFF X P' ∧ IsBrownianReal B P' ∧ IsBrownianReal B' P' ∧
        IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P' ∧
        IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P' ∧
        Measurable (fun ω =>
          (MatedCRTHarmonic.MatedCRT.coneField (X ω)
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)),
           Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
            (fun t => B t ω) (fun t => B' t ω))) ∧
        S.P.map (fun ω => (H ω, R ω)) = P'.map (fun ω =>
          (MatedCRTHarmonic.MatedCRT.coneField (X ω)
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)),
           Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
            (fun t => B t ω) (fun t => B' t ω)))

/-- DMS scaling transfers through the joint field–radius law; the latter is
still to be proved from the canonical cone identification. -/
theorem rescaledConeDistributionLawStep_of_canonical
    (𝒮 : SpaceFillingSLEModel) (hdms : Proposed.DMS14ConeScaling)
    (hcanonical : CanonicalConeDistributionRadiusLawStep 𝒮) :
    RescaledConeDistributionLawStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb H R hHm hRm hrep hR
  obtain ⟨Ω', mΩ', P', X, B, B', hprob, hX, hB, hB', hind, hindB, hmeas, hjoint⟩ :=
    hcanonical γ hγ hγ2 Ω S hS b hb H R hHm hRm hrep hR
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hprob
  let H' : Ω' → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  let R' : Ω' → ℝ := fun ω => Proposed.dmsConeEmbeddingRadius γ γ (-Real.log b)
    (fun t => B t ω) (fun t => B' t ω)
  have hq : γ < MatedCRTHarmonic.MatedCRT.lqgQ γ := by
    unfold MatedCRTHarmonic.MatedCRT.lqgQ
    have hsq : γ * γ < 4 := by nlinarith
    have hhalf : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hγ]
      nlinarith
    linarith
  have hscale := hdms γ γ hγ hγ2 hq Ω' P' X B B' hX hB hB' hind hindB (-Real.log b)
  have hscale' : P'.map (fun ω => rescaledDistribution γ b (H' ω) (R' ω)) = P'.map H' := by
    convert hscale using 1
    congr 1
    funext ω
    simp only [rescaledDistribution, H', R', HarmonicBalls.lqgQ,
      MatedCRTHarmonic.MatedCRT.lqgQ, div_eq_mul_inv]
    congr 1
    ring
  have hpair : Measurable (fun ω => (H ω, R ω)) := hHm.prodMk hRm
  calc
    S.P.map (fun ω => rescaledDistribution γ b (H ω) (R ω)) =
        (S.P.map (fun ω => (H ω, R ω))).map
          (fun p => rescaledDistribution γ b p.1 p.2) :=
      (Measure.map_map (measurable_rescaledDistribution γ b) hpair).symm
    _ = (P'.map (fun ω => (H' ω, R' ω))).map
          (fun p => rescaledDistribution γ b p.1 p.2) := by rw [hjoint]
    _ = P'.map (fun ω => rescaledDistribution γ b (H' ω) (R' ω)) :=
      Measure.map_map (measurable_rescaledDistribution γ b) hmeas
    _ = P'.map H' := hscale'
    _ = (P'.map (fun ω => (H' ω, R' ω))).map Prod.fst :=
      (Measure.map_map measurable_fst hmeas).symm
    _ = (S.P.map (fun ω => (H ω, R ω))).map Prod.fst := by rw [hjoint]
    _ = S.P.map H := Measure.map_map measurable_fst hpair

/-- Conditional field assembly.  The canonical joint law and the fixed-grid
circle identities remain independent proof obligations. -/
theorem rescaledConeFieldStep_of_canonical_and_grid
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hdms : Proposed.DMS14ConeScaling)
    (hcanonical : CanonicalConeDistributionRadiusLawStep 𝒮)
    (hgrid : RescaledConeDistributionCircleGridStep 𝒮) :
    RescaledConeFieldStep 𝒮 := by
  apply rescaledConeFieldStep_of_observable_law 𝒮 hscale
  apply rescaledConeObservableLawStep_of_represented_law 𝒮
  apply rescaledConeRepresentedLawStep_of_distribution 𝒮 hscale
  · exact rescaledConeDistributionCircleStep_of_grid 𝒮 hscale hgrid
  · exact rescaledConeDistributionLawStep_of_canonical 𝒮 hdms hcanonical

end MatedCRT.Sec1
