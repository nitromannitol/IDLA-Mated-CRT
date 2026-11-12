import MatedCRT.FirstPass.Derived.ConeScaleRadiusDecoder
import MatedCRT.FirstPass.Derived.RescaledCircleDecoder
import MatedCRT.FirstPass.Derived.OpenMassDecoder
import MatedCRT.FirstPass.Derived.MeasureSigmaAlgebraCountable
import MatedCRT.FirstPass.Derived.OpenMassProductGeneration
import MatedCRT.FirstPass.Derived.IndepTransfer
import MatedCRT.FirstPass.Derived.SimilarityScaling
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.JointMeasureLaw

/-!
# Similarity transfer: independence of the rescaled cone data from a variable independent of the cone data

If a random variable `ξ` is independent of the cone data `(circle average process, LQG measure)`, then it is also
independent of the rescaled cone data together with the scale radius,
`((circle average process, LQG measure) of the field rescaled at the scale radius `R_b`, `R_b)`.

The rescaled data is, almost surely, a Borel function of the circle average process: the rescaled circle average
process is the decoder of the circle average process and of `R_b` (itself a Borel function of the circle average
process), and the rescaled LQG measure is the LQG limit of the rescaled circle averages.  The sigma-algebra of the
measures on the plane is generated, relative to the locally finite measures, by the countably many masses of a
family of open sets; this transfers the independence from the coded variable to the measure-valued one.
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls

open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The rescaled cone data and the scale radius are independent of any variable independent of the cone data.** -/
theorem indepFun_rescaledCone_of_indep {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {C : Type*} [MeasurableSpace C] {ξ : Ω → C}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hlqg : ConeLQGScalingStep) {b : ℝ} (hb : 0 < b)
    (hind : IndepFun (fun ω => (circleProcess (hcirc ω), μ ω)) ξ P) :
    IndepFun (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b, coneScaleRadius γ (hcirc ω) b)) ξ P := by
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨U, hU, hgen⟩ := exists_countable_openMass_generation
  obtain ⟨F, hFm, hF⟩ := exists_measurable_openMass_decoder γ U hU
  have hs := hlqg γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hρ := ae_radiusDecoder_eq hγ0 hγ2 hcone.2.1 b
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    have h : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
    exact h.mono fun _ hω => hω.isLocallyFiniteMeasure
  let ρ : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ := radiusDecoder γ b
  let A : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) := fun y =>
    rescaledCircleDecoder γ b (y, ρ y)
  let Φ : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℕ → ℝ≥0∞) × ℝ := fun y =>
    (A y, F (A y), ρ y)
  have hρm : Measurable ρ := measurable_radiusDecoder γ b
  have hAm : Measurable A :=
    (measurable_rescaledCircleDecoder γ b).comp (measurable_id.prodMk hρm)
  have hΦm : Measurable Φ := hAm.prodMk ((hFm.comp hAm).prodMk hρm)
  let g : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ →
      (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℕ → ℝ≥0∞) × ℝ := fun p => Φ p.1
  have hgm : Measurable g := hΦm.comp measurable_fst
  let e : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × ℝ →
      (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℕ → ℝ≥0∞) × ℝ := fun q => (q.1, fun n => q.2.1 (U n), q.2.2)
  let Z : Ω → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × ℝ := fun ω =>
    (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b, coneScaleRadius γ (hcirc ω) b)
  have hae : (e ∘ Z) =ᵐ[P] g ∘ (fun ω => (circleProcess (hcirc ω), μ ω)) := by
    filter_upwards [hs, hρ, hcont] with ω hω hρω hcω
    obtain ⟨h0, hlim⟩ := hω
    have h1 : circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) =
        A (circleProcess (hcirc ω)) := by
      simp only [A, ρ, hρω]
      exact (rescaledCircleDecoder_circleProcess h0 hcω).symm
    have h2 : F (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
        fun n => FPScaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b (U n) :=
      hF _ _ (continuousOn_rescaledCircle hcω h0) hlim
    simp only [Function.comp_apply, e, Z, g, Φ]
    refine Prod.ext h1 (Prod.ext ?_ ?_)
    · simp only
      rw [← h1, h2]
    · simp only [ρ, hρω]
  have hind' : IndepFun (e ∘ Z) ξ P :=
    (hind.comp hgm measurable_id).congr hae.symm (Filter.EventuallyEq.refl _ _)
  have hL : ∀ᵐ ω ∂P, Z ω ∈ {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × ℝ |
      IsLocallyFiniteMeasure q.2.1} := by
    filter_upwards [hs, hlf] with ω hω hl
    have := hl
    exact isLocallyFiniteMeasure_fPScaledMeasure hω.1.ne' b
  exact indepFun_of_embedding_ae e _ hL (hcomap_prod_openMass U hgen) hind'

end MatedCRT.FirstPass.Derived
