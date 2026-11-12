import MatedCRT.FirstPass.Derived.ConeCurveIndep

/-! # The field, its circle averages and its LQG measure are jointly independent of the curve

Under the mating-of-trees coupling of a valid environment, the triple (circle-average process, `γ`-LQG measure,
distribution) is independent of the Lebesgue-parametrized whole-plane space-filling SLE `ηL`, for every measurable
version `H` of the field (a random distribution whose pairings with test functions are almost surely those of `h`).
This extends `indepFun_circleProcess_lqgMeasure_igCurve_of_coupling` by the distribution itself: the cone field has a
version independent of `ηL` (`exists_coneField_version_indepFun_igCurve`), the circle averages are a Borel function of
that version (`MatedCRT.Sec1.distributionCircleCode`), the masses of countably many open sets are a Borel function of
the circle averages (`exists_measurable_openMass_decoder`), and these masses generate the σ-algebra on locally finite
measures (`hcomap_prod_openMass`). -/

open HarmonicBalls

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- **The field, its circle averages and its LQG measure are independent of the curve.** For a valid environment `S`
(`0 < γ < 2`), a mating-of-trees coupling on its carrier whose cone field represents the pairings of `S`, and a
random distribution `H` whose pairings are a.s. those of `S`, the triple `((r, z) ↦ h_r(z), μ_h, H)` is independent
of the space-filling curve `ηL`. -/
theorem indepFun_circleProcess_lqgMeasure_distribution_igCurve_of_coupling {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ)
    {H : Ω → LQGMetric.DistC} (hHrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    IndepFun (fun ω => (circleProcess (S.hcirc ω), S.μ ω, H ω)) ηL S.P := by
  have hcone := hS.isConeField
  obtain ⟨Hc, -, hind, hHc⟩ := exists_coneField_version_indepFun_igCurve h hγ hγ2
  have hpair : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = Hc ω φ := by
    filter_upwards [hrep, hHc] with ω h1 h2 φ
    rw [h1 φ, h2]
  have hHH : ∀ᵐ ω ∂S.P, H ω = Hc ω := by
    filter_upwards [hpair, hHrep] with ω h1 h2
    ext φ
    rw [← h1 φ, h2 φ]
  have hcirc := MatedCRT.Sec1.ae_distributionCircleVersion_eq hS hpair
  obtain ⟨V, hV, hgen⟩ := exists_countable_openMass_generation
  obtain ⟨F, hFm, hF⟩ := exists_measurable_openMass_decoder γ V hV
  have hlim : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hcone.2.2
  have hcont := hcone.2.1.ae_continuousOn_circle
  let e : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × LQGMetric.DistC →
      (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℕ → ℝ≥0∞) × LQGMetric.DistC := fun q =>
    (q.1, fun n => q.2.1 (V n), q.2.2)
  let Z : Ω → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × LQGMetric.DistC := fun ω =>
    (circleProcess (S.hcirc ω), S.μ ω, H ω)
  let g : LQGMetric.DistC → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℕ → ℝ≥0∞) × LQGMetric.DistC := fun k =>
    (MatedCRT.Sec1.distributionCircleCode k, F (MatedCRT.Sec1.distributionCircleCode k), k)
  have hgm : Measurable g := MatedCRT.Sec1.measurable_distributionCircleCode.prodMk
    ((hFm.comp MatedCRT.Sec1.measurable_distributionCircleCode).prodMk measurable_id)
  have hcp : ∀ᵐ ω ∂S.P, MatedCRT.Sec1.distributionCircleCode (Hc ω) = circleProcess (S.hcirc ω) := by
    filter_upwards [hcirc] with ω hω
    funext p
    exact hω p.1 p.1.2 p.2
  have hae : (e ∘ Z) =ᵐ[S.P] g ∘ Hc := by
    filter_upwards [hlim, hcont, hcp, hHH] with ω hl hc hp hh
    simp only [Function.comp_apply, e, Z, g]
    rw [hp, hF _ _ hc hl, hh]
  have hind' : IndepFun (e ∘ Z) ηL S.P :=
    (hind.comp hgm measurable_id).congr hae.symm (ae_eq_refl _)
  have hL : ∀ᵐ ω ∂S.P, Z ω ∈ {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × LQGMetric.DistC |
      IsLocallyFiniteMeasure q.2.1} := by
    filter_upwards [hlim] with ω hl
    exact hl.isLocallyFiniteMeasure
  exact indepFun_of_embedding_ae e _ hL (hcomap_prod_openMass V hgen) hind'

end MatedCRT.FirstPass.Derived
