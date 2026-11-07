import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GaussianNormalization
import MatedCRT.Defs.LogCorrelatedField

/-! # Comparison of measurable Gaussian multiplicative chaos versions -/

namespace MatedCRT

open MeasureTheory

/-- Jointly measurable versions which agree at each spatial point give the
same variance-normalized chaos measure for almost every field realization. -/
theorem gmcApprox_ae_eq_of_pointwise_ae_eq
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] (σ : Measure E) [SFinite σ] (γ : ℝ)
    (H K : Ω → E → ℝ)
    (hH : Measurable (fun p : Ω × E => H p.1 p.2))
    (hK : Measurable (fun p : Ω × E => K p.1 p.2))
    (hHK : ∀ x, ∀ᵐ ω ∂P, H ω x = K ω x) :
    ∀ᵐ ω ∂P, gmcApprox P σ γ H ω = gmcApprox P σ γ K ω := by
  have hv : ∀ x, (∫ ω, (H ω x) ^ 2 ∂P) = ∫ ω, (K ω x) ^ 2 ∂P := by
    intro x
    apply integral_congr_ae
    filter_upwards [hHK x] with ω hω
    rw [hω]
  have hm : MeasurableSet {p : Ω × E | H p.1 p.2 = K p.1 p.2} :=
    measurableSet_eq_fun hH hK
  have hae : ∀ᵐ ω ∂P, ∀ᵐ x ∂σ, H ω x = K ω x := by
    apply (Measure.ae_ae_comm hm).2
    exact Filter.Eventually.of_forall hHK
  filter_upwards [hae] with ω hω
  apply withDensity_congr_ae
  filter_upwards [hω] with x hx
  simp only [hv x, hx]

/-- Two jointly measurable regularization versions give the same chaos
approximation on the domain at every fixed positive scale. -/
theorem gmcApprox_ae_eq_of_regularization_versions
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (k : ℕ) (D : Set (EuclideanSpace ℝ (Fin k))) (σ : Measure D) [SFinite σ]
    (h : SignedMeasure (EuclideanSpace ℝ (Fin k)) → Ω → ℝ)
    (θ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure θ]
    (γ ε : ℝ) (hε : 0 < ε)
    (H K : ℝ → Ω → EuclideanSpace ℝ (Fin k) → ℝ)
    (hH : IsLogFieldRegularizationVersion P k D h θ H)
    (hK : IsLogFieldRegularizationVersion P k D h θ K)
    (hmH : Measurable (fun p : Ω × D => H ε p.1 p.2.1))
    (hmK : Measurable (fun p : Ω × D => K ε p.1 p.2.1)) :
    ∀ᵐ ω ∂P, gmcApprox P σ γ (fun ω x => H ε ω x.1) ω =
      gmcApprox P σ γ (fun ω x => K ε ω x.1) ω := by
  apply gmcApprox_ae_eq_of_pointwise_ae_eq P σ γ _ _ hmH hmK
  intro x
  filter_upwards [hH.1 ε hε x.1 x.2, hK.1 ε hε x.1 x.2] with ω h₁ h₂
  exact h₁.trans h₂.symm

end MatedCRT
