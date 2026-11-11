import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GaussianNormalization
import MatedCRT.Defs.LogCorrelatedField

/-! # Comparison of measurable Gaussian multiplicative chaos versions -/

namespace MatedCRT

open MeasureTheory Filter Topology

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

/-- L¹ convergence of chaos masses transfers between jointly measurable
regularization versions, provided their scales are eventually positive. -/
theorem tendsto_gmc_mass_L1_of_regularization_versions
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (k : ℕ) (D : Set (EuclideanSpace ℝ (Fin k))) (σ : Measure D) [SFinite σ]
    (h : SignedMeasure (EuclideanSpace ℝ (Fin k)) → Ω → ℝ)
    (θ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure θ]
    (γ : ℝ) (l : Filter ι) (ε : ι → ℝ)
    (H K : ℝ → Ω → EuclideanSpace ℝ (Fin k) → ℝ)
    (hH : IsLogFieldRegularizationVersion P k D h θ H)
    (hK : IsLogFieldRegularizationVersion P k D h θ K)
    (hε : ∀ᶠ i in l, 0 < ε i)
    (hmH : ∀ᶠ i in l, Measurable (fun p : Ω × D => H (ε i) p.1 p.2.1))
    (hmK : ∀ᶠ i in l, Measurable (fun p : Ω × D => K (ε i) p.1 p.2.1))
    (S : Set D) (Y : Ω → ℝ)
    (hconv : Tendsto (fun i => ∫ ω, |(gmcApprox P σ γ
      (fun ω' x => H (ε i) ω' x.1) ω).real S - Y ω| ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, |(gmcApprox P σ γ
      (fun ω' x => K (ε i) ω' x.1) ω).real S - Y ω| ∂P) l (𝓝 0) := by
  apply hconv.congr'
  filter_upwards [hε, hmH, hmK] with i hi hmi hmk
  apply integral_congr_ae
  filter_upwards [gmcApprox_ae_eq_of_regularization_versions P k D σ h θ γ
    (ε i) hi H K hH hK hmi hmk] with ω hω
  rw [hω]

end MatedCRT
