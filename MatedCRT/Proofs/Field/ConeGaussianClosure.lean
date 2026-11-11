import Mathlib
import LatticeProb.Gauss.GaussianClosure

/-!
# Centred Gaussian spaces are closed under almost sure limits

A family of real random variables is a *centred Gaussian space* if every element is measurable and centred
Gaussian. Within a linear space of random variables this makes every finite family jointly Gaussian
(`isGaussianProcess_of_isCentredGaussianSpace`). The closure property used for the lateral part of the whole-plane
GFF (whose observables are almost sure limits of Riemann sums of circle averages):

* `exists_map_eq_gaussianReal_of_tendsto_ae`: an almost sure limit of centred Gaussians is a centred Gaussian. No
  hypothesis on the variances is needed: the characteristic functions `exp(-σ_n t²/2)` converge, and a limit `0` at
  `t = 1` would make the characteristic function of the limit vanish on `{1/(m+1)}`, against its continuity at `0`.
  The case of convergent variances is `map_eq_gaussianReal_of_tendsto_variance` (a citation of
  `LatticeProb.map_eq_gaussianReal_of_tendsto_ae`, LatticeProb/Gauss/Limit.lean).
* `isCentredGaussianSpace_sup_span`, `isCentredGaussianSpace_sup_span_finset`: adjoining almost sure limits of
  elements of a centred Gaussian linear space keeps it a centred Gaussian linear space.

The definitions and the proofs of this file are those of `LatticeProb.GaussianClosure`
(LatticeProb/Gauss/GaussianClosure.lean); the statements here are unchanged.
-/

namespace MatedCRT.Field.GaussClosure

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The characteristic function `t ↦ E[e^{itZ}]` of a real random variable. -/
noncomputable def cf (P : Measure Ω) (Z : Ω → ℝ) (t : ℝ) : ℂ :=
  ∫ ω, Complex.exp ((t : ℂ) * (Z ω : ℂ) * Complex.I) ∂P

/-- The characteristic function is the library one, `LatticeProb.GaussianClosure.cf`. -/
theorem cf_eq_lp (P : Measure Ω) (Z : Ω → ℝ) (t : ℝ) :
    cf P Z t = LatticeProb.GaussianClosure.cf P Z t := rfl

lemma norm_exp_mul_I (t u : ℝ) : ‖Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I)‖ = 1 :=
  LatticeProb.GaussianClosure.norm_exp_mul_I t u

lemma tendsto_cf_of_tendsto_ae [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hXm : ∀ n, Measurable (X n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) (t : ℝ) :
    Tendsto (fun n => cf P (X n) t) atTop (𝓝 (cf P Y t)) :=
  LatticeProb.GaussianClosure.tendsto_cf_of_tendsto_ae hXm hae t

lemma tendsto_cf_param [IsFiniteMeasure P] {Y : Ω → ℝ} (hYm : Measurable Y) {τ : ℕ → ℝ} {t : ℝ}
    (hτ : Tendsto τ atTop (𝓝 t)) : Tendsto (fun m => cf P Y (τ m)) atTop (𝓝 (cf P Y t)) :=
  LatticeProb.GaussianClosure.tendsto_cf_param hYm hτ

lemma cf_zero [IsProbabilityMeasure P] (Y : Ω → ℝ) : cf P Y 0 = 1 :=
  LatticeProb.GaussianClosure.cf_zero Y

lemma cf_eq_of_map_eq {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ≥0} (h : P.map Z = gaussianReal 0 v) (t : ℝ) :
    cf P Z t = ((Real.exp (-(v : ℝ) * t ^ 2 / 2) : ℝ) : ℂ) :=
  LatticeProb.GaussianClosure.cf_eq_of_map_eq hZ h t

/-- An almost sure limit of centred Gaussians with convergent variances is a centred Gaussian (as
`LatticeProb.map_eq_gaussianReal_of_tendsto_ae`). -/
theorem map_eq_gaussianReal_of_tendsto_variance [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {σ : ℕ → ℝ≥0} {s : ℝ≥0} (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y)
    (hX : ∀ n, P.map (X n) = gaussianReal 0 (σ n)) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hσ : Tendsto (fun n => ((σ n : ℝ≥0) : ℝ)) atTop (𝓝 ((s : ℝ≥0) : ℝ))) :
    P.map Y = gaussianReal 0 s :=
  LatticeProb.map_eq_gaussianReal_of_tendsto_ae hXm hYm hX hae hσ

/-- **An almost sure limit of centred Gaussians is a centred Gaussian.** -/
theorem exists_map_eq_gaussianReal_of_tendsto_ae [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y) (hX : ∀ n, ∃ v : ℝ≥0, P.map (X n) = gaussianReal 0 v)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    ∃ v : ℝ≥0, P.map Y = gaussianReal 0 v :=
  LatticeProb.GaussianClosure.exists_map_eq_gaussianReal_of_tendsto_ae hXm hYm hX hae

/-! ## Centred Gaussian spaces -/

/-- Every element of `M` is a measurable centred Gaussian random variable. -/
def IsCentredGaussianSpace (P : Measure Ω) (M : Set (Ω → ℝ)) : Prop :=
  ∀ Y ∈ M, Measurable Y ∧ ∃ v : ℝ≥0, P.map Y = gaussianReal 0 v

/-- `Z` is the almost sure limit of a sequence of elements of `M`. -/
def IsAeLimitOf (P : Measure Ω) (M : Set (Ω → ℝ)) (Z : Ω → ℝ) : Prop :=
  ∃ Y : ℕ → Ω → ℝ, (∀ n, Y n ∈ M) ∧ ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))

theorem isCentredGaussianSpace_eq_lp (P : Measure Ω) (M : Set (Ω → ℝ)) :
    IsCentredGaussianSpace P M = LatticeProb.GaussianClosure.IsCentredGaussianSpace P M := rfl

theorem isAeLimitOf_eq_lp (P : Measure Ω) (M : Set (Ω → ℝ)) (Z : Ω → ℝ) :
    IsAeLimitOf P M Z = LatticeProb.GaussianClosure.IsAeLimitOf P M Z := rfl

lemma IsAeLimitOf.mono {M M' : Set (Ω → ℝ)} (h : M ⊆ M') {Z : Ω → ℝ} (hZ : IsAeLimitOf P M Z) :
    IsAeLimitOf P M' Z :=
  LatticeProb.GaussianClosure.IsAeLimitOf.mono h hZ

lemma isAeLimitOf_of_mem {M : Set (Ω → ℝ)} {Z : Ω → ℝ} (hZ : Z ∈ M) : IsAeLimitOf P M Z :=
  LatticeProb.GaussianClosure.isAeLimitOf_of_mem hZ

/-- Adjoining an almost sure limit to a centred Gaussian linear space. -/
theorem isCentredGaussianSpace_sup_span [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : IsAeLimitOf P M Z) :
    IsCentredGaussianSpace P (M ⊔ Submodule.span ℝ {Z} : Submodule ℝ (Ω → ℝ)) :=
  LatticeProb.GaussianClosure.isCentredGaussianSpace_sup_span hM hZm hZ

/-- Adjoining finitely many almost sure limits to a centred Gaussian linear space. -/
theorem isCentredGaussianSpace_sup_span_finset [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) (T : Finset (Ω → ℝ)) (hTm : ∀ Z ∈ T, Measurable Z)
    (hT : ∀ Z ∈ T, IsAeLimitOf P M Z) :
    IsCentredGaussianSpace P (M ⊔ Submodule.span ℝ (T : Set (Ω → ℝ)) : Submodule ℝ (Ω → ℝ)) :=
  LatticeProb.GaussianClosure.isCentredGaussianSpace_sup_span_finset hM T hTm hT

/-- Adjoining a countable family of almost sure limits to a centred Gaussian linear space. -/
theorem isCentredGaussianSpace_sup_span_range [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {ι : Type*} (Z : ι → Ω → ℝ) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, IsAeLimitOf P M (Z i)) :
    IsCentredGaussianSpace P (M ⊔ Submodule.span ℝ (Set.range Z) : Submodule ℝ (Ω → ℝ)) :=
  LatticeProb.GaussianClosure.isCentredGaussianSpace_sup_span_range hM Z hZm hZ

/-- **Joint Gaussianity.** A family of elements of a centred Gaussian linear space is a Gaussian process. -/
theorem isGaussianProcess_of_isCentredGaussianSpace [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {T : Type*} {W : T → Ω → ℝ} (hW : ∀ t, W t ∈ M) :
    IsGaussianProcess W P :=
  LatticeProb.GaussianClosure.isGaussianProcess_of_isCentredGaussianSpace hM hW

end MatedCRT.Field.GaussClosure
