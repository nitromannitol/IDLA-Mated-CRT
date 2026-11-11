import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.FirstPass.LPBridge.LateralGaussian
import MatedCRT.LPStaging.Gauss.GaussianProcessLawExt

/-!
# Lateral part of a whole-plane GFF: finite-dimensional law

The lateral pairings `hC φ - ∫ φ(x) h_{|x|}(0) dx` of a whole-plane GFF (Definition 2.1 of the paper, the lateral
part `h - h_{|·|}(0)` of the circle average embedding) are, almost surely, the differences
`hC φ - hC (avgRot φ)` of two pairings (rotational average `avgRot φ` of `φ`). Their means vanish and their
covariances are read off from the covariance kernel `wholePlaneGFFCov` of the field. Hence the finite-dimensional
laws of the lateral pairings are the same for any two whole-plane GFFs (Gaussian laws are determined by means and
covariances).
-/

noncomputable section

namespace MatedCRT.ConeMeanZeroRestriction

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open MatedCRT.RotationalAverage MatedCRT.WholePlaneGFFLateral

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A test function supported in the unit ball is a test function on `ℂ`. -/
lemma isTestFunction_univ_of_ball {φ : ℂ → ℝ} (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) :
    IsTestFunction Set.univ φ :=
  ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩

/-- The lateral pairing agrees almost surely with the difference of the pairing and the pairing of its rotational
average (the radial integrals of `φ` and of `avgRot φ` agree almost surely, and the pairing of a rotation invariant
test function is its radial integral). -/
lemma lateralPair_ae_eq_sub_avgRot {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) :
    ∀ᵐ ω ∂P, lateralPair (hC ω) (hcirc ω) φ = hC ω φ - hC ω (avgRot φ) := by
  obtain ⟨F, hF, hFae⟩ := exists_ae_circle_version h
  filter_upwards [ae_radialIntegral_eq_avgRot h hφ,
    pairing_eq_radialIntegral_ae h hF hFae (isTestFunction_avgRot_ball hφ)
      (fun θ x => avgRot_rot φ θ x),
    ae_radialIntegral_eq hFae (avgRot φ)] with ω h1 h2 h3
  unfold lateralPair
  rw [h1, h3, ← h2]

/-- Pairings of a whole-plane GFF with test functions on `ℂ` are square integrable. -/
lemma memLp_two_pairing {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction Set.univ ψ) :
    MemLp (fun ω => hC ω ψ) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨GFFObservable.pairing ψ, hψ⟩).memLp_two

/-- The lateral pairings of a whole-plane GFF are centred. -/
lemma integral_lateralPair_eq_zero {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) :
    ∫ ω, lateralPair (hC ω) (hcirc ω) φ ∂P = 0 := by
  have hU : IsTestFunction Set.univ φ := isTestFunction_univ_of_ball hφ
  have hA : IsTestFunction Set.univ (avgRot φ) :=
    isTestFunction_univ_of_ball (isTestFunction_avgRot_ball hφ)
  have e1 : ∫ ω, hC ω φ ∂P = 0 := h.integral_eq_zero (GFFObservable.pairing φ) hU
  have e2 : ∫ ω, hC ω (avgRot φ) ∂P = 0 := h.integral_eq_zero (GFFObservable.pairing (avgRot φ)) hA
  rw [integral_congr_ae (lateralPair_ae_eq_sub_avgRot h hφ),
    integral_sub ((memLp_two_pairing h hU).integrable one_le_two)
      ((memLp_two_pairing h hA).integrable one_le_two), e1, e2, sub_zero]

/-- Covariances may be computed almost surely. -/
lemma covariance_congr_ae {μ : Measure Ω} {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    covariance X Y μ = covariance X' Y' μ := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- The covariance of two lateral pairings is the combination of covariance kernel values of the field:
`cov[L φ, L χ] = K(φ, χ) - K(φ, χ̄) - K(φ̄, χ) + K(φ̄, χ̄)` with `K = wholePlaneGFFCov` and `φ̄ = avgRot φ`. -/
lemma covariance_lateralPair_eq {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {φ χ : ℂ → ℝ}
    (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) (hχ : IsTestFunction (Metric.ball (0 : ℂ) 1) χ) :
    covariance (fun ω => lateralPair (hC ω) (hcirc ω) φ) (fun ω => lateralPair (hC ω) (hcirc ω) χ) P =
      wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing χ)
        - wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing (avgRot χ))
        - wholePlaneGFFCov (GFFObservable.pairing (avgRot φ)) (GFFObservable.pairing χ)
        + wholePlaneGFFCov (GFFObservable.pairing (avgRot φ)) (GFFObservable.pairing (avgRot χ)) := by
  have hU : IsTestFunction Set.univ φ := isTestFunction_univ_of_ball hφ
  have hV : IsTestFunction Set.univ χ := isTestFunction_univ_of_ball hχ
  have hA : IsTestFunction Set.univ (avgRot φ) :=
    isTestFunction_univ_of_ball (isTestFunction_avgRot_ball hφ)
  have hB : IsTestFunction Set.univ (avgRot χ) :=
    isTestFunction_univ_of_ball (isTestFunction_avgRot_ball hχ)
  rw [covariance_congr_ae (lateralPair_ae_eq_sub_avgRot h hφ) (lateralPair_ae_eq_sub_avgRot h hχ),
    covariance_fun_sub_fun_sub (memLp_two_pairing h hU) (memLp_two_pairing h hA)
      (memLp_two_pairing h hV) (memLp_two_pairing h hB)]
  have c11 : covariance (fun ω => hC ω φ) (fun ω => hC ω χ) P =
      wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing χ) :=
    h.covariance_eq (GFFObservable.pairing φ) (GFFObservable.pairing χ) hU hV
  have c12 : covariance (fun ω => hC ω φ) (fun ω => hC ω (avgRot χ)) P =
      wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing (avgRot χ)) :=
    h.covariance_eq (GFFObservable.pairing φ) (GFFObservable.pairing (avgRot χ)) hU hB
  have c21 : covariance (fun ω => hC ω (avgRot φ)) (fun ω => hC ω χ) P =
      wholePlaneGFFCov (GFFObservable.pairing (avgRot φ)) (GFFObservable.pairing χ) :=
    h.covariance_eq (GFFObservable.pairing (avgRot φ)) (GFFObservable.pairing χ) hA hV
  have c22 : covariance (fun ω => hC ω (avgRot φ)) (fun ω => hC ω (avgRot χ)) P =
      wholePlaneGFFCov (GFFObservable.pairing (avgRot φ)) (GFFObservable.pairing (avgRot χ)) :=
    h.covariance_eq (GFFObservable.pairing (avgRot φ)) (GFFObservable.pairing (avgRot χ)) hA hB
  rw [c11, c12, c21, c22]

/-- **Lateral law (finite-dimensional marginals).** The finite-dimensional laws of the lateral pairings of two
whole-plane GFFs agree: both are Gaussian with mean zero and covariances given by `wholePlaneGFFCov`
(`covariance_lateralPair_eq`), and Gaussian laws are determined by their means and covariances
(`LatticeProb.map_eq_of_mean_cov_fin`). -/
theorem lateralLawFinite_holds : LateralLawFinite := by
  intro Ω₁ Ω₂ _ _ P₁ P₂ hC₁ hcirc₁ hC₂ hcirc₂ hP₁ hP₂ h₁ h₂ S
  classical
  have hX := isGaussianProcess_lateral h₁
  have hY := isGaussianProcess_lateral h₂
  exact LatticeProb.map_eq_of_mean_cov_fin
    (X := fun (i : S) (ω : Ω₁) => lateralPair (hC₁ ω) (hcirc₁ ω) i.1.1)
    (Y := fun (i : S) (ω : Ω₂) => lateralPair (hC₂ ω) (hcirc₂ ω) i.1.1)
    (hX.hasGaussianLaw S) (hY.hasGaussianLaw S)
    (fun i => (hX.hasGaussianLaw_eval i.1).memLp_two)
    (fun i => (hY.hasGaussianLaw_eval i.1).memLp_two)
    (fun i => (integral_lateralPair_eq_zero h₁ i.1.2.1).trans (integral_lateralPair_eq_zero h₂ i.1.2.1).symm)
    (fun i j => (covariance_lateralPair_eq h₁ i.1.2.1 j.1.2.1).trans
      (covariance_lateralPair_eq h₂ i.1.2.1 j.1.2.1).symm)

end MatedCRT.ConeMeanZeroRestriction

end
