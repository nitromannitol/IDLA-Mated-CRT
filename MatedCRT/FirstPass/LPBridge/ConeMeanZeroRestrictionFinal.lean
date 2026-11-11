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
open scoped NNReal

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

/-! ### Absolute convergence of the cone radial integral (`ConeRadialAbsIntegrable`) -/

section ConeRadial

open MarkovProcess

variable {γ : ℝ}

/-- A measurable version of the circle averages of a quantum cone: `F ω = hcirc ω` for every `ω` outside the
measurable null set where continuity of `(r, z) ↦ h_r(z)` on `(0, ∞) × ℂ` fails (`IsQuantumCone.ae_continuousOn_circle`),
and `F ω = 0` on that set. -/
lemma exists_measurable_circle_version_quantumCone {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∃ F : Ω → C(CircleParameter, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2 := by
  classical
  set bad : Set Ω := {ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)} with hbad
  set S : Set Ω := (toMeasurable P bad)ᶜ with hS
  have hSm : MeasurableSet S := (measurableSet_toMeasurable P bad).compl
  have hbad0 : P bad = 0 := ae_iff.mp h.ae_continuousOn_circle
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := compl_mem_ae_iff.mpr (by rw [measure_toMeasurable, hbad0])
  have hcont : ∀ ω ∈ S, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable P bad hc)
  let F : Ω → C(CircleParameter, ℝ) := fun ω =>
    ⟨fun p => if ω ∈ S then hcirc ω (p.1 : ℝ) p.2 else 0, by
      by_cases hω : ω ∈ S
      · simp only [hω, ↓reduceIte]
        have hmap : Continuous (fun p : CircleParameter => ((p.1 : ℝ), p.2)) :=
          (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
        exact (hcont ω hω).comp_continuous hmap (fun p => ⟨p.1.2, Set.mem_univ _⟩)
      · simp only [hω, ↓reduceIte]
        exact continuous_const⟩
  have hFm : Measurable F := by
    refine ContinuousMap.measurable_iff_eval.mpr fun p => ?_
    exact Measurable.ite hSm (h.measurable_circle (p.1 : ℝ) p.2 p.1.2) measurable_const
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hSae] with ω hω p
  simp [F, hω]

/-- The radial process of a quantum cone is measurable (its coordinates are circle averages at positive radii). -/
lemma measurable_radialProcess_quantumCone {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω => radialProcess (hcirc ω) := by
  unfold radialProcess
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun t => h.measurable_circle _ _ (Real.exp_pos _)
  · exact measurable_pi_iff.mpr fun s => h.measurable_circle _ _ (Real.exp_pos _)

/-- One-time marginal of the cone's circle averages: `h_{e^{-t}}(0)` has the law of `B_t + γ t` with
`B_t ∼ N(0, t)` (Definition 2.1, `radial_law`). -/
lemma map_circle_eq_gaussian_shift {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) (t : ℝ≥0) :
    P.map (fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0) =
      (gaussianReal 0 t).map (fun x => x + γ * (t : ℝ)) := by
  obtain ⟨ν, hν, hlaw⟩ := h.radial_law
  have : IsProbabilityMeasure ν := hν.1
  have hm1 : Measurable (fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s + γ * (s : ℝ)) :=
    measurable_pi_iff.mpr fun s =>
      (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).add_const _
  have hm2 : Measurable (fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * (s : ℝ)) :=
    measurable_pi_iff.mpr fun s =>
      (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).sub_const _
  have hν' : (ν.map fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * (s : ℝ)) univ = 1 := by
    rw [Measure.map_apply hm2 MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hpt : Measurable (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.1 t) :=
    (measurable_pi_apply t).comp measurable_fst
  have hΦ := measurable_radialProcess_quantumCone h
  have hcoord : (fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0) =
      (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.1 t) ∘ (fun ω => radialProcess (hcirc ω)) := rfl
  rw [hcoord, ← Measure.map_map hpt hΦ, hlaw, quantumConeRadialLaw]
  have hfst : (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.1 t) = (fun a : ℝ≥0 → ℝ => a t) ∘ Prod.fst := rfl
  rw [hfst, ← Measure.map_map (measurable_pi_apply t) measurable_fst, Measure.map_fst_prod, hν', one_smul,
    Measure.map_map (measurable_pi_apply t) hm1, ← brownianMotion_map_eval t 0,
    Measure.map_map (measurable_add_const _)
      (show Measurable (fun omega : ContinuousPath ℝ => omega t) from
        ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t)]
  rfl

/-- The Gaussian shift `x ↦ x + c` is integrable against `N(0, t)`. -/
lemma integrable_add_const_gaussian (t : ℝ≥0) (c : ℝ) :
    Integrable (fun x : ℝ => x + c) (gaussianReal 0 t) :=
  ((memLp_id_gaussianReal 2 (μ := 0) (v := t)).integrable one_le_two).add (integrable_const c)

/-- Gaussian absolute moment bound: `E|X + c| ≤ 1 + t + |c|` for `X ∼ N(0, t)`. -/
lemma integral_norm_add_const_gaussian_le (t : ℝ≥0) (c : ℝ) :
    ∫ x, ‖x + c‖ ∂(gaussianReal 0 t) ≤ 1 + t + |c| := by
  have hL2 : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 t) := memLp_id_gaussianReal 2 (μ := 0) (v := t)
  have hsq : ∫ x, x ^ 2 ∂(gaussianReal 0 t) = t := by
    have hv : variance (fun x : ℝ => x) (gaussianReal 0 t) = t := variance_id_gaussianReal
    rw [variance_eq_sub hL2, integral_id_gaussianReal] at hv
    simp only [Pi.pow_apply] at hv
    linarith
  have hI1 : Integrable (fun x : ℝ => ‖x + c‖) (gaussianReal 0 t) :=
    (integrable_add_const_gaussian t c).norm
  have hB : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 t) := hL2.integrable_sq
  have hA : Integrable (fun x : ℝ => 1 + x ^ 2) (gaussianReal 0 t) := (integrable_const 1).add hB
  have hI2 : Integrable (fun x : ℝ => 1 + x ^ 2 + |c|) (gaussianReal 0 t) :=
    hA.add (integrable_const _)
  calc ∫ x, ‖x + c‖ ∂(gaussianReal 0 t) ≤ ∫ x, (1 + x ^ 2 + |c|) ∂(gaussianReal 0 t) := by
        refine integral_mono hI1 hI2 fun x => ?_
        rw [Real.norm_eq_abs]
        have h1 : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
        have h2 : |x + c| ≤ |x| + |c| := abs_add_le x c
        linarith
    _ = 1 + t + |c| := by
        rw [integral_add hA (integrable_const _), integral_add (integrable_const 1) hB, integral_const,
          integral_const, hsq]
        simp

/-- For `0 < ‖x‖ < 1` the circle average `h_{|x|}(0)` of a quantum cone is integrable and
`E|h_{|x|}(0)| ≤ 1 + (1 + |γ|) / |x|`. -/
lemma integrable_and_norm_integral_le_circle {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {x : ℂ} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    Integrable (fun ω => hcirc ω ‖x‖ 0) P ∧
      ∫ ω, ‖hcirc ω ‖x‖ 0‖ ∂P ≤ 1 + (1 + |γ|) * ‖x‖⁻¹ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set t : ℝ≥0 := Real.toNNReal (-Real.log ‖x‖) with ht
  have hlog : (t : ℝ) = -Real.log ‖x‖ :=
    Real.coe_toNNReal _ (neg_nonneg.2 (Real.log_nonpos (norm_nonneg x) hx1.le))
  have hexp : Real.exp (-(t : ℝ)) = ‖x‖ := by rw [hlog, neg_neg, Real.exp_log hr]
  have key : ∀ ω, hcirc ω ‖x‖ 0 = hcirc ω (Real.exp (-(t : ℝ))) 0 := fun ω => by rw [hexp]
  have hmeas : Measurable (fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0) :=
    h.measurable_circle _ _ (Real.exp_pos _)
  have hlaw := map_circle_eq_gaussian_shift h t
  simp only [key]
  constructor
  · refine (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).mp ?_
    rw [hlaw]
    exact (integrable_map_measure aestronglyMeasurable_id (measurable_add_const _).aemeasurable).mpr
      (integrable_add_const_gaussian t _)
  · have hnorm : ∫ ω, ‖hcirc ω (Real.exp (-(t : ℝ))) 0‖ ∂P = ∫ x, ‖x + γ * (t : ℝ)‖ ∂(gaussianReal 0 t) := by
      rw [← integral_map hmeas.aemeasurable measurable_norm.aestronglyMeasurable, hlaw,
        integral_map (measurable_add_const _).aemeasurable measurable_norm.aestronglyMeasurable]
    have ht1 : (t : ℝ) ≤ ‖x‖⁻¹ := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
      rw [Real.log_inv] at this
      rw [hlog]
      linarith
    have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    rw [hnorm]
    refine (integral_norm_add_const_gaussian_le t (γ * (t : ℝ))).trans ?_
    have habs : |γ * (t : ℝ)| = |γ| * (t : ℝ) := by rw [abs_mul, abs_of_nonneg ht0]
    rw [habs]
    nlinarith [mul_le_mul_of_nonneg_left ht1 (abs_nonneg γ)]

end ConeRadial

section ConeRadialMain

open MarkovProcess

variable {γ : ℝ}

/-- **`ConeRadialAbsIntegrable`.** For a quantum cone and a test function `φ` supported in the unit ball, the radial
pairings `∫ φ(x) h_{|x|}(0) dx` converge absolutely almost surely. Proof: Tonelli on `P ⊗ Leb` for a measurable
version of the circle averages, with `E|h_{|x|}(0)| ≤ 1 + (1 + |γ|)/|x|` (`integrable_and_norm_integral_le_circle`) and
`∫_{B(0,1)} |x|⁻¹ dx < ∞` (`integrableOn_ball_of_norm_le_rpow`). -/
theorem coneRadialAbsIntegrable_holds : ConeRadialAbsIntegrable := by
  intro γ Ω _ P hC hcirc hP h φ hφ
  classical
  obtain ⟨F, hF, hFae⟩ := exists_measurable_circle_version_quantumCone h
  obtain ⟨M, hM⟩ := (hφ.1.continuous).bounded_above_of_compact_support hφ.2.1
  have hφm : Measurable φ := hφ.1.continuous.measurable
  set G : Ω × ℂ → ℝ := fun q => φ q.2 * F q.1 (radialPoint q.2) with hG
  have hGm : Measurable G :=
    Measurable.mul (hφm.comp measurable_snd)
      ((measurable_circle_version_joint hF).comp
        (measurable_fst.prodMk (measurable_radialPoint.comp measurable_snd)))
  have hsupp : ∀ y, φ y ≠ 0 → ‖y‖ < 1 := fun y hy => by
    have hmem : y ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hy)
    simpa using hφ.2.2 hmem
  have h0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with y hy
    exact hy
  have hint : Integrable G (P.prod volume) := by
    rw [integrable_prod_iff' hGm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [h0] with y hy
      by_cases hφy : φ y = 0
      · exact (integrable_const (0 : ℝ)).congr (ae_of_all _ fun ω => by simp [G, hφy])
      · have hI := (integrable_and_norm_integral_le_circle h hy (hsupp y hφy)).1
        refine hI.const_mul (φ y) |>.congr ?_
        filter_upwards [hFae] with ω hω
        simp [G, hω, radialPoint, hy]
    · have hg : StronglyMeasurable (fun y : ℂ => ∫ ω, ‖G (ω, y)‖ ∂P) :=
        hGm.norm.stronglyMeasurable.integral_prod_left
      have hball : IntegrableOn (fun y : ℂ => ‖y‖⁻¹) (Metric.ball (0 : ℂ) 1) := by
        refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (r := 1) (by simp) (by simp) ?_ ?_
        · exact ae_of_all _ fun y => by simp [Real.rpow_neg_one]
        · exact (measurable_norm.inv).aestronglyMeasurable
      have hmaj : Integrable (Set.indicator (Metric.ball (0 : ℂ) 1)
          (fun y : ℂ => M * (1 + (1 + |γ|) * ‖y‖⁻¹))) := by
        refine IntegrableOn.integrable_indicator ?_ measurableSet_ball
        have h1 : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (Metric.ball (0 : ℂ) 1) :=
          integrableOn_const measure_ball_lt_top.ne
        exact ((h1.add (hball.const_mul (1 + |γ|))).const_mul M)
      refine Integrable.mono' hmaj hg.aestronglyMeasurable ?_
      filter_upwards [h0] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
      by_cases hy1 : ‖y‖ < 1
      · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hy1)]
        have hfin := integrable_and_norm_integral_le_circle h hy hy1
        have hcongr : ∫ ω, ‖G (ω, y)‖ ∂P = |φ y| * ∫ ω, ‖hcirc ω ‖y‖ 0‖ ∂P := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [hFae] with ω hω
          simp [G, hω, radialPoint, hy]
        have hX0 : 0 ≤ ∫ ω, ‖hcirc ω ‖y‖ 0‖ ∂P := integral_nonneg fun ω => norm_nonneg _
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        have hφM : |φ y| ≤ M := by simpa [Real.norm_eq_abs] using hM y
        rw [hcongr]
        calc |φ y| * ∫ ω, ‖hcirc ω ‖y‖ 0‖ ∂P ≤ M * ∫ ω, ‖hcirc ω ‖y‖ 0‖ ∂P :=
              mul_le_mul_of_nonneg_right hφM hX0
          _ ≤ M * (1 + (1 + |γ|) * ‖y‖⁻¹) := mul_le_mul_of_nonneg_left hfin.2 hM0
      · have hφy : φ y = 0 :=
          image_eq_zero_of_notMem_tsupport fun hm => hy1 (mem_ball_zero_iff.mp (hφ.2.2 hm))
        simp [G, hφy, hy1]
  filter_upwards [hint.prod_right_ae, hFae] with ω hωint hω
  refine hωint.congr ?_
  filter_upwards [h0] with y hy
  simp [G, hω, radialPoint, hy]

end ConeRadialMain

end MatedCRT.ConeMeanZeroRestriction

end
