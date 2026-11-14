import MatedCRT.FirstPass.Derived.TargetLawTemplateEvent
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

/-!
# Rotation invariance of planar Brownian motion and the isotropic limit law

The limit in the quenched invariance principle (Theorem 1.16 of Gwynne-Miller-Sheffield) is the law
of `t ↦ A B_t`, where `B` is a standard Euclidean Brownian motion and `Σ = A Aᵀ` is the covariance
matrix. When `Σ = c I` (the isotropic case, which holds for mated-CRT maps by rotation invariance),
the factor `A` is `√c O` for an orthogonal matrix `O`, not necessarily `√c I`. This file shows that
the law of `O B` is again the standard law, and hence that the limit law gives to the robust
disconnection event `E_δ` the probability that planar Brownian motion started from `0` lies in it,
for every factor of `c I`.

* `stdPlanarGaussian_eq_stdGaussian`: the standard planar Gaussian is Mathlib's standard Gaussian
  measure on the real inner product space `ℂ`; hence it is invariant under every real linear
  isometry of `ℂ` (`map_stdPlanarGaussian_linearIsometryEquiv`).
* `planarHeatSemigroup_isometry_conjugate`, `planarBrownianMotion_map_linearIsometryEquiv`: the
  planar heat semigroup is conjugate to itself under a real linear isometry `L` of `ℂ`, so
  `𝓑^{L u}` has the law of `L 𝓑^u`.
* `map_linearImageBrownianPath_of_transpose_mul_self`: if `Oᵀ O = 1`, every standard Euclidean
  Brownian law is invariant under `ω ↦ O ω`.
* `pathLaw_preimage_templateDisconnectionEvent_of_covariance`: if the covariance of the target is
  `c I` with `c > 0`, then `target.pathLaw (E_δ) = P(𝓑⁰ ∈ E_δ)`; and the lower bound
  `1 - (1 - p₀)^{K(δ)} ≤ target.pathLaw (E_δ)`.
-/

namespace MatedCRT.TargetLawRotation

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set
open MatedCRT MatedCRT.TemplateEventOpen MatedCRT.TemplateEventCompactOpen
open MatedCRT.TargetLawTemplateEvent
open scoped NNReal ENNReal

/-! ### The standard planar Gaussian -/

/-- The standard planar Gaussian is the standard Gaussian measure of the real inner product space
`ℂ`. -/
theorem stdPlanarGaussian_eq_stdGaussian : stdPlanarGaussian = stdGaussian ℂ := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI, stdPlanarGaussian,
    planarGaussian, Complex.zero_re, Complex.zero_im,
    ← (measurePreserving_piFinTwo fun _ : Fin 2 => gaussianReal 0 1).map_eq,
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable
      (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ).measurable]
  congr 1
  funext x
  apply Complex.ext <;> simp [Fin.sum_univ_two]

/-- The standard planar Gaussian is invariant under every real linear isometry of `ℂ`. -/
theorem map_stdPlanarGaussian_linearIsometryEquiv (L : ℂ ≃ₗᵢ[ℝ] ℂ) :
    stdPlanarGaussian.map L = stdPlanarGaussian := by
  rw [stdPlanarGaussian_eq_stdGaussian]
  exact stdGaussian_map L

/-- The planar heat semigroup is conjugate to itself under a real linear isometry of `ℂ`. -/
theorem planarHeatSemigroup_isometry_conjugate (L : ℂ ≃ₗᵢ[ℝ] ℂ) :
    SubMarkovKernelSemigroup.IsRescaledConjugate planarHeatSemigroup planarHeatSemigroup
      L.toHomeomorph 1 := by
  intro t z
  rw [one_mul, planarHeatSemigroup_apply, planarHeatSemigroup_apply,
    planarGaussian_eq_map_add_sqrt_mul, planarGaussian_eq_map_add_sqrt_mul,
    Measure.map_map L.toHomeomorph.continuous.measurable (by fun_prop)]
  conv_lhs => rw [← map_stdPlanarGaussian_linearIsometryEquiv L]
  rw [Measure.map_map (by fun_prop) L.continuous.measurable]
  congr 1
  funext w
  have h : ((Real.sqrt t : ℝ) : ℂ) * L w = L (((Real.sqrt t : ℝ) : ℂ) * w) := by
    rw [← Complex.real_smul, ← Complex.real_smul, map_smul]
  simp [h]

/-- **Rotation and reflection invariance of planar Brownian motion.** For a real linear isometry
`L` of `ℂ`, planar Brownian motion started from `L u` is the image of planar Brownian motion started
from `u` under `ω ↦ L ∘ ω`. -/
theorem planarBrownianMotion_map_linearIsometryEquiv (L : ℂ ≃ₗᵢ[ℝ] ℂ) (u : ℂ) :
    planarBrownianMotion (L u) =
      (planarBrownianMotion u).map (ContinuousPath.rescale L.toHomeomorph 1) := by
  simpa using planarBrownianMotion_map_rescale_of_heat_conjugacy L.toHomeomorph 1 one_pos
    (planarHeatSemigroup_isometry_conjugate L) u

/-! ### Orthogonal matrices -/

/-- The real linear map of `ℂ` with matrix `O` in the basis `1, i`. -/
noncomputable def matrixLinearMap (O : Matrix (Fin 2) (Fin 2) ℝ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨O 0 0 * z.re + O 0 1 * z.im, O 1 0 * z.re + O 1 1 * z.im⟩
  map_add' z w := by
    apply Complex.ext <;> simp <;> ring
  map_smul' r z := by
    apply Complex.ext <;> simp <;> ring

@[simp] theorem matrixLinearMap_re (O : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (matrixLinearMap O z).re = O 0 0 * z.re + O 0 1 * z.im := rfl

@[simp] theorem matrixLinearMap_im (O : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (matrixLinearMap O z).im = O 1 0 * z.re + O 1 1 * z.im := rfl

/-- For `Oᵀ O = 1` the linear map with matrix `O` preserves the norm. -/
theorem norm_matrixLinearMap {O : Matrix (Fin 2) (Fin 2) ℝ} (hO : O.transpose * O = 1) (z : ℂ) :
    ‖matrixLinearMap O z‖ = ‖z‖ := by
  have h00 := congrFun (congrFun hO 0) 0
  have h01 := congrFun (congrFun hO 0) 1
  have h11 := congrFun (congrFun hO 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  have hsq : ‖matrixLinearMap O z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      matrixLinearMap_re, matrixLinearMap_im]
    linear_combination z.re ^ 2 * h00 + 2 * z.re * z.im * h01 + z.im ^ 2 * h11
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- The real linear isometry of `ℂ` with orthogonal matrix `O` in the basis `1, i`. -/
noncomputable def matrixIsometry {O : Matrix (Fin 2) (Fin 2) ℝ} (hO : O.transpose * O = 1) :
    ℂ ≃ₗᵢ[ℝ] ℂ :=
  (⟨matrixLinearMap O, norm_matrixLinearMap hO⟩ : ℂ →ₗᵢ[ℝ] ℂ).toLinearIsometryEquiv rfl

@[simp] theorem matrixIsometry_apply {O : Matrix (Fin 2) (Fin 2) ℝ} (hO : O.transpose * O = 1)
    (z : ℂ) : matrixIsometry hO z = matrixLinearMap O z := rfl

/-- Reading paths in the basis `1, i` intertwines the matrix `O` with the isometry it defines. -/
theorem linearImageBrownianPath_complexPathToEuc {O : Matrix (Fin 2) (Fin 2) ℝ}
    (hO : O.transpose * O = 1) (b : ContinuousPath ℂ) :
    ReflectedGMS.StatementIngredients.linearImageBrownianPath O (complexPathToEuc b) =
      complexPathToEuc (ContinuousPath.rescale (matrixIsometry hO).toHomeomorph 1 b) := by
  ext t i
  fin_cases i <;>
    simp [ReflectedGMS.StatementIngredients.linearImageBrownianPath_apply, Fin.sum_univ_two]

/-- **Orthogonal invariance of the standard Euclidean Brownian law.** -/
theorem map_linearImageBrownianPath_of_transpose_mul_self
    {μ : Measure (BouRabeeGwynne.BrownianPath 2)} (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ)
    {O : Matrix (Fin 2) (Fin 2) ℝ} (hO : O.transpose * O = 1) :
    μ.map (ReflectedGMS.StatementIngredients.linearImageBrownianPath O) = μ := by
  have hfun : ReflectedGMS.StatementIngredients.linearImageBrownianPath O ∘ complexPathToEuc =
      complexPathToEuc ∘ ContinuousPath.rescale (matrixIsometry hO).toHomeomorph 1 :=
    funext (linearImageBrownianPath_complexPathToEuc hO)
  have h0 := planarBrownianMotion_map_linearIsometryEquiv (matrixIsometry hO) 0
  rw [map_zero] at h0
  rw [eq_map_complexPathToEuc hμ,
    Measure.map_map (ReflectedGMS.StatementIngredients.measurable_linearImageBrownianPath O)
      measurable_complexPathToEuc, hfun,
    ← Measure.map_map measurable_complexPathToEuc (ContinuousPath.measurable_rescale _ _), ← h0]

/-! ### The isotropic limit law on `E_δ` -/

/-- A standard Euclidean Brownian law gives to the paths `s ω` whose complex reading lies in `E_δ`
the probability that planar Brownian motion from `0` lies in `E_δ`. -/
theorem measure_preimage_linearImage_smul_one
    {μ : Measure (BouRabeeGwynne.BrownianPath 2)} (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ)
    {s : ℝ≥0} (hs : 0 < s) (δ : ℝ) :
    μ (ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1) ⁻¹'
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ)) =
      planarBrownianMotion 0 (templateDisconnectionEvent δ) := by
  have hE : MeasurableSet (templateDisconnectionEvent δ) :=
    (isOpen_templateDisconnectionEvent δ).measurableSet
  have hU := measurable_eucPathToComplex hE
  have hset : ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1) ⁻¹'
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) =
      BouRabeeGwynne.scaledBrownianPath s⁻¹ ⁻¹'
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) := by
    ext ω
    exact linearImage_mem_iff_scaled_mem hs δ ω
  rw [hset, ← Measure.map_apply (BouRabeeGwynne.measurable_scaledBrownianPath _) hU,
    BouRabeeGwynne.standardBrownianLaw_map_scale hμ (inv_pos.2 hs),
    measure_preimage_eucPathToComplex hμ hE]

/-- **The isotropic limit law on `E_δ`.** If the covariance of the target is `c I` with `c > 0`, the
limit law of the invariance principle gives to `E_δ` the probability that planar Brownian motion
started from `0` lies in `E_δ`, whatever the factor of the covariance. -/
theorem pathLaw_preimage_templateDisconnectionEvent_of_covariance
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1) (δ : ℝ) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) =
      planarBrownianMotion 0 (templateDisconnectionEvent δ) := by
  set s : ℝ≥0 := NNReal.sqrt c with hs_def
  have hs : 0 < s := NNReal.sqrt_pos.2 hc
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hss : (s : ℝ) * s = c := by
    rw [hs_def, ← NNReal.coe_mul, NNReal.mul_self_sqrt]
  set A := target.factor with hA
  have hAA : A * A.transpose = (c : ℝ) • 1 := by
    rw [← hcov, target.covariance_eq]
    rfl
  set O : Matrix (Fin 2) (Fin 2) ℝ := (s : ℝ)⁻¹ • A with hO_def
  have hOO : O * O.transpose = 1 := by
    rw [hO_def, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul,
      smul_smul, ← hss]
    rw [show (s : ℝ)⁻¹ * (s : ℝ)⁻¹ * ((s : ℝ) * s) = 1 by field_simp, one_smul]
  have hO : O.transpose * O = 1 := mul_eq_one_comm.1 hOO
  have hfac : ∀ ω t, ReflectedGMS.StatementIngredients.linearImageBrownianPath A ω t =
      ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1)
        (ReflectedGMS.StatementIngredients.linearImageBrownianPath O ω) t := by
    intro ω t
    rw [linearImageBrownianPath_smul_one_apply]
    ext i
    simp only [ReflectedGMS.StatementIngredients.linearImageBrownianPath_apply, PiLp.smul_apply,
      hO_def, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have hE : MeasurableSet (templateDisconnectionEvent δ) :=
    (isOpen_templateDisconnectionEvent δ).measurableSet
  have hU := measurable_eucPathToComplex hE
  have hV : MeasurableSet (ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1)
      ⁻¹' (eucPathToComplex ⁻¹' templateDisconnectionEvent δ)) :=
    ReflectedGMS.StatementIngredients.measurable_linearImageBrownianPath _ hU
  have hset : ReflectedGMS.StatementIngredients.linearImageBrownianPath A ⁻¹'
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) =
      ReflectedGMS.StatementIngredients.linearImageBrownianPath O ⁻¹'
        (ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1) ⁻¹'
          (eucPathToComplex ⁻¹' templateDisconnectionEvent δ)) := by
    ext ω
    have hω : ReflectedGMS.StatementIngredients.linearImageBrownianPath A ω =
        ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1)
          (ReflectedGMS.StatementIngredients.linearImageBrownianPath O ω) :=
      ContinuousMap.ext (hfac ω)
    simp only [mem_preimage, hω]
  rw [ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget.pathLaw,
    ReflectedGMS.StatementIngredients.anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (ReflectedGMS.StatementIngredients.measurable_linearImageBrownianPath _) hU,
    ← hA, hset,
    ← Measure.map_apply (ReflectedGMS.StatementIngredients.measurable_linearImageBrownianPath _) hV,
    map_linearImageBrownianPath_of_transpose_mul_self target.isStandard hO,
    measure_preimage_linearImage_smul_one target.isStandard hs δ]

/-- The lower bound of `E_δ` under the isotropic limit law. -/
theorem one_sub_le_pathLaw_templateDisconnectionEvent_of_covariance
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1) (δ : ℝ) :
    1 - (1 - templateTubeConst) ^ templateScaleCount δ ≤
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) := by
  rw [pathLaw_preimage_templateDisconnectionEvent_of_covariance target hc hcov δ]
  exact one_sub_le_planarBrownianMotion_templateDisconnectionEvent δ

end MatedCRT.TargetLawRotation

/-! ## Audit -/
#print axioms MatedCRT.TargetLawRotation.planarBrownianMotion_map_linearIsometryEquiv
#print axioms MatedCRT.TargetLawRotation.map_linearImageBrownianPath_of_transpose_mul_self
#print axioms MatedCRT.TargetLawRotation.pathLaw_preimage_templateDisconnectionEvent_of_covariance
#print axioms MatedCRT.TargetLawRotation.one_sub_le_pathLaw_templateDisconnectionEvent_of_covariance
