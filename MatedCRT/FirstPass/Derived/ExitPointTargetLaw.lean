import MatedCRT.FirstPass.Derived.ExitPointLocalUniform
import MatedCRT.FirstPass.Derived.TargetLawRotation

/-!
# The exit point under the limit law of the invariance principle

The limit law of Theorem 1.16 of Gwynne, Miller and Sheffield (arXiv 1807.07515) is the law of a
planar Brownian motion `A B` with an invertible factor `A` (its covariance `A Aᵀ` is positive
definite). For a bounded open set `U ∋ 0` with a measurable exterior normal field (for instance an
open axis-parallel square), we prove that the exit point from `U` of the complex reading of the path
is a Borel function of the path and is continuous, for the compact-open topology, at almost every
path of the limit law. These are the hypotheses of the continuous mapping theorem with almost sure
continuity, applied in condition 1 of the proof of Lemma 3.14 of that paper (the law of the exit
point of the walk from a square converges to the harmonic measure).

The linear image of planar Brownian motion exits `U` where planar Brownian motion exits `A⁻¹ U`,
and `A⁻¹ U` again has an exterior normal field, `p ↦ Aᵀ v(A p)`.

## Main statements

* `measurable_exitPoint`, `measurable_exitPoint_eucPathToComplex`: Borel measurability.
* `isUnit_det_factor`: the factor of the limit law is invertible.
* `exteriorNormal_preimage`: exterior normal fields pull back under linear automorphisms.
* `ae_continuousAt_exitPoint_pathLaw`: almost sure continuity of the exit point under the limit law.
-/

open MeasureTheory Filter Set Topology MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

open MatedCRT.TemplateEventCompactOpen MatedCRT.TargetLawTemplateEvent MatedCRT.TargetLawRotation
open ReflectedGMS.StatementIngredients

/-! ### Measurability -/

/-- The exit point is the exit position of Harmonic-Balls (both read the path at time `0` when it never exits). -/
theorem exitPoint_eq_exitPosition (U : Set ℂ) (b : ContinuousPath ℂ) :
    exitPoint U ⇑b = exitPosition U b := rfl

/-- The exit point from an open set is a Borel function of the continuous path. -/
theorem measurable_exitPoint {U : Set ℂ} (hU : IsOpen U) :
    Measurable fun b : ContinuousPath ℂ => exitPoint U ⇑b :=
  measurable_exitPosition hU

/-- The exit point of the complex reading of a planar path is a Borel function of the path. -/
theorem measurable_exitPoint_eucPathToComplex {U : Set ℂ} (hU : IsOpen U) :
    Measurable fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω) :=
  (measurable_exitPoint hU).comp measurable_eucPathToComplex

/-! ### Invertible matrices -/

theorem matrixLinearMap_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    matrixLinearMap (A * B) = (matrixLinearMap A).comp (matrixLinearMap B) :=
  LinearMap.ext fun z => Complex.ext (by simp [Matrix.mul_apply, Fin.sum_univ_two]; ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_two]; ring)

theorem matrixLinearMap_one : matrixLinearMap 1 = LinearMap.id :=
  LinearMap.ext fun z => Complex.ext (by simp) (by simp)

/-- The linear automorphism of `ℂ` with an invertible matrix `A` in the basis `1, i`. -/
noncomputable def matrixEquiv {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A.det) : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.ofLinearMap (matrixLinearMap A) (matrixLinearMap A⁻¹)
    (by rw [← matrixLinearMap_mul, Matrix.mul_nonsing_inv A hA, matrixLinearMap_one])
    (by rw [← matrixLinearMap_mul, Matrix.nonsing_inv_mul A hA, matrixLinearMap_one])).toContinuousLinearEquiv

@[simp] theorem matrixEquiv_apply {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A.det) (z : ℂ) :
    matrixEquiv hA z = matrixLinearMap A z := rfl

/-- The factor of the limit law is invertible: its covariance `A Aᵀ` is positive definite. -/
theorem isUnit_det_factor (target : AnisotropicBrownianTarget) : IsUnit target.factor.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨ξ, hξ, hξA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hpos := target.positiveDefinite.2 ξ hξ
  rw [target.covariance_eq, covarianceOfBrownianFactor] at hpos
  have h0 := congrFun hξA 0
  have h1 := congrFun hξA 1
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h0 h1
  simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply] at hpos
  refine absurd hpos (not_lt.mpr (le_of_eq ?_))
  linear_combination (ξ 0 * target.factor 0 0 + ξ 1 * target.factor 1 0) * h0 +
    (ξ 0 * target.factor 0 1 + ξ 1 * target.factor 1 1) * h1

/-! ### Exterior normals and exit points under linear automorphisms -/

/-- The preimage of a bounded set under a linear automorphism is bounded. -/
theorem isBounded_preimage (L : ℂ ≃L[ℝ] ℂ) {U : Set ℂ} (hUb : Bornology.IsBounded U) :
    Bornology.IsBounded (L ⁻¹' U) := by
  have := (L.symm : ℂ →L[ℝ] ℂ).lipschitzWith.isBounded_image hUb
  rwa [ContinuousLinearEquiv.coe_coe, L.image_symm_eq_preimage] at this

/-- The pulled-back normal field `p ↦ Lᵀ v(L p)` is measurable. -/
theorem measurable_adjoint_normal (L : ℂ ≃L[ℝ] ℂ) {v : ℂ → ℂ} (hv : Measurable v) :
    Measurable fun p => ContinuousLinearMap.adjoint (L : ℂ →L[ℝ] ℂ) (v (L p)) :=
  (ContinuousLinearMap.adjoint (L : ℂ →L[ℝ] ℂ)).continuous.measurable.comp
    (hv.comp L.continuous.measurable)

/-- **Exterior normals pull back.** If `v` is an exterior normal field of `U` (at each frontier point `p`, the open
half-plane `{q | ⟪v p, q - p⟫ > 0}` misses the closure of `U`), then `p ↦ Lᵀ v(L p)` is one of `L⁻¹ U`. -/
theorem exteriorNormal_preimage (L : ℂ ≃L[ℝ] ℂ) {U : Set ℂ} {v : ℂ → ℂ}
    (hvU : ∀ p ∈ frontier U, v p ≠ 0 ∧ ∀ q : ℂ, 0 < inner ℝ (v p) (q - p) → q ∉ closure U) :
    ∀ p ∈ frontier (L ⁻¹' U), ContinuousLinearMap.adjoint (L : ℂ →L[ℝ] ℂ) (v (L p)) ≠ 0 ∧
      ∀ q : ℂ, 0 < inner ℝ (ContinuousLinearMap.adjoint (L : ℂ →L[ℝ] ℂ) (v (L p))) (q - p) →
        q ∉ closure (L ⁻¹' U) := by
  intro p hp
  have e1 : L ⁻¹' frontier U = frontier (L ⁻¹' U) := L.toHomeomorph.preimage_frontier U
  have e2 : L ⁻¹' closure U = closure (L ⁻¹' U) := L.toHomeomorph.preimage_closure U
  rw [← e1] at hp
  obtain ⟨hne, hq⟩ := hvU (L p) hp
  refine ⟨fun h0 => hne ?_, fun q hq0 => ?_⟩
  · have key := ContinuousLinearMap.adjoint_inner_left (L : ℂ →L[ℝ] ℂ) (L.symm (v (L p))) (v (L p))
    rw [h0, inner_zero_left, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at key
    exact inner_self_eq_zero.mp key.symm
  · rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe, map_sub] at hq0
    rw [← e2]
    exact hq (L q) hq0

theorem pathExitTime_symm_comp (L : ℂ ≃L[ℝ] ℂ) (U : Set ℂ) (f : ℝ≥0 → ℂ) :
    pathExitTime (L ⁻¹' U) (fun t => L.symm (f t)) = pathExitTime U f := by
  simp only [pathExitTime, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]

theorem exitPoint_symm_comp (L : ℂ ≃L[ℝ] ℂ) (U : Set ℂ) (f : ℝ≥0 → ℂ) :
    exitPoint (L ⁻¹' U) (fun t => L.symm (f t)) = L.symm (exitPoint U f) := by
  unfold exitPoint
  rw [pathExitTime_symm_comp]

/-- Continuity of the exit point transfers from `L⁻¹ U` at `b` to `U` at `L ∘ b`. -/
theorem continuousAt_exitPoint_comp {L : ℂ ≃L[ℝ] ℂ} {U : Set ℂ} {b : ContinuousPath ℂ}
    (hb : ContinuousAt (fun g : ContinuousPath ℂ => exitPoint (L ⁻¹' U) ⇑g) b) :
    ContinuousAt (fun g : ContinuousPath ℂ => exitPoint U ⇑g)
      ((⟨L, L.continuous⟩ : C(ℂ, ℂ)).comp b) := by
  set Ψ : ContinuousPath ℂ → ContinuousPath ℂ := (⟨L.symm, L.symm.continuous⟩ : C(ℂ, ℂ)).comp with hΨdef
  have hΨ : Continuous Ψ := ContinuousMap.continuous_postcomp _
  have hfun : (fun g : ContinuousPath ℂ => exitPoint U ⇑g) =
      fun g => L (exitPoint (L ⁻¹' U) ⇑(Ψ g)) := by
    funext g
    rw [show (⇑(Ψ g) : ℝ≥0 → ℂ) = fun t => L.symm (g t) from rfl, exitPoint_symm_comp,
      ContinuousLinearEquiv.apply_symm_apply]
  have hΨb : Ψ ((⟨L, L.continuous⟩ : C(ℂ, ℂ)).comp b) = b := by
    ext t
    simp [hΨdef]
  rw [hfun]
  exact L.continuous.continuousAt.comp (hb.comp_of_eq hΨ.continuousAt hΨb)

/-! ### The limit law -/

/-- The limit law is the image of planar Brownian motion from `0` under `b ↦ A b`, read in the basis `1, i`. -/
theorem pathLaw_eq_map (target : AnisotropicBrownianTarget) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) =
      (planarBrownianMotion 0).map
        (fun b => linearImageBrownianPath target.factor (complexPathToEuc b)) := by
  rw [AnisotropicBrownianTarget.pathLaw, anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map,
    eq_map_complexPathToEuc target.isStandard,
    Measure.map_map (measurable_linearImageBrownianPath _) measurable_complexPathToEuc]
  rfl

theorem linearImageBrownianPath_complexPathToEuc_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A.det)
    (b : ContinuousPath ℂ) :
    linearImageBrownianPath A (complexPathToEuc b) =
      complexPathToEuc ((⟨matrixEquiv hA, (matrixEquiv hA).continuous⟩ : C(ℂ, ℂ)).comp b) := by
  ext t i
  fin_cases i <;> simp [linearImageBrownianPath_apply, Fin.sum_univ_two]

/-- **Almost sure continuity of the exit point under the limit law.** For a bounded open set `U ∋ 0` with a
measurable exterior normal field, the exit point from `U` of the complex reading of the path is continuous
(compact-open topology) at almost every path of the limit law of the invariance principle. -/
theorem ae_continuousAt_exitPoint_pathLaw (target : AnisotropicBrownianTarget) {U : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {v : ℂ → ℂ} (hv : Measurable v)
    (hvU : ∀ p ∈ frontier U, v p ≠ 0 ∧ ∀ q : ℂ, 0 < inner ℝ (v p) (q - p) → q ∉ closure U)
    (h0 : (0 : ℂ) ∈ U) :
    ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω := by
  have hA := isUnit_det_factor target
  set L := matrixEquiv hA with hL
  have hmeas : MeasurableSet {ω : BouRabeeGwynne.BrownianPath 2 |
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω} :=
    (IsGδ.setOfPred_continuousAt _).measurableSet
  have hS : Measurable fun b : ContinuousPath ℂ =>
      linearImageBrownianPath target.factor (complexPathToEuc b) :=
    (measurable_linearImageBrownianPath _).comp measurable_complexPathToEuc
  rw [pathLaw_eq_map, ae_map_iff hS.aemeasurable hmeas]
  have h0' : (0 : ℂ) ∈ L ⁻¹' U := by simpa using h0
  filter_upwards [ae_continuousAt_exitPoint_planarBrownian_of_exteriorNormal (hU.preimage L.continuous)
    (isBounded_preimage L hUb) (measurable_adjoint_normal L hv) (exteriorNormal_preimage L hvU) h0']
    with b hb
  rw [linearImageBrownianPath_complexPathToEuc_eq hA b]
  exact (continuousAt_exitPoint_comp hb).comp_of_eq continuous_eucPathToComplex.continuousAt
    (eucPathToComplex_complexPathToEuc _)

/-- The exit point from an open axis-parallel square containing `0` is continuous at almost every path of the
limit law. -/
theorem ae_continuousAt_exitPoint_openSquare_pathLaw (target : AnisotropicBrownianTarget) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}) :
    ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 =>
        exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} ⇑(eucPathToComplex ω)) ω :=
  ae_continuousAt_exitPoint_pathLaw target (isOpen_openSquare c a) (isBounded_openSquare c a)
    (measurable_squareNormal c) (squareNormal_exteriorNormal (lt_of_le_of_lt (abs_nonneg _) h0.1)) h0

end MatedCRT.StopAtExitCmp

/-! ## Audit -/
#print axioms MatedCRT.StopAtExitCmp.measurable_exitPoint_eucPathToComplex
#print axioms MatedCRT.StopAtExitCmp.isUnit_det_factor
#print axioms MatedCRT.StopAtExitCmp.ae_continuousAt_exitPoint_pathLaw
#print axioms MatedCRT.StopAtExitCmp.ae_continuousAt_exitPoint_openSquare_pathLaw
