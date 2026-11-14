import MatedCRT.FirstPass.Derived.TemplateEventCompactOpen
import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianScaling
import LatticeProb.Bonanno.ReflectedGMS.Process.QuenchedLimit

/-!
# The Brownian limit law of the invariance principle on the robust disconnection event

The limit in the quenched invariance principle (Theorem 1.16 of Gwynne-Miller-Sheffield) is the law
`target.pathLaw` of `t ↦ A B_t` on `C([0, ∞), ℝ²)`, where `B` is a standard Brownian motion on
`EuclideanSpace ℝ (Fin 2)` (the predicate `BouRabeeGwynne.IsStandardBrownianLaw`) and `A` is the
factor of the covariance matrix `Σ = A Aᵀ`. The robust disconnection event `E_δ` is a set of complex
paths. This file compares the two encodings of planar Brownian motion and evaluates the limit law on
`E_δ` when `A = s I`.

* `complexPathToEuc`: a complex path read in the orthonormal basis `1, i` of `ℂ`; it is inverse to
  `eucPathToComplex`.
* `isStandardBrownianLaw_map_complexPathToEuc`: standard planar Brownian motion started from `0`,
  read in the basis `1, i`, is a standard Euclidean Brownian law (its coordinates are the real and
  imaginary parts, two independent standard real Brownian motions).
* `eq_map_complexPathToEuc`: hence every standard Euclidean Brownian law is this image
  (uniqueness of the standard law), and `measure_preimage_eucPathToComplex`: for a Borel set `E` of complex paths,
  `μ {ω | ω read in ℂ ∈ E} = P(𝓑⁰ ∈ E)`.
* `pathLaw_preimage_templateDisconnectionEvent`: if `A = s I` with `s > 0`, then the path `s B` is
  the time change `t ↦ s² t` of the Brownian path `t ↦ s B_{t/s²}`, which has the standard law
  (Brownian scaling); `E_δ` is invariant under time changes, so
  `target.pathLaw (E_δ) = P(𝓑⁰ ∈ E_δ)`.
* `one_sub_le_pathLaw_templateDisconnectionEvent`: the resulting lower bound
  `1 - (1 - p₀)^{K(δ)} ≤ target.pathLaw (E_δ)`.
-/

namespace MatedCRT.TargetLawTemplateEvent

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set
open MatedCRT MatedCRT.TemplateEventOpen MatedCRT.TemplateEventCompactOpen
open scoped NNReal ENNReal

/-- A complex path read in the orthonormal basis `1, i` of `ℂ`. -/
noncomputable def complexPathToEuc (b : ContinuousPath ℂ) : BouRabeeGwynne.BrownianPath 2 :=
  (⟨Complex.orthonormalBasisOneI.repr, Complex.orthonormalBasisOneI.repr.continuous⟩ :
    C(ℂ, EuclideanSpace ℝ (Fin 2))).comp b

@[simp] theorem complexPathToEuc_apply (b : ContinuousPath ℂ) (t : ℝ≥0) :
    complexPathToEuc b t = Complex.orthonormalBasisOneI.repr (b t) := rfl

theorem complexPathToEuc_apply_zero (b : ContinuousPath ℂ) (t : ℝ≥0) :
    complexPathToEuc b t 0 = (b t).re := by
  simp

theorem complexPathToEuc_apply_one (b : ContinuousPath ℂ) (t : ℝ≥0) :
    complexPathToEuc b t 1 = (b t).im := by
  simp

theorem continuous_complexPathToEuc : Continuous complexPathToEuc :=
  ContinuousMap.continuous_postcomp _

theorem measurable_complexPathToEuc : Measurable complexPathToEuc :=
  continuous_complexPathToEuc.measurable

theorem measurable_eucPathToComplex : Measurable eucPathToComplex :=
  continuous_eucPathToComplex.measurable

theorem eucPathToComplex_complexPathToEuc (b : ContinuousPath ℂ) :
    eucPathToComplex (complexPathToEuc b) = b := by
  ext t
  simp

/-- The `i`-th coordinate path of a planar path. -/
noncomputable def coordPath (i : Fin 2) (ω : BouRabeeGwynne.BrownianPath 2) : ContinuousPath ℝ :=
  (⟨fun x : EuclideanSpace ℝ (Fin 2) => x i, by fun_prop⟩ :
    C(EuclideanSpace ℝ (Fin 2), ℝ)).comp ω

theorem measurable_coordPath (i : Fin 2) : Measurable (coordPath i) :=
  (ContinuousMap.continuous_postcomp _).measurable

/-- Two independent random variables indexed by `Fin 2` are mutually independent. -/
private lemma iIndepFun_fin_two {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin 2 → Ω → β} (hX : ∀ i, Measurable (X i))
    (h : IndepFun (X 0) (X 1) P) : iIndepFun X P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hX, Measure.infinitePi_eq_pi]
  apply (MeasurableEquiv.piFinTwo fun _ : Fin 2 => β).map_measurableEquiv_injective
  rw [(measurePreserving_piFinTwo fun i => P.map (X i)).map_eq,
    Measure.map_map (MeasurableEquiv.measurable _) (measurable_pi_iff.2 hX)]
  exact (indepFun_iff_map_prod_eq_prod_map_map (hX 0).aemeasurable (hX 1).aemeasurable).1 h

/-- Mutual independence is transported to an image measure. -/
private lemma iIndepFun_map {Ω Ω' β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → Ω'} (hh : Measurable h)
    {X : Fin 2 → Ω' → β} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun (fun i => X i ∘ h) P) : iIndepFun X (P.map h) := by
  have : IsProbabilityMeasure (P.map h) :=
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).mpr inferInstance
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hX, Measure.map_map (measurable_pi_iff.2 hX) hh]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun i => (hX i).comp hh] at hind
  simp_rw [Measure.map_map (hX _) hh]
  exact hind

theorem hasLaw_coordPath_zero :
    HasLaw (coordPath 0) (MarkovProcess.brownianMotion 0)
      ((planarBrownianMotion 0).map complexPathToEuc) := by
  refine ⟨(measurable_coordPath 0).aemeasurable, ?_⟩
  rw [Measure.map_map (measurable_coordPath 0) measurable_complexPathToEuc]
  have h := (PlanarBrownianSpace.hasLaw_re 0).map_eq
  rw [Complex.zero_re] at h
  rw [← h]
  congr 1

theorem hasLaw_coordPath_one :
    HasLaw (coordPath 1) (MarkovProcess.brownianMotion 0)
      ((planarBrownianMotion 0).map complexPathToEuc) := by
  refine ⟨(measurable_coordPath 1).aemeasurable, ?_⟩
  rw [Measure.map_map (measurable_coordPath 1) measurable_complexPathToEuc]
  have h := (PlanarBrownianSpace.hasLaw_im 0).map_eq
  rw [Complex.zero_im] at h
  rw [← h]
  congr 1

/-- Standard planar Brownian motion started from `0`, read in the basis `1, i`, is a standard
Euclidean Brownian law. -/
theorem isStandardBrownianLaw_map_complexPathToEuc :
    BouRabeeGwynne.IsStandardBrownianLaw ((planarBrownianMotion 0).map complexPathToEuc) := by
  refine ⟨(Measure.isProbabilityMeasure_map_iff measurable_complexPathToEuc.aemeasurable).mpr
    inferInstance, ?_, ?_⟩
  · intro i
    fin_cases i
    · have h := PlanarBrownianSpace.isBrownianReal_comp_hasLaw
        (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub 0) hasLaw_coordPath_zero
      simpa [coordPath] using h
    · have h := PlanarBrownianSpace.isBrownianReal_comp_hasLaw
        (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub 0) hasLaw_coordPath_one
      simpa [coordPath] using h
  · have hφ : Measurable fun (p : ContinuousPath ℝ) (t : ℝ≥0) => p t :=
      measurable_pi_iff.mpr fun t => PlanarBrownianSpace.measurable_eval_path t
    have hX : ∀ i : Fin 2, Measurable fun (ω : BouRabeeGwynne.BrownianPath 2) (t : ℝ≥0) => ω t i :=
      fun i => hφ.comp (measurable_coordPath i)
    refine iIndepFun_map measurable_complexPathToEuc hX ?_
    have hRI : IndepFun (fun b : ContinuousPath ℂ => (reImPath b).1)
        (fun b => (reImPath b).2) (planarBrownianMotion 0) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map (PlanarBrownianSpace.hasLaw_re 0).aemeasurable
        (PlanarBrownianSpace.hasLaw_im 0).aemeasurable, (PlanarBrownianSpace.hasLaw_re 0).map_eq,
        (PlanarBrownianSpace.hasLaw_im 0).map_eq]
      exact planarBrownianMotion_map_reImPath 0
    refine iIndepFun_fin_two (fun i => (hX i).comp measurable_complexPathToEuc) ?_
    have h01 := hRI.comp hφ hφ
    convert h01 using 1 <;> funext b t <;> simp

/-- Every standard Euclidean Brownian law is the image of standard planar Brownian motion started
from `0` under reading complex paths in the basis `1, i`. -/
theorem eq_map_complexPathToEuc {μ : Measure (BouRabeeGwynne.BrownianPath 2)}
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) :
    μ = (planarBrownianMotion 0).map complexPathToEuc :=
  BouRabeeGwynne.standardBrownianLaw_unique hμ isStandardBrownianLaw_map_complexPathToEuc

/-- For a Borel set `E` of complex paths, a standard Euclidean Brownian law gives to the paths whose
complex reading lies in `E` the probability that planar Brownian motion from `0` lies in `E`. -/
theorem measure_preimage_eucPathToComplex {μ : Measure (BouRabeeGwynne.BrownianPath 2)}
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) {E : Set (ContinuousPath ℂ)}
    (hE : MeasurableSet E) :
    μ (eucPathToComplex ⁻¹' E) = planarBrownianMotion 0 E := by
  rw [eq_map_complexPathToEuc hμ,
    Measure.map_apply measurable_complexPathToEuc (measurable_eucPathToComplex hE)]
  congr 1
  ext b
  simp [eucPathToComplex_complexPathToEuc]

/-- With the factor `s I`, the linear image of a path is multiplication by `s`. -/
theorem linearImageBrownianPath_smul_one_apply (s : ℝ) (ω : BouRabeeGwynne.BrownianPath 2)
    (t : ℝ≥0) :
    ReflectedGMS.StatementIngredients.linearImageBrownianPath (s • 1) ω t = s • ω t := by
  ext i
  fin_cases i <;>
    simp [ReflectedGMS.StatementIngredients.linearImageBrownianPath_apply, Matrix.one_apply]

/-- The path `s ω` is the time change `t ↦ s² t` of the scaled path `t ↦ s ω (t / s²)`. -/
theorem linearImageBrownianPath_smul_one_eq_scaled {s : ℝ≥0} (hs : 0 < s)
    (ω : BouRabeeGwynne.BrownianPath 2) (t : ℝ≥0) :
    ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1) ω t =
      BouRabeeGwynne.scaledBrownianPath s⁻¹ ω (s ^ 2 * t) := by
  rw [linearImageBrownianPath_smul_one_apply, BouRabeeGwynne.scaledBrownianPath_apply]
  have h : s⁻¹ ^ 2 * (s ^ 2 * t) = t := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul]
  rw [h]
  simp

/-- `E_δ` cannot distinguish the paths `s ω` and `t ↦ s ω (t / s²)`. -/
theorem linearImage_mem_iff_scaled_mem {s : ℝ≥0} (hs : 0 < s) (δ : ℝ)
    (ω : BouRabeeGwynne.BrownianPath 2) :
    eucPathToComplex (ReflectedGMS.StatementIngredients.linearImageBrownianPath ((s : ℝ) • 1) ω) ∈
        templateDisconnectionEvent δ ↔
      eucPathToComplex (BouRabeeGwynne.scaledBrownianPath s⁻¹ ω) ∈
        templateDisconnectionEvent δ := by
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  constructor
  · intro hf
    refine comp_mem_templateDisconnectionEvent hf (OrderIso.mulLeft₀ (s ^ 2)⁻¹ (inv_pos.2 hs2))
      fun t => ?_
    simp only [eucPathToComplex_apply, OrderIso.mulLeft₀_apply]
    rw [linearImageBrownianPath_smul_one_eq_scaled hs, ← mul_assoc,
      mul_inv_cancel₀ hs2.ne', one_mul]
  · intro hg
    refine comp_mem_templateDisconnectionEvent hg (OrderIso.mulLeft₀ (s ^ 2) hs2) fun t => ?_
    simp only [eucPathToComplex_apply, OrderIso.mulLeft₀_apply]
    rw [linearImageBrownianPath_smul_one_eq_scaled hs]

/-- **The limit law on `E_δ`.** If the factor of the target covariance is `s I` with `s > 0`, the
limit law of the invariance principle gives to `E_δ` the probability that planar Brownian motion
started from `0` lies in `E_δ`. -/
theorem pathLaw_preimage_templateDisconnectionEvent
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget) {s : ℝ≥0} (hs : 0 < s)
    (hfac : target.factor = (s : ℝ) • 1) (δ : ℝ) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) =
      planarBrownianMotion 0 (templateDisconnectionEvent δ) := by
  have hE : MeasurableSet (templateDisconnectionEvent δ) :=
    (isOpen_templateDisconnectionEvent δ).measurableSet
  have hU := measurable_eucPathToComplex hE
  have hset : ReflectedGMS.StatementIngredients.linearImageBrownianPath target.factor ⁻¹'
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) =
      BouRabeeGwynne.scaledBrownianPath s⁻¹ ⁻¹'
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) := by
    ext ω
    simp only [mem_preimage, hfac]
    exact linearImage_mem_iff_scaled_mem hs δ ω
  rw [ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget.pathLaw,
    ReflectedGMS.StatementIngredients.anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (ReflectedGMS.StatementIngredients.measurable_linearImageBrownianPath _) hU,
    hset, ← Measure.map_apply (BouRabeeGwynne.measurable_scaledBrownianPath _) hU,
    BouRabeeGwynne.standardBrownianLaw_map_scale target.isStandard (inv_pos.2 hs),
    measure_preimage_eucPathToComplex target.isStandard hE]

/-- The lower bound of `E_δ` under the limit law, for the factor `s I`. -/
theorem one_sub_le_pathLaw_templateDisconnectionEvent
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget) {s : ℝ≥0} (hs : 0 < s)
    (hfac : target.factor = (s : ℝ) • 1) (δ : ℝ) :
    1 - (1 - templateTubeConst) ^ templateScaleCount δ ≤
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) := by
  rw [pathLaw_preimage_templateDisconnectionEvent target hs hfac δ]
  exact one_sub_le_planarBrownianMotion_templateDisconnectionEvent δ

end MatedCRT.TargetLawTemplateEvent

/-! ## Audit -/
#print axioms MatedCRT.TargetLawTemplateEvent.isStandardBrownianLaw_map_complexPathToEuc
#print axioms MatedCRT.TargetLawTemplateEvent.measure_preimage_eucPathToComplex
#print axioms MatedCRT.TargetLawTemplateEvent.pathLaw_preimage_templateDisconnectionEvent
#print axioms MatedCRT.TargetLawTemplateEvent.one_sub_le_pathLaw_templateDisconnectionEvent
