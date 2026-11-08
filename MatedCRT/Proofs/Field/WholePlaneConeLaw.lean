import MatedCRT.Proofs.Field.WholePlaneConeLateral
import MatedCRT.Proofs.Field.WholePlaneLateralCov
import MatedCRT.Proofs.Measurability.ConePairing
import MatedCRT.Proofs.Field.GaussianLaw

/-!
# The circle averages of a quantum cone on region circles: Gaussian structure and independence (eq:gff)

For a cone field, the level-integral versions `Y_o` of the radial circle averages lie in one centred Gaussian space
(`cone_Y_global`); the vector of `Y_o` is independent of the vector of lateral circle averages (`cone_indep_vectors`,
from `IsQuantumCone.indep`), since `Y_o` is a.s. a measurable functional of the radial path (`circLevelFun_ae_eq`).
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric HarmonicBalls MarkovProcess
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {γ : ℝ}

/-- The observable of a region circle. -/
def circObs (o : RegIdx) : GFFObservable.Admissible := ⟨.circle o.1.1 o.1.2, o.2.1⟩

omit [IsProbabilityMeasure P] in
/-- A centred Gaussian element has mean zero. -/
lemma integral_eq_zero_of_mem_centred {M : Submodule ℝ (Ω → ℝ)} (hM : IsCentredGaussianSpace P M)
    {Z : Ω → ℝ} (hZ : Z ∈ M) : ∫ ω, Z ω ∂P = 0 := by
  obtain ⟨hmeas, v, hv⟩ := hM Z hZ
  have hint : ∫ x, x ∂(P.map Z) = ∫ ω, Z ω ∂P := integral_map hmeas.aemeasurable aestronglyMeasurable_id
  rw [← hint, hv, integral_id_gaussianReal]

/-- The cone's `Y` family: the level-integral versions of the radial circle averages in one centred Gaussian space. -/
theorem cone_Y_global (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    ∃ (Y : RegIdx → Ω → ℝ) (M : Submodule ℝ (Ω → ℝ)), IsCentredGaussianSpace P M ∧
      (∀ o, Measurable (Y o)) ∧ (∀ o, Y o ∈ M) ∧
      (∀ o, ∀ᵐ ω ∂P, Real.circleAverage (fun x => coneRadW γ (hcirc ω) (-Real.log ‖x‖)) o.1.2 o.1.1 = Y o ω) := by
  have hM₀ : IsCentredGaussianSpace P
      (Submodule.span ℝ (Set.range fun u : ℝ => fun ω => coneRadW γ (hcirc ω) u)) :=
    isCentredGaussianSpace_span (coneRadW_gaussian hcone hmc)
      (fun u => (hmc _ _ (Real.exp_pos _)).sub measurable_const) (fun u => coneRadW_mean hcone hmc u)
  obtain ⟨Y, M, hM, -, hYm, hYM, havg⟩ := radial_global_space (fun o : RegIdx => o.1.1)
    (fun o : RegIdx => o.1.2) (fun o => o.2) (coneRadW_radialData hcone hmc) hM₀
  exact ⟨Y, M, hM, hYm, hYM, havg⟩

omit [IsProbabilityMeasure P] in
/-- The vector of `Y`s on a finite family of circles is independent of the vector of lateral circle averages of
another (or the same) finite family of circles. -/
theorem cone_indep_vectors (hcone : IsQuantumCone γ P hC hcirc) {ι : Type*} [Finite ι] (oY oL : ι → RegIdx)
    (Y : ι → Ω → ℝ)
    (hY : ∀ i, ∀ᵐ ω ∂P, Real.circleAverage (fun x => coneRadW γ (hcirc ω) (-Real.log ‖x‖)) (oY i).1.2 (oY i).1.1
      = Y i ω)
    (hc : ∀ᵐ ω ∂P, Continuous fun u => coneRadW γ (hcirc ω) u) :
    IndepFun (fun ω (i : ι) => Y i ω) (fun ω (i : ι) => latCirc (hcirc ω) (oL i).1.1 (oL i).1.2) P := by
  have hYc : ∀ᵐ ω ∂P, ∀ i, Y i ω = circLevelFun γ (oY i) (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [circLevelFun_ae_eq (oY i) (hY i) hc] with ω hω
    exact hω.symm
  have hind := hcone.indep
  let F : ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → (ι → ℝ) := fun q i => circLevelFun γ (oY i) q.1
  let G : (GFFObservable.Admissible → ℝ) → (ι → ℝ) := fun l i => l (circObs (oL i))
  have hF : Measurable F := Measurable.of_eval fun i => (measurable_circLevelFun γ (oY i)).comp measurable_fst
  have hG : Measurable G := Measurable.of_eval fun i => measurable_pi_apply _
  have hcomp := hind.comp hF hG
  refine hcomp.congr ?_ ?_
  · filter_upwards [hYc] with ω hω
    funext i
    simp only [Function.comp_apply, F]
    exact (hω i).symm
  · exact Filter.Eventually.of_forall fun ω => rfl


omit [IsProbabilityMeasure P] in
/-- The covariance of the cone's lateral circle averages, through the lateral law and the whole-plane covariance. -/
theorem cone_cov_latCirc (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''} {hC'' : Ω'' → (ℂ → ℝ) → ℝ}
    {hcirc'' : Ω'' → ℝ → ℂ → ℝ} [IsProbabilityMeasure P'']
    (hwp'' : IsWholePlaneGFF P'' hC'' hcirc'')
    (hlaw : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)))
    (o o' : RegIdx) :
    covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2) P =
      wholePlaneGFFCov (.circle o.1.1 o.1.2) (.circle o'.1.1 o'.1.2) -
        Real.circleAverage (fun y => Real.circleAverage (fun x => min (-Real.log ‖y‖) (-Real.log ‖x‖)) o.1.2 o.1.1)
          o'.1.2 o'.1.1 := by
  have hae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    CirclePairing.aemeasurable_lateralProcess (fun φ hφ => hcone.measurable_pairing φ hφ) hmc hcont
  have hae'' : AEMeasurable (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)) P'' :=
    CirclePairing.aemeasurable_lateralProcess (fun φ hφ => hwp''.measurable_pairing φ hφ)
      (fun r z hr => hwp''.measurable_circle r z hr) hwp''.ae_continuousOn_circle
  have e1 : covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2) P =
      covariance (fun l : GFFObservable.Admissible → ℝ => l (circObs o))
        (fun l => l (circObs o')) (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))) := by
    rw [covariance_map (measurable_pi_apply (circObs o)).aestronglyMeasurable
      (measurable_pi_apply (circObs o')).aestronglyMeasurable hae]
    rfl
  have e2 : covariance (fun l : GFFObservable.Admissible → ℝ => l (circObs o))
      (fun l => l (circObs o')) (P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω))) =
      covariance (fun ω => latCirc (hcirc'' ω) o.1.1 o.1.2) (fun ω => latCirc (hcirc'' ω) o'.1.1 o'.1.2) P'' := by
    rw [covariance_map (measurable_pi_apply (circObs o)).aestronglyMeasurable
      (measurable_pi_apply (circObs o')).aestronglyMeasurable hae'']
    rfl
  rw [e1, hlaw, e2]
  exact cov_latCirc_latCirc hwp'' o.2 o'.2

omit [IsProbabilityMeasure P] in
/-- The whole-plane radial averages of a whole-plane GFF in one centred Gaussian space. -/
theorem wp_Y_global {Ω'' : Type*} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {hC'' : Ω'' → (ℂ → ℝ) → ℝ} {hcirc'' : Ω'' → ℝ → ℂ → ℝ} (hwp : IsWholePlaneGFF P'' hC'' hcirc'') :
    ∃ (Y : RegIdx → Ω'' → ℝ) (M : Submodule ℝ (Ω'' → ℝ)), IsCentredGaussianSpace P'' M ∧
      wpSpace hC'' hcirc'' ≤ M ∧ (∀ o, Measurable (Y o)) ∧ (∀ o, Y o ∈ M) ∧
      (∀ o : RegIdx, ∀ᵐ ω ∂P'', radAvg (hcirc'' ω) o.1.1 o.1.2 = Y o ω) := by
  obtain ⟨Y, M, hM, hle, hYm, hYM, havg⟩ := radial_global_space (fun o : RegIdx => o.1.1)
    (fun o : RegIdx => o.1.2) (fun o => o.2) (wp_radialData hwp) (wpSpace_gaussian hwp)
  refine ⟨Y, M, hM, hle, hYm, hYM, fun o => ?_⟩
  filter_upwards [havg o] with ω hω
  rw [radAvg_eq_wpRad o.2 (hcirc'' ω)]
  exact hω

omit [IsProbabilityMeasure P] in
/-- The lateral circle averages of a whole-plane GFF form a Gaussian process. -/
theorem wp_L_isGaussianProcess {Ω'' : Type*} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {hC'' : Ω'' → (ℂ → ℝ) → ℝ} {hcirc'' : Ω'' → ℝ → ℂ → ℝ} (hwp : IsWholePlaneGFF P'' hC'' hcirc'') :
    IsGaussianProcess (fun (o : RegIdx) (ω : Ω'') => latCirc (hcirc'' ω) o.1.1 o.1.2) P'' := by
  obtain ⟨Y, M, hM, hle, -, hYM, havg⟩ := wp_Y_global hwp
  have hX : ∀ o : RegIdx, (fun ω => hcirc'' ω o.1.1 o.1.2) ∈ M := fun o =>
    hle (Submodule.subset_span ⟨circObs o, rfl⟩)
  have hZ : IsGaussianProcess (fun (o : RegIdx) (ω : Ω'') => hcirc'' ω o.1.1 o.1.2 - Y o ω) P'' :=
    isGaussianProcess_of_isCentredGaussianSpace hM (fun o => Submodule.sub_mem M (hX o) (hYM o))
  refine ⟨fun I => ?_⟩
  refine (hZ.hasGaussianLaw I).congr ?_
  have hall : ∀ᵐ ω ∂P'', ∀ i : I, hcirc'' ω (i : RegIdx).1.1 (i : RegIdx).1.2 - Y (i : RegIdx) ω =
      latCirc (hcirc'' ω) (i : RegIdx).1.1 (i : RegIdx).1.2 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [havg (i : RegIdx)] with ω h
    unfold latCirc
    rw [h]
  filter_upwards [hall] with ω hω
  funext i
  exact hω i

omit [IsProbabilityMeasure P] in
/-- The vector of the cone's lateral circle averages is Gaussian (through the lateral law). -/
theorem cone_L_isGaussianProcess (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''} {hC'' : Ω'' → (ℂ → ℝ) → ℝ}
    {hcirc'' : Ω'' → ℝ → ℂ → ℝ} [IsProbabilityMeasure P'']
    (hwp'' : IsWholePlaneGFF P'' hC'' hcirc'')
    (hlaw : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω))) :
    IsGaussianProcess (fun (o : RegIdx) (ω : Ω) => latCirc (hcirc ω) o.1.1 o.1.2) P := by
  have hae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    CirclePairing.aemeasurable_lateralProcess (fun φ hφ => hcone.measurable_pairing φ hφ) hmc hcont
  have hae'' : AEMeasurable (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)) P'' :=
    CirclePairing.aemeasurable_lateralProcess (fun φ hφ => hwp''.measurable_pairing φ hφ)
      (fun r z hr => hwp''.measurable_circle r z hr) hwp''.ae_continuousOn_circle
  refine ⟨fun I => ?_⟩
  have hG : Measurable (fun l : GFFObservable.Admissible → ℝ => fun (i : I) => l (circObs (i : RegIdx))) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hGauss'' : HasGaussianLaw (fun ω (i : I) => latCirc (hcirc'' ω) (i : RegIdx).1.1 (i : RegIdx).1.2) P'' :=
    (wp_L_isGaussianProcess hwp'').hasGaussianLaw I
  have hmap : P.map (fun ω (i : I) => latCirc (hcirc ω) (i : RegIdx).1.1 (i : RegIdx).1.2) =
      P''.map (fun ω (i : I) => latCirc (hcirc'' ω) (i : RegIdx).1.1 (i : RegIdx).1.2) := by
    have e1 : (fun ω (i : I) => latCirc (hcirc ω) (i : RegIdx).1.1 (i : RegIdx).1.2) =
        (fun l : GFFObservable.Admissible → ℝ => fun (i : I) => l (circObs (i : RegIdx))) ∘
          (fun ω => lateralProcess (hC ω) (hcirc ω)) := rfl
    have e2 : (fun ω (i : I) => latCirc (hcirc'' ω) (i : RegIdx).1.1 (i : RegIdx).1.2) =
        (fun l : GFFObservable.Admissible → ℝ => fun (i : I) => l (circObs (i : RegIdx))) ∘
          (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)) := rfl
    rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hae,
      hlaw, AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hae'']
  exact hasGaussianLaw_of_map_eq (hG.comp_aemeasurable hae) hmap hGauss''

omit [IsProbabilityMeasure P] in
/-- The centred lateral circle average of the cone has mean zero. -/
theorem cone_L_integral_eq_zero (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''} {hC'' : Ω'' → (ℂ → ℝ) → ℝ}
    {hcirc'' : Ω'' → ℝ → ℂ → ℝ} [IsProbabilityMeasure P'']
    (hwp'' : IsWholePlaneGFF P'' hC'' hcirc'')
    (hlaw : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)))
    (o : RegIdx) : ∫ ω, latCirc (hcirc ω) o.1.1 o.1.2 ∂P = 0 := by
  have hae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    CirclePairing.aemeasurable_lateralProcess (fun φ hφ => hcone.measurable_pairing φ hφ) hmc hcont
  have hae'' : AEMeasurable (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)) P'' :=
    CirclePairing.aemeasurable_lateralProcess (fun φ hφ => hwp''.measurable_pairing φ hφ)
      (fun r z hr => hwp''.measurable_circle r z hr) hwp''.ae_continuousOn_circle
  have hev : Measurable (fun l : GFFObservable.Admissible → ℝ => l (circObs o)) := measurable_pi_apply _
  have h1 : ∫ ω, latCirc (hcirc ω) o.1.1 o.1.2 ∂P = ∫ l, l (circObs o) ∂(P.map (fun ω => lateralProcess (hC ω) (hcirc ω))) := by
    rw [integral_map hae hev.aestronglyMeasurable]
    rfl
  rw [h1, hlaw, integral_map hae'' hev.aestronglyMeasurable]
  -- the whole-plane lateral circle average has mean zero
  obtain ⟨Y, M, hM, hle, -, hYM, havg⟩ := wp_Y_global hwp''
  have hXint : Integrable (fun ω => hcirc'' ω o.1.1 o.1.2) P'' :=
    ((wpSpace_gaussian hwp'').memLp (Submodule.subset_span ⟨circObs o, rfl⟩)).integrable one_le_two
  have hYint : Integrable (Y o) P'' := ((hM.memLp (hYM o))).integrable one_le_two
  have hcongr : (fun ω => lateralProcess (hC'' ω) (hcirc'' ω) (circObs o)) =ᵐ[P''] fun ω => hcirc'' ω o.1.1 o.1.2 - Y o ω := by
    filter_upwards [havg o] with ω h
    show latCirc (hcirc'' ω) o.1.1 o.1.2 = _
    unfold latCirc
    rw [h]
  rw [integral_congr_ae hcongr, integral_sub hXint hYint]
  have hX0 : ∫ ω, hcirc'' ω o.1.1 o.1.2 ∂P'' = 0 := hwp''.integral_eq_zero (.circle o.1.1 o.1.2) o.2.1
  rw [hX0, integral_eq_zero_of_mem_centred hM (hYM o), sub_zero]

/-- The covariance of two radial level-integral versions of the cone (`S`, the double circle average). -/
theorem cone_cov_Y (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    {Y : RegIdx → Ω → ℝ}
    (hY : ∀ o : RegIdx, ∀ᵐ ω ∂P, Real.circleAverage (fun x => coneRadW γ (hcirc ω) (-Real.log ‖x‖)) o.1.2 o.1.1 =
      Y o ω) (o o' : RegIdx) :
    covariance (Y o) (Y o') P = Real.circleAverage
      (fun y => Real.circleAverage (fun x => min (-Real.log ‖y‖) (-Real.log ‖x‖)) o.1.2 o.1.1) o'.1.2 o'.1.1 := by
  have hM₀ : IsCentredGaussianSpace P
      (Submodule.span ℝ (Set.range fun u : ℝ => fun ω => coneRadW γ (hcirc ω) u)) :=
    isCentredGaussianSpace_span (coneRadW_gaussian hcone hmc)
      (fun u => (hmc _ _ (Real.exp_pos _)).sub measurable_const) (fun u => coneRadW_mean hcone hmc u)
  obtain ⟨Yt1, Yt2, hYt1m, hYt2m, hA, hA', hex⟩ :=
    radial_avg_cov_pair (coneRadW_radialData hcone hmc) hM₀ o'.2 o.2
  have hcov := hex.choose_spec.2.2.2.2.2.2.2.2
  have hYo' : Y o' =ᵐ[P] Yt1 := by
    filter_upwards [hY o', hA] with ω h1 h2
    exact h1.symm.trans h2
  have hYo : Y o =ᵐ[P] Yt2 := by
    filter_upwards [hY o, hA'] with ω h1 h2
    exact h1.symm.trans h2
  rw [covariance_congr_ae' hYo hYo', covariance_comm _ _]
  exact hcov

/-- **eq:gff at the circle level.** On the region circles, the circle averages of a quantum cone and of
`h^ℂ - γ log|·|` have the same law: `h_r(z) + γ log|z|` is a centred Gaussian process with the covariance of the
whole-plane GFF (lateral part plus radial level integral, independent). -/
theorem cone_circle_law (hcone : IsQuantumCone γ P hC hcirc)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''} {hC'' : Ω'' → (ℂ → ℝ) → ℝ}
    {hcirc'' : Ω'' → ℝ → ℂ → ℝ} [IsProbabilityMeasure P'']
    (hwp'' : IsWholePlaneGFF P'' hC'' hcirc'')
    (hlaw : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P''.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω)))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {hcirc' : Ω' → ℝ → ℂ → ℝ} (hwp' : IsWholePlaneGFF P' hC' hcirc') :
    P.map (fun ω (o : RegIdx) => hcirc ω o.1.1 o.1.2) =
      P'.map (fun ω (o : RegIdx) => HarmonicBalls.fieldCircleAverage γ (hcirc' ω) o.1.1 o.1.2) := by
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) :=
    hcone.ae_continuousOn_circle
  have hc : ∀ᵐ ω ∂P, Continuous fun u => coneRadW γ (hcirc ω) u :=
    (coneRadW_radialData hcone hmc).cont
  obtain ⟨Y, M, hMc, hYm, hYM, hY⟩ := cone_Y_global hcone hmc
  have hYg : IsGaussianProcess (fun (o : RegIdx) (ω : Ω) => Y o ω) P :=
    isGaussianProcess_of_isCentredGaussianSpace hMc hYM
  have hLg := cone_L_isGaussianProcess hcone hmc hcont hwp'' hlaw
  set C : RegIdx → Ω → ℝ := fun o ω => hcirc ω o.1.1 o.1.2 + γ * Real.log ‖o.1.2‖ with hCdef
  have hdec : ∀ o : RegIdx, ∀ᵐ ω ∂P, C o ω = latCirc (hcirc ω) o.1.1 o.1.2 + Y o ω := fun o => by
    filter_upwards [cone_circle_decomp o (hY o) hc] with ω h
    simp only [hCdef]
    linear_combination h
  have hLmem : ∀ o : RegIdx, MemLp (fun ω => latCirc (hcirc ω) o.1.1 o.1.2) 2 P := by
    intro o
    have h1 := ((hLg.hasGaussianLaw ({o} : Finset RegIdx)).map
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({o} : Finset RegIdx) => ℝ)
        ⟨o, Finset.mem_singleton_self o⟩)).memLp_two
    exact h1
  have hYmem : ∀ o : RegIdx, MemLp (Y o) 2 P := fun o => hMc.memLp (hYM o)
  have hindv : ∀ I : Finset RegIdx, IndepFun (fun ω (i : I) => Y i ω)
      (fun ω (i : I) => latCirc (hcirc ω) (i : RegIdx).1.1 (i : RegIdx).1.2) P := fun I =>
    cone_indep_vectors hcone (fun i : I => (i : RegIdx)) (fun i : I => (i : RegIdx))
      (fun i : I => Y i) (fun i => hY i) hc
  have hsc : ∀ o o' : RegIdx, IndepFun (fun ω => Y o ω) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2) P := by
    intro o o'
    have h := cone_indep_vectors hcone (fun _ : Unit => o) (fun _ : Unit => o') (fun _ : Unit => Y o)
      (fun _ => hY o) hc
    exact h.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  have hcovC : ∀ o o' : RegIdx, covariance (fun ω => C o ω) (fun ω => C o' ω) P =
      wholePlaneGFFCov (.circle o.1.1 o.1.2) (.circle o'.1.1 o'.1.2) := by
    intro o o'
    have e : covariance (fun ω => C o ω) (fun ω => C o' ω) P =
        covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2 + Y o ω)
          (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2 + Y o' ω) P :=
      covariance_congr_ae' (by filter_upwards [hdec o] with ω h using h)
        (by filter_upwards [hdec o'] with ω h using h)
    rw [e]
    have hL := hLmem o
    have hL' := hLmem o'
    have hY1 := hYmem o
    have hY2 := hYmem o'
    have hLY : covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2) (Y o') P = 0 :=
      (hsc o' o).symm.covariance_eq_zero hL hY2
    have hYL : covariance (Y o) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2) P = 0 :=
      (hsc o o').covariance_eq_zero hY1 hL'
    have hLL := cone_cov_latCirc hcone hmc hcont hwp'' hlaw o o'
    have hYY := cone_cov_Y hcone hmc hY o o'
    have h1 : covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2 + Y o ω)
        (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2 + Y o' ω) P =
        covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2)
          (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2 + Y o' ω) P +
        covariance (Y o) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2 + Y o' ω) P :=
      covariance_add_left hL hY1 (hL'.add hY2)
    have h2 : covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2)
        (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2 + Y o' ω) P =
        covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2) P +
        covariance (fun ω => latCirc (hcirc ω) o.1.1 o.1.2) (Y o') P :=
      covariance_add_right hL hL' hY2
    have h3 : covariance (Y o) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2 + Y o' ω) P =
        covariance (Y o) (fun ω => latCirc (hcirc ω) o'.1.1 o'.1.2) P + covariance (Y o) (Y o') P :=
      covariance_add_right hY1 hL' hY2
    rw [h1, h2, h3, hLY, hYL, hLL, hYY]
    ring
  have hCg : IsGaussianProcess (fun (o : RegIdx) (ω : Ω) => C o ω) P := by
    refine ⟨fun I => ?_⟩
    have hsum := iIndepFun.hasGaussianLaw_add (hLg.hasGaussianLaw I) (hYg.hasGaussianLaw I)
      (hindv I).symm
    refine hsum.congr ?_
    have hall : ∀ᵐ ω ∂P, ∀ i : I, C i ω = latCirc (hcirc ω) (i : RegIdx).1.1 (i : RegIdx).1.2 + Y i ω := by
      rw [ae_all_iff]
      intro i
      exact hdec i
    filter_upwards [hall] with ω hω
    funext i
    simp only [Pi.add_apply]
    exact (hω i).symm
  have hCmean : ∀ o : RegIdx, ∫ ω, C o ω ∂P = 0 := by
    intro o
    rw [integral_congr_ae (by filter_upwards [hdec o] with ω h using h)]
    rw [integral_add (MemLp.integrable one_le_two (hLmem o)) (MemLp.integrable one_le_two (hYmem o))]
    rw [cone_L_integral_eq_zero hcone hmc hcont hwp'' hlaw o, integral_eq_zero_of_mem_centred hMc (hYM o),
      add_zero]
  have hX' : IsGaussianProcess (fun (o : RegIdx) (ω : Ω') => hcirc' ω o.1.1 o.1.2) P' :=
    hwp'.isGaussianProcess.comp_right (fun o : RegIdx => circObs o)
  have hCm : ∀ o : RegIdx, Measurable (fun ω => C o ω) := fun o =>
    (hmc o.1.1 o.1.2 o.2.1).add_const _
  have hXm : ∀ o : RegIdx, Measurable (fun ω => hcirc' ω o.1.1 o.1.2) := fun o =>
    hwp'.measurable_circle o.1.1 o.1.2 o.2.1
  have hmapC := map_eq_of_covariance hCg hX' hCm hXm (fun o => by
      -- the centred cone process has mean zero
      exact hCmean o)
    (fun o => hwp'.integral_eq_zero (.circle o.1.1 o.1.2) o.2.1) (fun o o' => by
      rw [hcovC o o']
      exact (hwp'.covariance_eq (.circle o.1.1 o.1.2) (.circle o'.1.1 o'.1.2) o.2.1 o'.2.1).symm)
  have hF : Measurable (fun x : RegIdx → ℝ => fun o : RegIdx => x o + (-γ * Real.log ‖o.1.2‖)) :=
    Measurable.of_eval fun o => (measurable_pi_apply o).add_const _
  have hCvec : Measurable (fun ω (o : RegIdx) => C o ω) := Measurable.of_eval fun o => hCm o
  have hXvec : Measurable (fun ω (o : RegIdx) => hcirc' ω o.1.1 o.1.2) :=
    Measurable.of_eval fun o => hXm o
  have e1 : (fun ω (o : RegIdx) => hcirc ω o.1.1 o.1.2) =
      (fun x : RegIdx → ℝ => fun o : RegIdx => x o + (-γ * Real.log ‖o.1.2‖)) ∘
        (fun ω (o : RegIdx) => C o ω) := by
    funext ω o
    simp only [Function.comp_apply, hCdef]
    ring
  have e2 : (fun ω (o : RegIdx) => HarmonicBalls.fieldCircleAverage γ (hcirc' ω) o.1.1 o.1.2) =
      (fun x : RegIdx → ℝ => fun o : RegIdx => x o + (-γ * Real.log ‖o.1.2‖)) ∘
        (fun ω (o : RegIdx) => hcirc' ω o.1.1 o.1.2) := by
    funext ω o
    simp only [Function.comp_apply, HarmonicBalls.fieldCircleAverage]
    rw [circleAverage_log_norm_center o.2.1 o.2.2.1]
    ring
  rw [e1, e2, ← Measure.map_map hF hCvec, hmapC, Measure.map_map hF hXvec]

end Law

end MatedCRT.Field
