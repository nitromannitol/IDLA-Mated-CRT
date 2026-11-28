import MatedCRT.FirstPass.Derived.ConeConfigReconstructionCore
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionIdentity
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionCutoffs
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionMeasurable
import MatedCRT.FirstPass.Derived.ConeOffsetDensityProof

/-!
# Recovering the local configurations of the quantum cones from the outer data and the residues

The main theorem `coneConfigReconstruction_of_peanosphere` (hypotheses `hLG`, `hT`) proves
`ConeConfigReconstruction γ` (the third input of Lemma 3.3 of Gwynne–Miller–Sheffield, arXiv:1705.11161, for a
mating-of-trees coupling; the answer to MQ-sbl-18, section "Recovering the formal configuration") from the two named
inputs of the cell-side identity, `PlanarBMNoTwoSidedConePoints` (Le Gall) and
`CorrelatedBMPeanosphereTriplePointsNoContinuum` (the triple points of the Peanosphere curves of a correlated Brownian
pair), which identify the Brownian edge counts of the cells with the frontier-side multiplicities of the cells read off
the curve. `coneConfigReconstruction_of_literature` takes `CorrelatedBMTraversalTriplePointsNoContinuum`
(Duplantier–Miller–Sheffield, Gwynne–Holden–Miller) in place of the second input, through
`ae_forall_peanosphere_not_containsNondegenerateContinuum`.

The cutoffs come from `exists_cutoffs_reconCurveEvent`, the Borel maps are `coneRecon` (`measurable_coneRecon`). On the
curve event, almost surely, the local configuration of either cone is eventually equal to `coneRecon` of the outer data
and the residues (`eventually_localConfig_eq_coneRecon`), with the quantum-time curves `η = ηL ∘ φ` and `η₀ = ηL ∘ φ₀`
parametrized by the area measures of the two cones (`IsMatingOfTreesCoupling.areaParam`, `areaParam₀`); the
probabilities of the failure sets then tend to `0` (`tendsto_measure_of_ae_eventually_notMem`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open LatticeProb (CountablePhaseSpace measurableEmbedding_countablePhase_inject)

/-! ### Two general facts -/

/-- If almost every point eventually leaves the measurable sets `A n`, their measures tend to `0`. -/
theorem tendsto_measure_of_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : ℕ → Set Ω} (hA : ∀ n, NullMeasurableSet (A n) P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ A n) : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
  set Bs : ℕ → Set Ω := fun N => ⋃ n ≥ N, A n with hBs
  have hBm : ∀ N, NullMeasurableSet (Bs N) P := fun N =>
    NullMeasurableSet.biUnion (to_countable _) fun n _ => hA n
  have hanti : Antitone Bs := fun N N' hNN => biUnion_mono (fun n hn => le_trans hNN hn) fun _ _ => le_rfl
  have hnull : P (⋂ N, Bs N) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
    simp only [mem_iInter, hBs, mem_iUnion, exists_prop] at hω
    simp only [mem_ofPred_eq, eventually_atTop, not_exists, not_forall, not_not]
    intro N
    obtain ⟨n, hn, hωn⟩ := hω N
    exact ⟨n, hn, hωn⟩
  have hlim := tendsto_measure_iInter_atTop hBm hanti ⟨0, measure_ne_top P _⟩
  rw [hnull] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun N => measure_mono (subset_biUnion_of_mem (u := A) (le_refl N))

/-- Equality of local configurations is a measurable relation. -/
theorem measurableSet_localConfig_eq {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → LocalConfig}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {ω | f ω = g ω} := by
  have h1 : MeasurableSet {ω | (f ω).1 = (g ω).1} :=
    measurableSet_eq_fun hf.fst hg.fst
  have h2 : ∀ k, MeasurableSet {ω | (f ω).2.1 k = (g ω).2.1 k} := fun k =>
    measurableSet_eq_fun ((measurable_pi_apply k).comp hf.snd.fst) ((measurable_pi_apply k).comp hg.snd.fst)
  have h3 : ∀ k l, MeasurableSet {ω | (f ω).2.2 k l = (g ω).2.2 k l} := fun k l =>
    measurableSet_eq_fun ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp hf.snd.snd))
      ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp hg.snd.snd))
  have hset : {ω | f ω = g ω} = {ω | (f ω).1 = (g ω).1} ∩ (⋂ k, {ω | (f ω).2.1 k = (g ω).2.1 k}) ∩
      ⋂ k, ⋂ l, {ω | (f ω).2.2 k l = (g ω).2.2 k l} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h; rw [h]; exact ⟨⟨rfl, fun _ => rfl⟩, fun _ _ => rfl⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact Prod.ext h1 (Prod.ext (funext h2) (funext fun k => funext (h3 k)))
  rw [hset]
  exact (h1.inter (MeasurableSet.iInter h2)).inter (MeasurableSet.iInter fun k => MeasurableSet.iInter (h3 k))

/-- The set where a curve lies in a measurable set of curves and a measurable local configuration differs from an almost
everywhere measurable one is null measurable. -/
theorem nullMeasurableSet_mem_and_ne {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {c : Ω → C(ℝ, ℂ)}
    {E : Set C(ℝ, ℂ)} (hE : MeasurableSet E) (hc : Measurable c) {f g : Ω → LocalConfig} (hf : Measurable f)
    (hg : AEMeasurable g Q) : NullMeasurableSet {x | c x ∈ E ∧ f x ≠ g x} Q := by
  have hm : MeasurableSet {x | c x ∈ E ∧ f x ≠ hg.mk g x} :=
    (hc hE).inter (measurableSet_localConfig_eq hf hg.measurable_mk).compl
  refine hm.nullMeasurableSet.congr ?_
  filter_upwards [hg.ae_eq_mk] with x hx
  show (c x ∈ E ∧ f x ≠ hg.mk g x) = (c x ∈ E ∧ f x ≠ g x)
  rw [hx]

/-- The two offsets are almost everywhere measurable when the area measure is almost everywhere measurable and almost
surely finite on bounded sets and positive on open disks. -/
theorem aemeasurable_quantumTimeOffsets {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {e : Ω → C(ℝ, ℂ)}
    {μ : Ω → Measure ℂ} (he : Measurable e) (hμ : AEMeasurable μ P)
    (hgood : ∀ᵐ ω ∂P, OffsetGoodMeasure (μ ω)) (a : ℝ) :
    AEMeasurable (fun ω => quantumTimeOffsets (e ω) (μ ω) a) P := by
  have hZ : AEMeasurable (fun ω => (e ω, μ ω)) P := he.aemeasurable.prodMk hμ
  have hae : ∀ᵐ ω ∂P, offsetData a 1 2 (e ω, μ ω) =
      (annulusOuterData (e ω) (μ ω) 1 2, quantumTimeOffsets (e ω) (μ ω) a) := by
    filter_upwards [hgood] with ω hω
    have h1 := coverMass_eq isCompact_Icc (e ω) (J := Icc (-a) 0)
      ⟨1, one_pos, hω.measure_ne_top (isCompact_Icc.image (e ω).continuous).cthickening⟩
    have h2 := coverMass_eq isCompact_Icc (e ω) (J := Icc 0 a)
      ⟨1, one_pos, hω.measure_ne_top (isCompact_Icc.image (e ω).continuous).cthickening⟩
    simp only [offsetData, quantumTimeOffsets, h1, h2]
  refine ((measurable_snd.comp (measurable_offsetData a 1 2)).comp_aemeasurable hZ).congr ?_
  filter_upwards [hae] with ω hω
  show (offsetData a 1 2 (e ω, μ ω)).2 = _
  rw [hω]

/-- The outer data with the residues is almost everywhere measurable. -/
theorem aemeasurable_offsetResidues {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {e : Ω → C(ℝ, ℂ)}
    {μ : Ω → Measure ℂ} {θ : Ω → ℝ} (he : Measurable e) (hμ : AEMeasurable μ Q) (hθ : Measurable θ) {a : ℝ}
    (hC : AEMeasurable (fun x => quantumTimeOffsets (e x) (μ x) a) Q) (n : ℕ) (δ M : ℝ) :
    AEMeasurable (fun x => offsetResidues n (θ x) (e x) (μ x) a δ M) Q := by
  have hout : AEMeasurable (fun x => annulusOuterData (e x) (μ x) δ M) Q :=
    he.aemeasurable.prodMk
      ((measurable_restrict_of_measurableSet (measurableSet_offsetOuterAnnulus δ M)).comp_aemeasurable hμ)
  have hF : Measurable fun y : (Fin 2 → ℝ) × ℝ => fun i : Fin 2 => Int.fract ((n : ℝ) * y.1 i - y.2) :=
    measurable_pi_iff.2 fun i => measurable_fract.comp
      ((measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).sub measurable_snd)
  exact (measurableEmbedding_countablePhase_inject 2).measurable.comp_aemeasurable
    (hout.prodMk (hF.comp_aemeasurable (hC.prodMk hθ.aemeasurable)))

/-! ### The true data of the two cones -/

theorem vertexData_coneConfigData_eq_phaseData {Ω : Type} {η : Ω → C(ℝ, ℂ)} {bm : Ω → Path2} {n : ℕ} {ω : Ω}
    (hid : ∀ j k : ℤ, bmEdgeCount (1 / (n : ℝ)) (fun t => (bm ω t).1) (fun t => (bm ω t).2) j k =
      cellSideMult (1 / (n : ℝ)) (η ω) j k) :
    vertexData (1 / (n : ℝ)) (coneConfigData η bm n ω) = phaseData n 0 (η ω) := by
  refine Prod.ext (funext fun k => ?_) (funext fun j => funext fun k => ?_)
  · simp only [vertexData, coneConfigData, phaseData, vertexPoint, add_zero]
    congr 1
    ring
  · simp only [vertexData, coneConfigData, phaseData, zero_div, add_zero]
    exact hid j k

/-- The frontier-side multiplicities at unit mesh of the rescaled shifted curve are those at mesh `1/n` of the shifted
curve. -/
theorem cellSideMult_one_phaseShifted_meshRescale {n : ℕ} (hn : 0 < n) (θ : ℝ) (q : C(ℝ, ℂ)) (j k : ℤ) :
    cellSideMult 1 (phaseShiftedCurve 1 θ (GMS310Transfer.curveMeshRescale n q)) j k =
      cellSideMult (1 / (n : ℝ)) (fun t => q (t + θ / n)) j k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let τ : ℝ ≃o ℝ := OrderIso.mulLeft₀ (1 / (n : ℝ)) (one_div_pos.2 hn')
  have hτ : ∀ t, τ t = 1 / (n : ℝ) * t := fun t => rfl
  have hcomp : ⇑(phaseShiftedCurve 1 θ (GMS310Transfer.curveMeshRescale n q)) = (fun t => q (t + θ / n)) ∘ τ := by
    funext t
    simp only [phaseShiftedCurve, GMS310Transfer.curveMeshRescale, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      Function.comp_apply, hτ, one_mul]
    congr 1
    field_simp
  rw [hcomp]
  unfold cellSideMult
  have h1 : ¬ ((1 : ℝ) ≤ 0) := by norm_num
  have h2 : ¬ (1 / (n : ℝ) ≤ 0) := not_le.2 (one_div_pos.2 hn')
  simp only [h1, h2, false_or]
  split_ifs with h3 h4
  · rfl
  · rfl
  · rw [cellSideCount_comp_orderIso]
    simp only [hτ, one_mul]

theorem vertexData_zeroConeShiftedData_eq_phaseData {Ω : Type} {η₀ : Ω → C(ℝ, ℂ)} {G : Ω → Path2} {n : ℕ}
    (hn : 0 < n) {p : Ω × ℝ}
    (hid : ∀ j k : ℤ, phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1) j k =
      cellSideMult 1 (phaseShiftedCurve 1 p.2 (GMS310Transfer.curveMeshRescale n (η₀ p.1))) j k) :
    vertexData (1 / (n : ℝ)) (zeroConeShiftedData η₀ G n p) = phaseData n p.2 (η₀ p.1) := by
  refine Prod.ext (funext fun k => ?_) (funext fun j => funext fun k => ?_)
  · simp only [vertexData, zeroConeShiftedData, phaseData, vertexPoint, phaseShiftedCurve,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    congr 1
    ring
  · simp only [vertexData, zeroConeShiftedData, phaseData]
    rw [hid j k, cellSideMult_one_phaseShifted_meshRescale hn]

/-! ### The reconstruction -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely the curve of the `γ`-cone is the Lebesgue curve parametrized by the area measure of the `γ`-cone. -/
theorem ae_isMassParam_cone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (quantumConeArea γ γ X B B' ω) ∧
      ∃ φ : ℝ ≃o ℝ, IsMassParam (ηL ω) (η ω) φ (quantumConeArea γ γ X B B' ω) := by
  filter_upwards [D.areaParam, MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ] with
    ω hap hex
  obtain ⟨⟨φ, hφ0, hφ⟩, harea⟩ := hap
  have hv := MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex
  exact ⟨⟨fun K hK => hv.1 K hK⟩, φ, ⟨hφ0, hφ, harea _ hv⟩⟩

theorem ae_isMassParam_zeroCone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, IsFiniteMeasureOnCompacts (quantumConeArea γ 0 X₀ B₀ B₀' ω) ∧
      ∃ φ : ℝ ≃o ℝ, IsMassParam (ηL ω) (η₀ ω) φ (quantumConeArea γ 0 X₀ B₀ B₀' ω) := by
  filter_upwards [D.areaParam₀, MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ] with
    ω hap hex
  obtain ⟨⟨φ, hφ0, hφ⟩, harea⟩ := hap
  have hv := MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex
  exact ⟨⟨fun K hK => hv.1 K hK⟩, φ, ⟨hφ0, hφ, harea _ hv⟩⟩

theorem ae_offsetGoodMeasure_cone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : ∀ᵐ ω ∂P, OffsetGoodMeasure (quantumConeArea γ γ X B B' ω) := by
  filter_upwards [D.spaceFilling, D.areaParam,
    MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ] with ω hsf hap hex
  obtain ⟨⟨φ, -, hφ⟩, harea⟩ := hap
  exact offsetGoodMeasure_of_areaParam hsf.1
    (isProperMap_iff_tendsto_cocompact.2 ⟨(ηL ω).continuous, hsf.2.1⟩) hφ
    (harea _ (MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex))

theorem ae_offsetGoodMeasure_zeroCone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : ∀ᵐ ω ∂P, OffsetGoodMeasure (quantumConeArea γ 0 X₀ B₀ B₀' ω) := by
  filter_upwards [D.spaceFilling, D.areaParam₀,
    MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ] with ω hsf hap hex
  obtain ⟨⟨φ, -, hφ⟩, harea⟩ := hap
  exact offsetGoodMeasure_of_areaParam hsf.1
    (isProperMap_iff_tendsto_cocompact.2 ⟨(ηL ω).continuous, hsf.2.1⟩) hφ
    (harea _ (MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex))

end Coupling

/-- **Recovering the local configurations of the two quantum cones from the outer data and the residues**
(`ConeConfigReconstruction`, the third input of Lemma 3.3 of Gwynne–Miller–Sheffield, arXiv:1705.11161, for a
mating-of-trees coupling), from Le Gall's theorem on cone points (`PlanarBMNoTwoSidedConePoints`) and the absence of
continua among the triple points of the Peanosphere curves of a correlated Brownian pair
(`CorrelatedBMPeanosphereTriplePointsNoContinuum`). -/
theorem coneConfigReconstruction_of_peanosphere (hLG : PlanarBMNoTwoSidedConePoints)
    (hT : GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum) (γ : ℝ) :
    ConeConfigReconstruction γ := by
  intro Ω mΩ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D hγ G hG α R hα _hαR ε hε
  have hP := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hη : Measurable η := D.measurable_curves.2.1
  have hη₀ : Measurable η₀ := D.measurable_curves.2.2.1
  have hbm : Measurable bm := D.measurable_curves.2.2.2
  obtain ⟨a, L, δ, M, ha, haL, hδ, hδM, hEc⟩ := exists_cutoffs_reconCurveEvent (R := R) hηL
    (D.spaceFilling.mono fun _ h => h.2.2.1) (D.spaceFilling.mono fun _ h => h.2.1)
    (ae_eq_zero_of_curve_eq_zero D) hα hε
  have hV : MeasurableSet (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hEm := measurableSet_reconCurveEvent α R a L δ M
  have hAγ : AEMeasurable (quantumConeArea γ γ X B B') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMSCase.aemeasurable_coneField D hγ)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ)
  have hA0 : AEMeasurable (quantumConeArea γ 0 X₀ B₀ B₀') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMS4.aemeasurable_prop48ZeroConeField D)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ)
  have hCγ := aemeasurable_quantumTimeOffsets hηL hAγ (ae_offsetGoodMeasure_cone D hγ) a
  have hC0 := aemeasurable_quantumTimeOffsets hηL hA0 (ae_offsetGoodMeasure_zeroCone D hγ) a
  have hqmp : Measure.QuasiMeasurePreserving Prod.fst (P.prod zeroConePhase) P :=
    Measure.quasiMeasurePreserving_fst
  refine ⟨a, δ, M, ReconCurveEvent α R a L δ M, coneRecon α R a L M, ha, hδ, hδM, hEm, hEc,
    fun n => measurable_coneRecon α R a L M n, ?_, ?_⟩
  · -- the `γ`-cone, phase `0`
    refine tendsto_measure_of_ae_eventually_notMem (fun n => nullMeasurableSet_mem_and_ne hEm hηL
      ((measurable_localConfig hV).comp ((measurable_vertexData _).comp (measurable_coneConfigData hη hbm n)))
      ((measurable_coneRecon α R a L M n).comp_aemeasurable
        (aemeasurable_offsetResidues hηL hAγ measurable_const hCγ n δ M))) ?_
    filter_upwards [ae_bmEdgeCount_eq_cellSideMult_cone hLG hT D hγ, ae_isMassParam_cone D hγ] with ω hid hmp
    obtain ⟨hfin, φ, hp⟩ := hmp
    by_cases hE : ηL ω ∈ ReconCurveEvent α R a L δ M
    · filter_upwards [eventually_localConfig_eq_coneRecon hα ha haL hδ hp hE 0, eventually_gt_atTop 0]
        with n hn hn0
      rintro ⟨-, hne⟩
      rw [vertexData_coneConfigData_eq_phaseData (hid n hn0)] at hne
      exact hne hn
    · exact Eventually.of_forall fun n hn => hE hn.1
  · -- the `0`-cone, uniform phase
    refine tendsto_measure_of_ae_eventually_notMem (fun n => nullMeasurableSet_mem_and_ne hEm
      (hηL.comp measurable_fst)
      ((measurable_localConfig hV).comp ((measurable_vertexData _).comp
        (measurable_zeroConeShiftedData hη₀ hG.1 n)))
      ((measurable_coneRecon α R a L M n).comp_aemeasurable
        (aemeasurable_offsetResidues (hηL.comp measurable_fst) (aemeasurable_comp_fst_prod hA0) measurable_snd
          (aemeasurable_comp_fst_prod hC0) n δ M))) ?_
    have hid : ∀ᵐ p ∂P.prod zeroConePhase, ∀ n : ℕ, 0 < n → ∀ j k : ℤ,
        phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1) j k =
          cellSideMult 1 (phaseShiftedCurve 1 p.2 (GMS310Transfer.curveMeshRescale n (η₀ p.1))) j k := by
      refine ae_all_iff.2 fun n => ?_
      by_cases hn : 0 < n
      · filter_upwards [ae_phaseShiftedEdgeCount_eq_cellSideMult hLG hT D hγ G hG n hn] with p hp _ using hp
      · exact Eventually.of_forall fun p hn' => absurd hn' hn
    filter_upwards [hid, hqmp.ae (ae_isMassParam_zeroCone D hγ)] with p hidp hmp
    obtain ⟨hfin, φ, hp⟩ := hmp
    by_cases hE : ηL p.1 ∈ ReconCurveEvent α R a L δ M
    · filter_upwards [eventually_localConfig_eq_coneRecon hα ha haL hδ hp hE p.2, eventually_gt_atTop 0]
        with n hn hn0
      rintro ⟨-, hne⟩
      rw [vertexData_zeroConeShiftedData_eq_phaseData hn0 (hidp n hn0)] at hne
      exact hne hn
    · exact Eventually.of_forall fun n hn => hE hn.1

/-- **`ConeConfigReconstruction` from the two named literature inputs** `PlanarBMNoTwoSidedConePoints` (Le Gall) and
`CorrelatedBMTraversalTriplePointsNoContinuum` (Duplantier–Miller–Sheffield, Gwynne–Holden–Miller); the second gives
the Peanosphere form by `ae_forall_peanosphere_not_containsNondegenerateContinuum`. -/
theorem coneConfigReconstruction_of_literature (hLG : PlanarBMNoTwoSidedConePoints)
    (hA : CorrelatedBMTraversalTriplePointsNoContinuum) (γ : ℝ) : ConeConfigReconstruction γ :=
  coneConfigReconstruction_of_peanosphere hLG
    (fun _ h0 h2 _ hμ => ae_forall_peanosphere_not_containsNondegenerateContinuum hA h0 h2 hμ) γ

end MatedCRT
