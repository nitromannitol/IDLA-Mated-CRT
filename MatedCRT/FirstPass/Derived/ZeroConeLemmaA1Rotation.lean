import MatedCRT.FirstPass.Derived.ZeroConeAreaCoordinateChangeProof
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhaseCone

/-!
# Rotation invariance of the circle-average embedding of the `0`-quantum cone and of its area measure

The circle-average embedding `h = zeroConeFieldOf γ X₀ b b'` of the `0`-quantum cone built from a whole-plane GFF
`X₀` and two independent standard Brownian motions `b`, `b'`, independent of `X₀`, is rotation invariant in law, and
its area measure rotates with it. The statements of the coupling `p48o_*` of `GMS4O/Prop48OPhaseCone.lean` only use
these data (the whole-plane GFF, the two Brownian motions and their independence), so we restate them for general
data, without a mating-of-trees coupling.

## Main statements

* `map_rotateField_zeroConeFieldOf`: the law of `h(e^{iθ} ·)` is the law of `h`.
* `ae_areaMap_rotateField`: almost surely, the area map of `h(e^{iθ} ·)` is the image of the area map of `h` under
  `w ↦ e^{-iθ} w`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4O
open scoped NNReal ENNReal

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X₀ : Ω → Field} {b b' : ℝ≥0 → Ω → ℝ}

/-- The radial path of the `0`-quantum cone as a measurable continuous path `W`, independent of `X₀`, with almost
surely locally integrable radial profile. -/
theorem exists_zeroCone_radialPath [IsProbabilityMeasure P] (hγ : 0 < γ)
    (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P)
    (hXB : IndepFun X₀ (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P)
    (hbb : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧ IndepFun X₀ W P ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ 0 (fun s => b s ω) (fun s => b' s ω) t) ∧
      (∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume) := by
  have hQ0 : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ
  have hQ0' : 0 < CellScaling.lqgQ γ - 0 := by rw [sub_zero]; exact hQ0
  obtain ⟨W, hWm, hXW, -, hW⟩ := IGLaw.exists_radialPath_alpha (γ := γ) (α := 0) hQ0' hb hb' hXB
    (indepFun_const_left (μ := P) (c := ()) _)
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  have hA : MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ 0 (fun s => b s ω) (fun s => b' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial hb hb' hbb
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume := by
    filter_upwards [hW, MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω hl
    refine hl.congr (Eventually.of_forall fun z => ?_)
    simp only [ConeScaling.radialOf, hω, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  exact ⟨W, hWm, hXW, hW, hli⟩

/-- **The law of the circle-average embedding of the `0`-quantum cone is rotation invariant**, for the cone field
with the `CellScaling` copies of the frozen definitions. -/
theorem map_rotateField_p48oZeroConeField [IsProbabilityMeasure P] (hγ : 0 < γ)
    (hX : LQGMetric.IsWholePlaneGFF X₀ P) (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P)
    (hXB : IndepFun X₀ (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P)
    (hbb : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P) (θ : ℝ) :
    P.map (fun ω => MoTPort.rotateField θ (p48oZeroConeField γ X₀ b b' ω)) =
      P.map (p48oZeroConeField γ X₀ b b') := by
  obtain ⟨W, hWm, hXW, hW, hli⟩ := exists_zeroCone_radialPath hγ hb hb' hXB hbb
  have hL : Measurable fun ω => CellScaling.lateralPart (X₀ ω) :=
    ConeScaling.measurable_lateralPart.comp hX.measurable
  have hRL : Measurable fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)) :=
    (MoTPort.measurable_rotateField θ).comp hL
  have hindL : IndepFun (fun ω => CellScaling.lateralPart (X₀ ω)) W P :=
    hXW.comp ConeScaling.measurable_lateralPart measurable_id
  have hindRL : IndepFun (fun ω => MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω))) W P :=
    hXW.comp ((MoTPort.measurable_rotateField θ).comp ConeScaling.measurable_lateralPart)
      measurable_id
  have hpair : P.map (fun ω => (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)), W ω)) =
      P.map (fun ω => (CellScaling.lateralPart (X₀ ω), W ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hRL.aemeasurable hWm.aemeasurable).1 hindRL,
      (indepFun_iff_map_prod_eq_prod_map_map hL.aemeasurable hWm.aemeasurable).1 hindL,
      p48o_map_rotateField_lateralPart hX θ]
  have hfield : (fun ω => MoTPort.rotateField θ (p48oZeroConeField γ X₀ b b' ω)) =ᵐ[P]
      fun ω => ConeScaling.fieldOf (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω))) (W ω) := by
    filter_upwards [hW, hli] with ω hω hl
    rw [p48oZeroConeField, IGLaw.coneField_eq_fieldOf_alpha γ 0 (X₀ ω) hω, ConeScaling.fieldOf,
      ConeScaling.fieldOf, p48o_rotateField_add,
      p48o_rotateField_ofFunC_of_radial hl (fun z w hzw => by simp [ConeScaling.radialOf, hzw])]
  have hpRL : AEMeasurable
      (fun ω => (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)), W ω)) P :=
    (hRL.prodMk hWm).aemeasurable
  have hpL : AEMeasurable (fun ω => (CellScaling.lateralPart (X₀ ω), W ω)) P :=
    (hL.prodMk hWm).aemeasurable
  rw [Measure.map_congr hfield, Measure.map_congr (p48o_zeroCone_ae_eq_fieldOf hW)]
  change P.map ((fun p : LQGMetric.DistC × C(ℝ, ℝ) => ConeScaling.fieldOf p.1 p.2) ∘
      fun ω => (MoTPort.rotateField θ (CellScaling.lateralPart (X₀ ω)), W ω)) =
    P.map ((fun p : LQGMetric.DistC × C(ℝ, ℝ) => ConeScaling.fieldOf p.1 p.2) ∘
      fun ω => (CellScaling.lateralPart (X₀ ω), W ω))
  rw [← AEMeasurable.map_map_of_aemeasurable ConeScaling.measurable_fieldOf.aemeasurable hpRL,
    ← AEMeasurable.map_map_of_aemeasurable ConeScaling.measurable_fieldOf.aemeasurable hpL, hpair]

/-- **Circle-average covariance of the rotated `0`-quantum cone**, on one almost sure event for all positive radii
and all centres off the circle through the cone point. -/
theorem ae_circleAvg_rotateField_p48oZeroConeField [IsProbabilityMeasure P] (hγ : 0 < γ)
    (hX : LQGMetric.IsWholePlaneGFF X₀ P) (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P)
    (θ : ℝ) :
    ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ, ‖w‖ ≠ ρ →
      LQGMetric.circleAvg (MoTPort.rotateField θ (p48oZeroConeField γ X₀ b b' ω)) ρ w =
        LQGMetric.circleAvg (p48oZeroConeField γ X₀ b b' ω) ρ (p48oRot θ w) := by
  have hαQ : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ
  have hRX : LQGMetric.IsWholePlaneGFF (fun ω => MoTPort.rotateField θ (X₀ ω)) P :=
    IGLaw.IsWholePlaneGFF.rotateField hX θ
  filter_upwards [LQGCoord.ae_radialGood hX hb hb' hαQ,
    LQGCoord.ae_tendsto_mollAvgS_circleAvg hX,
    LQGCoord.ae_tendsto_mollAvgS_circleAvg hRX,
    IGLaw.rotCircleAvgCovarianceAll_holds P X₀ hX θ] with ω hr hXω hRXω hcov
  intro ρ hρ w hw
  set g₁ : ℂ → ℝ := CellScaling.radialAvg (X₀ ω)
  set g₂ : ℂ → ℝ := LQGCoord.coneProfile γ 0 (fun t => b t ω) (fun t => b' t ω)
  have hc₁ : ContinuousOn g₁ {0}ᶜ := LQGCoord.continuousOn_radialAvg hr.good
  have hc₂ : ContinuousOn g₂ {0}ᶜ := LQGCoord.continuousOn_coneProfile hr
  obtain ⟨C₁, hC₁⟩ := LQGCoord.abs_radialAvg_le hr one_pos
  obtain ⟨C₂, hC₂⟩ := LQGCoord.abs_coneProfile_le hr one_pos
  have hl₁ : LocallyIntegrable g₁ volume :=
    LQGCoord.locallyIntegrable_of_logBound (LQGCoord.measurable_radialAvg _) hc₁ hC₁
  have hl₂ : LocallyIntegrable g₂ volume :=
    LQGCoord.locallyIntegrable_of_logBound (LQGCoord.measurable_coneProfile hr) hc₂
      fun w h0 h1 => (hC₂ w h0 h1).1
  have hrad₁ : ∀ z w : ℂ, ‖z‖ = ‖w‖ → g₁ z = g₁ w := by
    intro z w hzw
    simp only [g₁, CellScaling.radialAvg, hzw]
  have hrad₂ : ∀ z w : ℂ, ‖z‖ = ‖w‖ → g₂ z = g₂ w := by
    intro z w hzw
    simp only [g₂, LQGCoord.coneProfile, hzw]
  have hdec : p48oZeroConeField γ X₀ b b' ω = X₀ ω - CellScaling.ofFunC g₁ + CellScaling.ofFunC g₂ :=
    LQGCoord.coneField_eq_cone γ 0 (X₀ ω) (fun t => b t ω) (fun t => b' t ω)
  have hdecR : MoTPort.rotateField θ (p48oZeroConeField γ X₀ b b' ω) =
      MoTPort.rotateField θ (X₀ ω) - CellScaling.ofFunC g₁ + CellScaling.ofFunC g₂ := by
    rw [hdec, p48o_rotateField_add, p48o_rotateField_sub,
      p48o_rotateField_ofFunC_of_radial hl₁ hrad₁, p48o_rotateField_ofFunC_of_radial hl₂ hrad₂]
  have hwR : ‖p48oRot θ w‖ ≠ ρ := by
    rwa [LinearIsometryEquiv.norm_map]
  rw [hdecR, LQGCoord.circleAvg_cone hl₁ hl₂ hc₁ hc₂ hρ hw (hRXω.2 ρ hρ w), hdec,
    LQGCoord.circleAvg_cone hl₁ hl₂ hc₁ hc₂ hρ hwR (hXω.2 ρ hρ (p48oRot θ w)),
    hcov ρ hρ w, p48oRot_apply, ← p48oRot_apply,
    p48o_circleAverage_rot_of_radial hrad₁, p48o_circleAverage_rot_of_radial hrad₂]

/-- The set of parameters whose section of a measurable set is almost surely full is measurable. -/
theorem measurableSet_ae_prodMk {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure β}
    [SFinite ν] {S : Set (α × β)} (hS : MeasurableSet S) :
    MeasurableSet {x : α | ∀ᵐ y ∂ν, (x, y) ∈ S} := by
  have hm := measurable_measure_prodMk_left (ν := ν) hS.compl
  have e : {x : α | ∀ᵐ y ∂ν, (x, y) ∈ S} = (fun x : α => ν (Prod.mk x ⁻¹' Sᶜ)) ⁻¹' {0} :=
    Set.ext fun x => ae_iff
  rw [e]
  exact hm (measurableSet_singleton 0)

/-- The event that the dyadic-scale circle averages of the rotated field are those of the field read in rotated
coordinates, for almost every centre, is measurable. -/
theorem measurableSet_ae_circleAvg_rotateField (θ s : ℝ) :
    MeasurableSet {h : LQGMetric.DistC | ∀ᵐ z : ℂ,
      LQGMetric.circleAvg (MoTPort.rotateField θ h) s z = LQGMetric.circleAvg h s (p48oRot θ z)} := by
  have hf1 : Measurable fun p : LQGMetric.DistC × ℂ => (MoTPort.rotateField θ p.1, s, p.2) :=
    ((MoTPort.measurable_rotateField θ).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
  have hf2 : Measurable fun p : LQGMetric.DistC × ℂ => (p.1, s, p48oRot θ p.2) :=
    measurable_fst.prodMk (measurable_const.prodMk ((measurable_p48oRot θ).comp measurable_snd))
  have h1 := LQGMetric.measurable_circleAvg.comp hf1
  have h2 := LQGMetric.measurable_circleAvg.comp hf2
  exact measurableSet_ae_prodMk (ν := (volume : Measure ℂ)) (measurableSet_eq_fun h1 h2)

variable (θ : ℝ)

/-- **The law of the circle-average embedding of the `0`-quantum cone is rotation invariant**: the law of
`h(e^{iθ} ·)` is the law of `h` (the cone field is `zeroConeFieldOf γ X₀ b b'`; the rotation of fields is
`MoTPort.rotateField`). -/
theorem map_rotateField_zeroConeFieldOf [IsProbabilityMeasure P] (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hX : LQGMetric.IsWholePlaneGFF X₀ P) (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P)
    (hXB : IndepFun X₀ (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P)
    (hbb : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P) :
    (P.map (zeroConeFieldOf γ X₀ b b')).map (MoTPort.rotateField θ) =
      P.map (zeroConeFieldOf γ X₀ b b') := by
  have hQ : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ.1
  have hfm : AEMeasurable (zeroConeFieldOf γ X₀ b b') P :=
    ConeAreaCovariance.aemeasurable_coneField_alpha hQ hX hb hb'
  rw [AEMeasurable.map_map_of_aemeasurable (MoTPort.measurable_rotateField θ).aemeasurable hfm]
  exact map_rotateField_p48oZeroConeField hγ.1 hX hb hb' hXB hbb θ

/-- **The area map of the rotated `0`-quantum cone is the rotated area map**: almost surely for the law of the
circle-average embedding `h` of the `0`-quantum cone, `areaMap (h(e^{iθ} ·)) = (areaMap h) ∘ (w ↦ e^{iθ} w)`, that is,
the image of `areaMap h` under `w ↦ e^{-iθ} w` (`p48oRot (-θ)`). -/
theorem ae_areaMap_rotateField [IsProbabilityMeasure P] (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hX : LQGMetric.IsWholePlaneGFF X₀ P) (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P)
    (hXB : IndepFun X₀ (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P)
    (hbb : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P) :
    ∀ᵐ h ∂(P.map (zeroConeFieldOf γ X₀ b b')),
      ConeAreaCovariance.areaMap γ (MoTPort.rotateField θ h) =
        (ConeAreaCovariance.areaMap γ h).map (p48oRot (-θ)) := by
  have hQ : (0 : ℝ) < CellScaling.lqgQ γ := p48o_lqgQ_pos hγ.1
  have hfm : AEMeasurable (zeroConeFieldOf γ X₀ b b') P :=
    ConeAreaCovariance.aemeasurable_coneField_alpha hQ hX hb hb'
  have hrfm : AEMeasurable (fun ω => MoTPort.rotateField θ (zeroConeFieldOf γ X₀ b b' ω)) P :=
    (MoTPort.measurable_rotateField θ).comp_aemeasurable hfm
  set G : Set LQGMetric.DistC := (ConeAreaCovariance.goodSet γ ∩
      MoTPort.rotateField θ ⁻¹' ConeAreaCovariance.goodSet γ) ∩
    ⋂ k : ℕ, {h : LQGMetric.DistC | ∀ᵐ z : ℂ, LQGMetric.circleAvg (MoTPort.rotateField θ h)
      (dyadicScale k) z = LQGMetric.circleAvg h (dyadicScale k) (p48oRot θ z)} with hG
  have hGm : MeasurableSet G :=
    ((ConeAreaCovariance.measurableSet_goodSet γ).inter
      ((MoTPort.measurable_rotateField θ) (ConeAreaCovariance.measurableSet_goodSet γ))).inter
      (MeasurableSet.iInter fun k => measurableSet_ae_circleAvg_rotateField θ (dyadicScale k))
  have hgood : ∀ᵐ ω ∂P, zeroConeFieldOf γ X₀ b b' ω ∈ ConeAreaCovariance.goodSet γ :=
    ConeAreaCovariance.ae_coneField_mem_goodSet hγ.1 hγ.2 hQ hX hb hb'
  have hgoodmap : ∀ᵐ h ∂(P.map (zeroConeFieldOf γ X₀ b b')), h ∈ ConeAreaCovariance.goodSet γ :=
    (ae_map_iff hfm (ConeAreaCovariance.measurableSet_goodSet γ)).2 hgood
  have hrgood : ∀ᵐ ω ∂P, MoTPort.rotateField θ (zeroConeFieldOf γ X₀ b b' ω) ∈
      ConeAreaCovariance.goodSet γ := by
    refine ae_of_ae_map hrfm ?_
    have hmap : P.map (fun ω => MoTPort.rotateField θ (zeroConeFieldOf γ X₀ b b' ω)) =
        P.map (zeroConeFieldOf γ X₀ b b') :=
      map_rotateField_p48oZeroConeField hγ.1 hX hb hb' hXB hbb θ
    rw [hmap]
    exact hgoodmap
  have hcirc := ae_circleAvg_rotateField_p48oZeroConeField hγ.1 hX hb hb' θ
  have hae : ∀ᵐ ω ∂P, zeroConeFieldOf γ X₀ b b' ω ∈ G := by
    filter_upwards [hgood, hrgood, hcirc] with ω h1 h2 h3
    refine ⟨⟨h1, h2⟩, mem_iInter.2 fun k => ?_⟩
    filter_upwards [LQGCoord.ae_norm_ne (dyadicScale k)] with z hz
    exact h3 _ (LQGCoord.dyadicScale_pos k) z hz
  filter_upwards [(ae_map_iff hfm hGm).2 hae] with h hh
  obtain ⟨⟨hg, hrg⟩, hcov⟩ := hh
  have hv := (ConeAreaCovariance.areaMap_spec hγ.1.ne' hg).1
  have hv' := p48o_isVagueLimitC_rot (γ := γ) θ (fun k => mem_iInter.1 hcov k) hv
  exact LQGCoord.isVagueLimitC_unique (ConeAreaCovariance.areaMap_spec hγ.1.ne' hrg).1 hv'

end ZeroCone

end MatedCRT
