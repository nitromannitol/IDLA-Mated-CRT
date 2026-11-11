import MatedCRT.Proofs.Sec4.Prop42Closure.HalfBallClosure
import MatedCRT.Proofs.Sec4.Prop42Closure.HalfBallPremature
import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauAE
import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauRadii
import MatedCRT.Proofs.Sec4.Prop42Closure.RestrictionLocality
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeVolumeGrowth
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneRestrictedLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureLocalityProof

/-! # The premature-contact event is null for the cone (closure of Proposition 4.2)

Target `ConePrematureContactNullStep` (`HalfBallClosure.lean:59`).
Let `E` be the measurable set of measures with premature half-ball contact of the raw `3/4`-clusters
(`exists_measurable_halfBallPrematureContact`, `ContactEvent.lean:11`). The argument is:

* (A) on the cone, almost surely `μ ∈ E` iff the raw clusters of `μ` have premature contact (volume growth, B1 cone);
* (B) restriction to `B_1` does not change the event (`halfBallPrematureContact_restrict_iff`, `volumeGrowth_restrict_ball_one`);
* (C) fact (2) for the restricted LQG measures transfers `P[μ|_{B_1} ∈ E]` to the whole-plane model (`IdentDistrib.measure_mem_eq`);
* (D) on the whole plane, the premature event is null: almost surely it forces the half-plateau `1/2` of the chosen global
  family (`plateau_of_prematureContact`, with monotonicity, compatibility `ClusterStrongCompatibilityStmt` and openness),
  and the plateau probabilities vanish (`plateau_measure_zero_of_ae_radii_family`, fact (1), radii a.e. measurable).

Named inputs: `VolumeGrowthStmt` (IDLA Lemma 2.7), `WholePlaneVolumeGrowthAeStep` (B1, whole plane),
`WholePlaneLQGModelStep` (B2) and `ConeWholePlaneFieldLawStep` (fact (2) for the fields). The locality input (A),
`LQGMeasureLocalityFunctionalStep`, is proved: `LQGMeasureLocalityFunctionalStep_proof` (`LQGMeasureLocalityProof.lean`). The reduced-input consumers `conePrematureContactNullStep_of_fieldLaw` and
`coneHalfBallClosureInsideStep_of_fieldLaw` (end of this file) supply it internally; fact (2) for the restricted LQG measures
(gap G1) comes through `coneWholePlaneRestrictedLQGLawStep_of_inputs`, whose reduced form is
`coneWholePlaneRestrictedLQGLawStep_of_fieldLaw` (`ConeWholePlaneRestrictedLaw.lean`). The `_of_inputs` versions keep (A)
as a hypothesis, for compatibility.

`PlateauScaleInvarianceStep` (fact (1)), `HarmonicBallLocalSetStmt`, `ExistenceHarmonicBallsStmt` and
`ClusterStrongCompatibilityStmt` (Harmonic-Balls Thm 5.5 and Lemma 5.8; two components of `HarmonicBallsDraftInputs`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory

/-- The almost sure local finiteness of the LQG measure of a whole-plane field (from `IsLQGMeasureOfField`). -/
theorem ae_isLocallyFiniteMeasure_of_isLQGMeasureOfField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (h : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
  have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := h
  filter_upwards [hL] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- `γ < Q = 2/γ + γ/2` for `0 < γ < 2` (the insertion `γ` is below the LQG threshold). -/
theorem self_lt_lqgQ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have hγ0 : γ ≠ 0 := hγ.ne'
  have h1 : 2 / γ + γ / 2 - γ = (4 - γ * γ) / (2 * γ) := by
    field_simp
    ring
  have h2 : 0 < (4 - γ * γ) / (2 * γ) := div_pos (by nlinarith) (by positivity)
  linarith

/-- A measurable choice of a regularized cluster family at every centre, almost surely (choice from a.s. existence). -/
theorem exists_regularized_choice {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (h : ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ Λ : ℝ → Set ℂ, IsRegularizedClusterFamily (μ ω) Λ z) :
    ∃ Λhat : Ω → ℂ → ℝ → Set ℂ, ∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z := by
  refine ⟨fun ω z => Classical.epsilon (fun Λ : ℝ → Set ℂ => IsRegularizedClusterFamily (μ ω) Λ z), ?_⟩
  filter_upwards [h] with ω hω z
  exact Classical.epsilon_spec (hω z)

/-- Step (A)-(B): for a measure with volume growth at radius `3/4` (and local finiteness), the event `E` of `ν` and of its
restriction to `B_1` agree with premature contact, hence with each other. -/
theorem restrict_mem_iff_premature {ν : Measure ℂ} (hl : IsLocallyFiniteMeasure ν) {βm βp : ℝ}
    (hV : VolumeGrowth ν (3 / 4) βm βp) {E : Set (Measure ℂ)}
    (hE : ∀ ν' : Measure ℂ, IsLocallyFiniteMeasure ν' → (∃ βm βp : ℝ, VolumeGrowth ν' (3 / 4) βm βp) →
      (ν' ∈ E ↔ halfBallPrematureContact (fun t : Ioi (0 : ℝ) => interior (closure (cluster ν' (3 / 4) 0 t))))) :
    ν ∈ E ↔ ν.restrict (ball (0 : ℂ) 1) ∈ E := by
  have : IsLocallyFiniteMeasure ν := hl
  have h1 := hE ν hl ⟨βm, βp, hV⟩
  have h2 := hE (ν.restrict (ball (0 : ℂ) 1)) (isLocallyFiniteMeasure_restrict_ball_one ν)
    ⟨βm, βp, volumeGrowth_restrict_ball_one hV⟩
  rw [h1, h2, halfBallPrematureContact_restrict_iff]

/-- **Step (D), whole plane.** The premature-contact event of the whole-plane LQG measure is null. -/
theorem wholePlane_premature_null (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hfact1 : PlateauScaleInvarianceStep)
    (hVGw : WholePlaneVolumeGrowthAeStep) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    {μ' : Ω' → Measure ℂ} (hGFF' : IsWholePlaneGFF P' hC' hcirc') (hLQG' : IsLQGMeasureOfField P' γ γ hcirc' μ') :
    P' {ω | halfBallPrematureContact (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ' ω) (3 / 4) 0 t)))} = 0 := by
  have hα : γ < lqgQ γ := self_lt_lqgQ hγ hγ2
  have hEx' : ∀ᵐ ω ∂P', ∀ z : ℂ, ∃ Λ : ℝ → Set ℂ, IsRegularizedClusterFamily (μ' ω) Λ z :=
    hEx γ γ hγ hγ2 hα Ω' P' hC' hcirc' μ' hGFF' hLQG'
  obtain ⟨Λhat, hΛhat⟩ := exists_regularized_choice hEx'
  have hΛ0 : ∀ᵐ ω ∂P', IsRegularizedClusterFamily (μ' ω) (Λhat ω 0) 0 :=
    hΛhat.mono fun ω h => h 0
  -- compatibility of the chosen family with the 3/4-clusters at the origin (HB Lemma 5.8)
  have hcomp : ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t →
      (closure (Λhat ω 0 t) ⊆ ball (0 : ℂ) (3 / 4) ∨
        closure (clusterOn (μ' ω) (ball (0 : ℂ) (3 / 4)) 0 t) ⊆ ball (0 : ℂ) (3 / 4)) →
      closure (Λhat ω 0 t) = closure (clusterOn (μ' ω) (ball (0 : ℂ) (3 / 4)) 0 t) := by
    have hsc := hSC γ γ hγ hγ2 hα Ω' P' hC' hcirc' μ' hGFF' hLQG' Λhat hΛhat (ball (0 : ℂ) (3 / 4))
      isOpen_ball Metric.isBounded_ball
    filter_upwards [hsc] with ω hω
    intro t ht hcond
    exact hω t ht 0 (mem_ball_self (by norm_num)) hcond
  have hVGa : ∀ᵐ ω ∂P', ∃ βm βp : ℝ, VolumeGrowth (μ' ω) (3 / 4) βm βp :=
    hVGw γ hγ hγ2 Ω' P' hC' hcirc' μ' hGFF' hLQG'
  -- the premature event forces the half-plateau of the chosen family
  have hpt : ∀ᵐ ω ∂P', halfBallPrematureContact
      (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ' ω) (3 / 4) 0 t))) →
      (1 / 2 : ℝ) ∈ plateauValues (Λhat ω 0) := by
    filter_upwards [hΛ0, hcomp, ae_isLocallyFiniteMeasure_of_isLQGMeasureOfField hLQG', hVGa]
      with ω hreg hcmp hl hv
    intro hpre
    obtain ⟨hsat, -, -⟩ := hreg
    obtain ⟨βm, βp, hV⟩ := hv
    have hmono : ∀ s t : ℝ, 0 < s → s ≤ t → Λhat ω 0 s ⊆ Λhat ω 0 t := fun s t hs hst =>
      hsat.monotoneOn (show s ∈ Ioi (0 : ℝ) from hs) (show t ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hs hst) hst
    have hopen : ∀ t : ℝ, 0 < t → IsOpen (cluster (μ' ω) (3 / 4) 0 t) := fun t ht =>
      (cluster_open_laplacian_of_general greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
        shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds hl (by norm_num) hV
        (mem_ball_self (by norm_num)) (show t ∈ Ioi (0 : ℝ) from ht)).1
    exact plateau_of_prematureContact hmono hcmp hopen hpre
  -- radii a.e. measurable, and fact (1) for the chosen family
  have hRae : ∀ q : ℚ, 0 < (q : ℝ) → AEMeasurable (fun ω => familyRadius (Λhat ω 0 (q : ℝ))) P' :=
    fun q hq => aemeasurable_familyRadius_of_regularized hloc hγ hγ2 hα hGFF' hLQG' (fun ω => Λhat ω 0) hΛ0 hq
  have hscale : ∀ a r : ℝ, 0 < a → 0 < r →
      P' {ω | r ∈ plateauValues (Λhat ω 0)} = P' {ω | a * r ∈ plateauValues (Λhat ω 0)} :=
    fun a r ha hr => hfact1 γ γ hγ hγ2 hα Ω' P' hC' hcirc' μ' (fun ω => Λhat ω 0) inferInstance hGFF' hLQG' hΛ0 a r ha hr
  have hzero : ∀ r : ℝ, 0 < r → P' {ω | r ∈ plateauValues (Λhat ω 0)} = 0 :=
    plateau_measure_zero_of_ae_radii_family P' (fun ω => Λhat ω 0) hRae hscale
  have hle : P' {ω | halfBallPrematureContact
      (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ' ω) (3 / 4) 0 t)))} ≤
      P' {ω | (1 / 2 : ℝ) ∈ plateauValues (Λhat ω 0)} :=
    measure_mono_ae hpt
  rw [hzero (1 / 2) (by norm_num)] at hle
  exact le_antisymm hle zero_le

/-- **`ConePrematureContactNullStep`** (`HalfBallClosure.lean:59`), from the named inputs of the transfer (draft lines
275-289): almost surely the raw `3/4`-clusters of the cone measure have no premature half-ball contact. -/
theorem conePrematureContactNullStep_of_inputs (hloc : HarmonicBallLocalSetStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hfact1 : PlateauScaleInvarianceStep) (hVG : VolumeGrowthStmt) (hVGw : WholePlaneVolumeGrowthAeStep)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep)
    (hLoc : LQGMeasureLocalityFunctionalStep) :
    ConePrematureContactNullStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨E, hE, hEprop⟩ := exists_measurable_halfBallPrematureContact
  have hlc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := ae_isLocallyFiniteMeasure_of_isConeField hcone
  have hvc : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, VolumeGrowth (μ ω) (3 / 4) βm βp :=
    coneVolumeGrowthAeStep_of_volumeGrowthStmt hVG γ hγ hγ2 Ω P hC hcirc μ hcone
  -- (A) on the cone, `μ ∈ E` is the premature event
  have hA : ∀ᵐ ω ∂P, (μ ω ∈ E ↔ halfBallPrematureContact
      (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ ω) (3 / 4) 0 t)))) := by
    filter_upwards [hlc, hvc] with ω hl hv
    obtain ⟨βm, βp, hV⟩ := hv
    exact hEprop (μ ω) hl ⟨βm, βp, hV⟩
  -- (B) restriction to `B_1` does not change the event
  have hB : ∀ᵐ ω ∂P, (μ ω ∈ E ↔ (μ ω).restrict (ball (0 : ℂ) 1) ∈ E) := by
    filter_upwards [hlc, hvc] with ω hl hv
    obtain ⟨βm, βp, hV⟩ := hv
    exact restrict_mem_iff_premature hl hV hEprop
  -- (C) fact (2) for the restricted LQG measures, to the whole-plane model of B2
  obtain ⟨Ω', _, P', hC', hcirc', μ', hP', hGFF', hLQG'⟩ := hB2 γ hγ hγ2
  have hCeq : P {ω | (μ ω).restrict (ball (0 : ℂ) 1) ∈ E} =
      P' {ω' | (μ' ω').restrict (ball (0 : ℂ) 1) ∈ E} :=
    (coneWholePlaneRestrictedLQGLawStep_of_inputs hFL hLoc γ hγ hγ2 Ω P hC hcirc μ hcone Ω' P' hC' hcirc' μ' hP'
      hGFF' hLQG').measure_mem_eq hE
  -- (D) the whole-plane event is null
  have hDz : P' {ω' | (μ' ω').restrict (ball (0 : ℂ) 1) ∈ E} = 0 := by
    have heq' : ∀ᵐ ω ∂P', ((μ' ω).restrict (ball (0 : ℂ) 1) ∈ E ↔
        halfBallPrematureContact (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ' ω) (3 / 4) 0 t)))) := by
      filter_upwards [ae_isLocallyFiniteMeasure_of_isLQGMeasureOfField hLQG',
        hVGw γ hγ hγ2 Ω' P' hC' hcirc' μ' hGFF' hLQG'] with ω hl hv
      obtain ⟨βm, βp, hV⟩ := hv
      exact (restrict_mem_iff_premature hl hV hEprop).symm.trans (hEprop (μ' ω) hl ⟨βm, βp, hV⟩)
    have hsetEq : {ω' | (μ' ω').restrict (ball (0 : ℂ) 1) ∈ E} =ᵐ[P']
        {ω' | halfBallPrematureContact
          (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ' ω') (3 / 4) 0 t)))} :=
      Filter.eventuallyEqSet_iff.mpr heq'
    rw [measure_congr hsetEq]
    exact wholePlane_premature_null hloc hEx hSC hfact1 hVGw hγ hγ2 hGFF' hLQG'
  -- conclusion: `P[μ ∈ E] = P[μ|_{B_1} ∈ E] = P'[μ'|_{B_1} ∈ E] = 0`
  have hsetB : {ω | μ ω ∈ E} =ᵐ[P] {ω | (μ ω).restrict (ball (0 : ℂ) 1) ∈ E} :=
    Filter.eventuallyEqSet_iff.mpr hB
  have hS0 : P {ω | μ ω ∈ E} = 0 := by
    rw [measure_congr hsetB, hCeq, hDz]
  have hae : ∀ᵐ ω ∂P, μ ω ∉ E := ae_iff.mpr (by simpa using hS0)
  filter_upwards [hae, hA] with ω hnot hiff
  exact fun hpr => hnot (hiff.mpr hpr)

/-- **`ConeHalfBallClosureInsideStep`** (frozen target, `StoppedClosure.lean:18`), from the same named inputs, through the
closure argument `coneHalfBallClosureInsideStep_of_prematureContactNull` (`HalfBallClosure.lean`). -/
theorem coneHalfBallClosureInsideStep_of_inputs (hloc : HarmonicBallLocalSetStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hfact1 : PlateauScaleInvarianceStep) (hVG : VolumeGrowthStmt) (hVGw : WholePlaneVolumeGrowthAeStep)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep)
    (hLoc : LQGMeasureLocalityFunctionalStep) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_prematureContactNull
    (conePrematureContactNullStep_of_inputs hloc hEx hSC hfact1 hVG hVGw hB2 hFL hLoc)

/-- **`ConePrematureContactNullStep`, reduced inputs.** The locality input (A) is supplied internally by the proof
`LQGMeasureLocalityFunctionalStep_proof` (`LQGMeasureLocalityProof.lean`). The remaining named inputs are
those of `conePrematureContactNullStep_of_inputs` other than (A): `hloc`, `hEx`, `hSC`, `hfact1`, `hVG`, `hVGw`, `hB2`
and `hFL`. Same conclusion. -/
theorem conePrematureContactNullStep_of_fieldLaw (hloc : HarmonicBallLocalSetStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hfact1 : PlateauScaleInvarianceStep) (hVG : VolumeGrowthStmt) (hVGw : WholePlaneVolumeGrowthAeStep)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) :
    ConePrematureContactNullStep :=
  conePrematureContactNullStep_of_inputs hloc hEx hSC hfact1 hVG hVGw hB2 hFL LQGMeasureLocalityFunctionalStep_proof

/-- **`ConeHalfBallClosureInsideStep`, reduced inputs.** The closure step of `coneHalfBallClosureInsideStep_of_inputs`
with the locality input (A) supplied internally by `LQGMeasureLocalityFunctionalStep_proof`; the named inputs other than
(A) are kept, and the deterministic closure argument is `coneHalfBallClosureInsideStep_of_prematureContactNull`. -/
theorem coneHalfBallClosureInsideStep_of_fieldLaw (hloc : HarmonicBallLocalSetStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hfact1 : PlateauScaleInvarianceStep) (hVG : VolumeGrowthStmt) (hVGw : WholePlaneVolumeGrowthAeStep)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_inputs hloc hEx hSC hfact1 hVG hVGw hB2 hFL LQGMeasureLocalityFunctionalStep_proof

end MatedCRT
