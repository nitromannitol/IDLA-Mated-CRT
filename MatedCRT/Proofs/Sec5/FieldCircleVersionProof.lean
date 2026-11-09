import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Proofs.Sec5.StoppedActualMarginCode

/-!
# Field-measurable circle versions and the stopped margin

The reconstruction in audited `steps2-r3.tex:3326-3354` is already implemented by
`Sec1.exists_fieldMeasurable_distribution_with_circles`. A countable continuous-function decoder
discharges the residual producer of `StoppedActualMarginCode`; the proved
supersolution section identity removes the other internal input. The three
Preston statements remain explicit literature hypotheses. No numbered result
is asserted here. The distribution reconstruction uses Leonardo Bonanno’s
`LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg` API through `Sec1.Field`.
-/

namespace MatedCRT.StoppedActualMarginCode

open MeasureTheory

/-- The existing distribution reconstruction gives a field-measurable version
of every positive circle, simultaneously almost surely. -/
theorem fieldCircleVersionStmt_holds (𝒮 : SpaceFillingSLEModel) :
    FieldCircleVersionStmt 𝒮 := by
  classical
  intro γ _ _ Ω _ S hS
  obtain ⟨H, hHm, hH⟩ := Sec1.exists_fieldMeasurable_distribution_with_circles hS
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense CircleProcessSpace.PosCircleIndex
  let : Countable D := hDc.to_subtype
  let encode : CircleProcessSpace.PosCircleFns → D → ℝ := fun f p => f p
  have hem : Measurable encode := measurable_pi_iff.mpr fun p =>
    CircleProcessSpace.measurable_posCircleFns_eval p
  have hei : Function.Injective encode := by
    intro f g he
    apply DFunLike.ext'
    apply Continuous.ext_on hDd f.continuous g.continuous
    intro p hp
    exact congrFun he ⟨p, hp⟩
  have hemb : MeasurableEmbedding encode := hem.measurableEmbedding hei
  let decode : (D → ℝ) → CircleProcessSpace.PosCircleFns :=
    Function.extend encode id (fun _ => 0)
  have hdm : Measurable decode := hemb.measurable_extend measurable_id measurable_const
  let coords : Ω → D → ℝ := fun ω p => Sec1.distributionCircleCode (H ω) p
  have hcm : Measurable[S.fieldSigma] coords := by
    let : MeasurableSpace Ω := S.fieldSigma
    exact measurable_pi_iff.mpr fun p =>
      (Sec1.measurable_distributionCircleVersion_fixed p.val.1 p.val.2).comp hHm
  refine ⟨decode ∘ coords, hdm.comp hcm, ?_⟩
  filter_upwards [hH, hS.isQuantumCone.ae_continuousOn_circle] with ω hω hc
  let f : CircleProcessSpace.PosCircleFns :=
    ⟨fun p => S.hcirc ω p.1 p.2, by
      exact hc.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨p.1.2, Set.mem_univ _⟩)⟩
  have heq : coords ω = encode f := by
    funext p
    exact hω.2 p.val.1 p.val.1.2 p.val.2
  have hd : decode (encode f) = f := hei.extend_apply id (fun _ => 0) f
  intro p
  change decode (coords ω) p = f p
  rw [heq, hd]

/-- The actual compact and surplus codes need only the explicit Preston inputs;
the field circle version and supersolution section are supplied by proofs. -/
theorem stoppedMarginCode_of_preston (𝒮 : SpaceFillingSLEModel)
    (hP : PrestonAnalyticUniversallyMeasurableStmt) (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) : StoppedInterior.StoppedMarginCodeStep 𝒮 :=
  stoppedMarginCode_of_inputs 𝒮 hP hCantor hT61
    (ConeOriginNull.codeSectionStmt_holds 𝒮) (fieldCircleVersionStmt_holds 𝒮)

/-- The stopped interior margin has an environment-measurable version under
the three explicit Preston hypotheses. -/
theorem stoppedInteriorMeasurableStep_of_preston (𝒮 : SpaceFillingSLEModel)
    (hP : PrestonAnalyticUniversallyMeasurableStmt) (hCantor : PrestonAnalyticCantorStmt)
    (hT61 : PrestonTheorem61Stmt) : StoppedInterior.StoppedInteriorMeasurableStep 𝒮 :=
  StoppedInterior.stoppedInteriorMeasurable_of_code 𝒮
    (stoppedMarginCode_of_preston 𝒮 hP hCantor hT61)

end MatedCRT.StoppedActualMarginCode
