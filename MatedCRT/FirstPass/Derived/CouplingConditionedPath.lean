import MatedCRT.FirstPass.Derived.DMSPostLastConsumers
import MatedCRT.FirstPass.Derived.DMSPostLastCanonicalLaw
import MatedCRT.FirstPass.Derived.ConeCurveJointScaleLaw
import MatedCRT.FirstPass.Derived.ConeCurveIndep

/-! # Conditioned Brownian path on a mating-of-trees coupling -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

private theorem indepFun_continuousPath_of_coe {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} {f : Ω → β} {W : Ω → C(ℝ≥0, ℝ)}
    (h : IndepFun f (fun ω => (⇑(W ω) : ℝ≥0 → ℝ)) P) : IndepFun f W P := by
  have hσ : MeasurableSpace.comap W (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.comap (fun ω => (⇑(W ω) : ℝ≥0 → ℝ)) MeasurableSpace.pi := by
    apply le_antisymm
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap
        (fun ω => (⇑(W ω) : ℝ≥0 → ℝ)) MeasurableSpace.pi
      have hm : Measurable fun ω => (⇑(W ω) : ℝ≥0 → ℝ) := comap_measurable _
      exact ContinuousMap.measurable_iff_eval.2 fun t => (measurable_pi_apply t).comp hm
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
      have hm : Measurable W := comap_measurable _
      exact measurable_pi_iff.2 fun t => (ContinuousMap.measurable_eval t).comp hm
  unfold IndepFun Kernel.IndepFun at h ⊢
  rw [hσ]
  exact h

/-- On a mating-of-trees coupling, the conditioned outer Brownian path can be
chosen independently of the joint whole-plane field and inner Brownian path. -/
theorem exists_conditionedPath_indep_field_brownian_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ W F : Ω → C(ℝ≥0, ℝ), Measurable W ∧ Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, F ω t = referenceConeConditionedPath γ (fun s => B' s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) ∧
      IndepFun (fun ω => (X ω, W ω)) F P := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨W, hWm, hW⟩ := MatedCRTHarmonic.ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨V, hVm, hV⟩ := MatedCRTHarmonic.ConeScaling.exists_continuousMap_version D.bm_B'
  have he : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
      fun ω => ((⇑(W ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)) := by
    filter_upwards [hW, hV] with ω hw hv
    exact Prod.ext (funext fun t => (hw t).symm) (funext fun t => (hv t).symm)
  have hX : IndepFun X (fun ω => (W ω, V ω)) P :=
    MatedCRTHarmonic.ConeScaling.indepFun_pair_continuousMap_of_coe
      (D.indep_cone.1.congr (ae_eq_refl _) he)
  have hWV0 : IndepFun (fun ω => (⇑(W ω) : ℝ≥0 → ℝ))
      (fun ω => (⇑(V ω) : ℝ≥0 → ℝ)) P := by
    apply D.indep_cone.2.congr
    · filter_upwards [hW] with ω hw
      exact funext fun t => (hw t).symm
    · filter_upwards [hV] with ω hv
      exact funext fun t => (hv t).symm
  have hWV : IndepFun W V P :=
    indepFun_continuousPath_of_coe (indepFun_continuousPath_of_coe hWV0.symm).symm
  have hind : IndepFun (fun ω => (X ω, W ω)) V P :=
    indepFun_prodMk_left_of_indepFun_prodMk D.gff.measurable hWm hVm hX hWV
  let d := MatedCRTHarmonic.MatedCRT.lqgQ γ - γ
  let F := fun ω => MatedCRT.Proposed.postLastPathMap d (V ω)
  have hFm : Measurable F := (MatedCRT.Proposed.measurable_postLastPathMap d).comp hVm
  have hF : ∀ᵐ ω ∂P, ∀ t, F ω t = referenceConeConditionedPath γ (fun s => B' s ω) t := by
    filter_upwards [hV] with ω hv t
    have hv' : (⇑(V ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext hv
    change MatedCRT.Proposed.postLastPathMap d (V ω) t = _
    rw [← hv']
    exact (MatedCRT.Proposed.dmsPostLastZeroPath_eq_postLast d (V ω) t).symm
  refine ⟨W, F, hWm, hFm, hW, hF, ?_, hind.comp measurable_id
    (MatedCRT.Proposed.measurable_postLastPathMap d)⟩
  exact MatedCRT.Proposed.dms14Remark44PostLastZeroLaw γ hγ hγ2 Ω P B' F D.bm_B' hFm hF

end MatedCRT.Sec1
