import MatedCRT.FirstPass.Derived.ValidSelectedComponentVisits
import MatedCRT.FirstPass.Derived.BlockRunningMinTail
import LatticeProb.Prob.CorrelatedBMCompletedObservations
import LatticeProb.Prob.AEDetermined
import LatticeProb.Topology.ComponentVisitCodeEndpointGeneral
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3G

/-! # Observations of selected component endpoints -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LatticeProb LatticeProb.CorrelatedBM MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- Under two-sided observation of the visit code and an interval-image witness,
the endpoints have versions observable from the Brownian increments on the segment. -/
theorem MatedCRTEnv.IsValid.exists_segment_observable_component_endpoints
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) (η : Ω → C(ℝ, ℂ))
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω) (A B : Ω → ℝ)
    (hpast : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Iic b) b).comap S.bm) S.P)
    (hfuture : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Ici a) a).comap S.bm) S.P)
    (hcomponent : ∀ᵐ ω ∂S.P,
      a ≤ A ω ∧ A ω < B ω ∧ B ω ≤ b ∧
      (η ω) '' Icc (A ω) (B ω) =
        closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))) :
    ∃ A' B' : Path2 → ℝ,
      Measurable[incrementSigma lrCoord (Icc a b) a] A' ∧
      Measurable[incrementSigma lrCoord (Icc a b) a] B' ∧
      (∀ᵐ ω ∂S.P, A' (S.bm ω) = A ω ∧ B' (S.bm ω) = B ω) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hab : a ≤ b := (hau.trans hub).le
  have hbm := hS.isCorrelatedBM2_map_bm
  have hmeas (T : Set ℝ) (c : ℝ) :
      incrementSigma lrCoord T c ≤ (inferInstance : MeasurableSpace Path2) := by
    refine iSup_le fun i => iSup_le fun t => iSup_le fun _ => ?_
    exact measurable_iff_comap_le.mp (measurable_coneIncr i t c)
  have hci : LatticeProb.CondIndepEv
      ((incrementSigma lrCoord (Icc a b) a).comap S.bm)
      ((incrementSigma lrCoord (Iic b) b).comap S.bm)
      ((incrementSigma lrCoord (Ici a) a).comap S.bm) S.P := by
    apply LQGMetric.DFGPS.L217.condIndepEv_comap_of_map hbm.2
      (hmeas _ _) (hmeas _ _) (hmeas _ _)
    exact LatticeProb.CorrelatedBM.condIndepEv_increment_past_future hbm.1 hab
  have hbound (T : Set ℝ) (c : ℝ) :
      (incrementSigma lrCoord T c).comap S.bm ≤ (inferInstance : MeasurableSpace Ω) :=
    (MeasurableSpace.comap_mono (hmeas T c)).trans hbm.2.comap_le
  have hdet := AELeSigma.of_condIndepEv_two_sides
    (MeasurableSpace.comap_mono (incrementSigma_segment_le_past lrCoord hab))
    (hbound _ _) (hbound _ _) hci hpast hfuture
  obtain ⟨V, hV, hVe⟩ := exists_ae_eq_measurable_of_aeDeterminedSigma hdet
  obtain ⟨A₀, B₀, hA₀, hB₀, hAB⟩ :=
    exists_observable_endpoints_of_restricted_component_visit_code_general
      ((incrementSigma lrCoord (Icc a b) a).comap S.bm) S.P η
      (fun ω => η ω u) (Icc a b) a b hab V A B hV
      (by filter_upwards [hVe] with ω hω q; exact (congrFun hω q).symm)
      (hS.ae_selected_component_visit_identity hau hub hη A B hcomponent)
  have hfactor (F : Ω → ℝ)
      (hF : Measurable[(incrementSigma lrCoord (Icc a b) a).comap S.bm] F) :
      ∃ F' : Path2 → ℝ, Measurable[incrementSigma lrCoord (Icc a b) a] F' ∧
        F = F' ∘ S.bm := by
    let : MeasurableSpace Path2 := incrementSigma lrCoord (Icc a b) a
    exact hF.exists_eq_measurable_comp
  obtain ⟨A', hA', hAe⟩ := hfactor A₀ hA₀
  obtain ⟨B', hB', hBe⟩ := hfactor B₀ hB₀
  refine ⟨A', B', hA', hB', ?_⟩
  filter_upwards [hAB] with ω hω
  exact ⟨by simpa only [hAe, Function.comp_apply] using hω.1,
    by simpa only [hBe, Function.comp_apply] using hω.2⟩

end MatedCRT
