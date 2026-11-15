import MatedCRT.FirstPass.LPBridge.WholePlaneContinuousVersion
import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

/-! # Selected coordinates of a normalized whole-plane field -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- Pairing and circle versions agreeing with a normalized distribution-valued
field at each admissible coordinate define a whole-plane GFF on its law. -/
theorem isWholePlaneGFF_selected_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2)) :
    IsWholePlaneGFF (P.map Y) hC c := by
  let μ := P.map Y
  let : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hY.1.measurable.aemeasurable).2 inferInstance
  have hnorm : IsNormalizedWPGFF id μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hY.1, ?_⟩
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hY.2
  obtain ⟨hC₀, c₀, hG, hp₀, hc₀⟩ := normalizedGFF_exists_projectGFF hnorm
  have hcm (r : ℝ) (z : ℂ) (hr : 0 < r) : Measurable (fun x => c x r z) := by
    exact hmeas.comp (measurable_const.prodMk measurable_id :
      Measurable (fun x : DistC => ((⟨r, hr⟩, z), x)))
  have hca (r : ℝ) (hr : 0 < r) (z : ℂ) :
      (fun x => c x r z) =ᵐ[μ] fun x => c₀ x r z := by
    have hraw : ∀ᵐ x ∂μ, c x r z = circleAvg x r z :=
      (ae_map_iff hY.1.measurable.aemeasurable
        (measurableSet_eq_fun (hcm r z hr) (measurable_circleAvg_left r z))).2 (hc r hr z)
    filter_upwards [hraw, hc₀ r hr z, hnorm.2] with x h₁ h₂ h₃
    change circleAvg x 1 0 = 0 at h₃
    exact h₁.trans (by simpa only [LQGMetric.CircleAvg.cInc, id_eq, h₃, sub_zero] using h₂.symm)
  have hev : ∀ o : GFFObservable.Admissible,
      (fun x => o.1.eval (hC x) (c x)) =ᵐ[μ] fun x => o.1.eval (hC₀ x) (c₀ x) := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ =>
      filter_upwards with x
      exact (hp x ⟨φ, ho.1, ho.2.1, ho.2.2⟩).trans
        (hp₀ x ⟨φ, ho.1, ho.2.1, ho.2.2⟩).symm
    | circle r z => exact hca r ho z
  refine
    { measurable_pairing := ?_
      measurable_circle := hcm
      isGaussianProcess := hG.isGaussianProcess.congr (fun o => (hev o).symm)
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := Filter.Eventually.of_forall hcont }
  · intro φ hφ
    have heq : (fun x => hC x φ) = fun x => hC₀ x φ := by
      funext x
      exact (hp x ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩).trans
        (hp₀ x ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩).symm
    rw [heq]
    exact hG.measurable_pairing φ hφ
  · intro o ho
    rw [integral_congr_ae (hev ⟨o, ho⟩)]
    exact hG.integral_eq_zero o ho
  · intro o o' ho ho'
    rw [MatedCRT.GFFInterface.cov_congr_ae (hev ⟨o, ho⟩) (hev ⟨o', ho'⟩)]
    exact hG.covariance_eq o o' ho ho'

end MatedCRT.FirstPass.Derived
