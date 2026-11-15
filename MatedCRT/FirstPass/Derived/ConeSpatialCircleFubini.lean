import MatedCRT.FirstPass.Derived.ConeSpatialCircleAgreement
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-! # Spatial almost-everywhere agreement of circle averages -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Distributions
open HarmonicBalls

namespace MatedCRT

/-- The circle-average map is jointly measurable in a distribution and centre. -/
theorem measurable_circleAvg_fixed_radius (r : ℝ) :
    Measurable (fun p : LQGMetric.DistC × ℂ => LQGMetric.circleAvg p.1 r p.2) := by
  exact LQGMetric.measurable_circleAvg.comp
    (f := fun p : LQGMetric.DistC × ℂ => (p.1, r, p.2))
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- A measurable distribution has jointly measurable circle averages at fixed radius. -/
theorem measurable_distribution_circleAvg_param {Ω : Type*} [MeasurableSpace Ω]
    {H : Ω → LQGMetric.DistC} (hH : Measurable H) (r : ℝ) :
    Measurable (fun p : Ω × ℂ => LQGMetric.circleAvg (H p.1) r p.2) := by
  exact (measurable_circleAvg_fixed_radius r).comp
    (f := fun p : Ω × ℂ => (H p.1, p.2))
    ((hH.comp measurable_fst).prodMk measurable_snd)

/-- For any countable family of positive radii, the circle averages of a
matching measurable distribution agree spatially almost everywhere, on one
sample event. -/
theorem ae_cone_circleAvg_eq_spatial {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsQuantumCone γ P hC hcirc) {H : Ω → LQGMetric.DistC}
    (hHm : Measurable H)
    (hH : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∀ᵐ ω ∂P, ∀ n, ∀ᵐ z ∂(volume : Measure ℂ),
      hcirc ω (r n) z = LQGMetric.circleAvg (H ω) (r n) z := by
  have hgrid := ae_cone_gridVersion_eq hQ
  have hn (n : ℕ) : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
      FieldCircle.gridVersion (fun w ω => hcirc ω (r n) w) ω z =
        LQGMetric.circleAvg (H ω) (r n) z := by
    have hm1 := FieldCircle.measurable_gridVersion (fun w ω => hcirc ω (r n) w)
      (fun w => hQ.measurable_circle (r n) w (hr n))
    have hm2 := measurable_distribution_circleAvg_param hHm (r n)
    have hm : MeasurableSet {p : Ω × ℂ |
        FieldCircle.gridVersion (fun w ω => hcirc ω (r n) w) p.1 p.2 =
          LQGMetric.circleAvg (H p.1) (r n) p.2} :=
      measurableSet_eq_fun hm1 hm2
    apply (Measure.ae_ae_comm hm).mpr
    have hs : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ ≠ r n := by
      have hz : (volume : Measure ℂ) (sphere 0 (r n)) = 0 :=
        Measure.addHaar_sphere volume 0 (r n)
      filter_upwards [compl_mem_ae_iff.2 hz] with z hz
      simpa [mem_sphere, dist_zero_right] using hz
    filter_upwards [hs] with z hz
    filter_upwards [hgrid, ae_cone_circleAvg_eq_fixed hQ hH (hr n) hz] with ω hg hc
    exact (hg (r n) (hr n) z).trans hc.symm
  filter_upwards [ae_all_iff.2 hn, hgrid] with ω hω hg n
  filter_upwards [hω n] with z hz
  rw [← hg (r n) (hr n) z]
  exact hz

end MatedCRT
