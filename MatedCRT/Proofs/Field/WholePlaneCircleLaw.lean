import MatedCRT.Proofs.Field.WholePlaneCircleBridge

/-!
# The law of whole-plane circle averages

The whole-plane GFF interface fixes the joint law of all positive-radius circle
averages. This supplies the field-law part of the uniformity in Lemma 6.5.
The circle-average interface and GMC estimates used in the companion bridge are
due to Leonardo Bonanno.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Set HarmonicBalls

/-- Whole-plane GFFs have the same joint law of all positive-radius circle averages. -/
theorem wholePlane_circle_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ}
    {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    (h' : HarmonicBalls.IsWholePlaneGFF P' hC' hcirc') :
    P.map (fun ω (p : Set.Ioi (0 : ℝ) × ℂ) => hcirc ω p.1 p.2) =
      P'.map (fun ω (p : Set.Ioi (0 : ℝ) × ℂ) => hcirc' ω p.1 p.2) := by
  let _ : IsProbabilityMeasure P := h.isProbabilityMeasure
  let _ : IsProbabilityMeasure P' := h'.isProbabilityMeasure
  let f : Set.Ioi (0 : ℝ) × ℂ → GFFObservable.Admissible :=
    fun p => ⟨.circle p.1 p.2, p.1.2⟩
  refine map_eq_of_covariance (h.isGaussianProcess.comp_right f) (h'.isGaussianProcess.comp_right f)
    (fun p => h.measurable_circle p.1 p.2 p.1.2)
    (fun p => h'.measurable_circle p.1 p.2 p.1.2)
    (fun p => h.integral_eq_zero (.circle p.1 p.2) p.1.2)
    (fun p => h'.integral_eq_zero (.circle p.1 p.2) p.1.2) ?_
  intro p q
  exact (h.covariance_eq (.circle p.1 p.2) (.circle q.1 q.2) p.1.2 q.1.2).trans
    (h'.covariance_eq (.circle p.1 p.2) (.circle q.1 q.2) p.1.2 q.1.2).symm

end MatedCRT.Field
