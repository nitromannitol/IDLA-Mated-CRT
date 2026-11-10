import MatedCRT.FirstPass.Frozen.S2h
import MatedCRT.FirstPass.Frozen.S2k
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionScalingLaw

/-! # FIRST PASS S2l: the whole-plane LQG scaling law from the insertion coordinate rule (task fp-S2l-wholeplane-scaling-derive)

`firstPass_wholePlaneLQGScaling_of_coordinateRule` proves the frozen `MatedCRT.FrozenWholePlaneLQGScaling`
(`FirstPass/Frozen/S2h.lean`) from the frozen insertion coordinate rule `FrozenInsertionCoordinateRule`
(`FirstPass/Frozen/S2k.lean`, input K). No other external input is used.

Route: truth note `notes/fp-gaps/CHATGPT-idla-K-S2h-S2k-truth.md` §2, "Short proof from (1)". The three ingredients of that
argument are already proved in the repository, and this file re-runs the proof of
`insertionLQGScalingLawStep_of_coordinateRule` (`Proofs/Sec4/Prop42Closure/InsertionScalingLaw.lean`) at `α = γ`, `a = s`,
keeping the explicit constant `c_s = h_s(0) + Q log s` (the Step there only asserts an existential constant):
1. dyadic limit of the affine map `z ↦ s z` (`FrozenInsertionCoordinateRule` with `a = s`, `b = 0`);
2. the constant shift by `Q log s + h_s(0)` multiplies the limit by `e^{-γ c_s}` (`isLQGLimit_insertion_shift`);
3. the shifted field is the normalized field `H(s·) − H_s(0)` of the whole-plane GFF, which has the law of `H`
   (`MatedCRT.Field.isWholePlaneGFF_affine`, `MatedCRT.Field.wholePlane_circle_law`);
4. the Borel recovery of the vague limit (`identDistrib_lqgMeasure_of_circleProcess`) gives equality in law.
Normalization: `h_s(0) = H_s(0) − γ log s` with `H_s(0) = h^ℂ_s(0)`, so `A_s = e^{γ H_s(0)} s^{2−γ²/2}`. -/

namespace MatedCRT.FirstPass.S2l

open MeasureTheory Filter Topology Set Metric ProbabilityTheory HarmonicBalls
open scoped ENNReal

/-- **Derived: `FrozenWholePlaneLQGScaling` (FIRST-PASS, fp-S2l).** From the frozen insertion coordinate rule
`FrozenInsertionCoordinateRule` (`FirstPass/Frozen/S2k.lean`), the whole-plane LQG scaling law holds: for `0 < γ < 2`, a
whole-plane GFF `h^ℂ` with `γ`-insertion LQG measure `μ` and `s > 0`, the random measure `A_s^{-1} · μ(s^{-1} ·)` with
`A_s = e^{γ H_s(0)} s^{2-γ²/2}` has the law of `μ`. -/
theorem firstPass_wholePlaneLQGScaling_of_coordinateRule
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) : MatedCRT.FrozenWholePlaneLQGScaling := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hP hGFF hLQG _hμ s hs
  have := hP
  have hα : γ < lqgQ γ := by
    unfold lqgQ
    have h4 : γ * γ < 4 := by nlinarith
    have h2 : 0 < 2 / γ - γ / 2 := by
      rw [div_sub_div _ _ hγ0.ne' two_ne_zero]
      apply div_pos <;> nlinarith
    linarith
  have hna : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hGFF'' : IsWholePlaneGFF P (MatedCRT.Field.affHC s 0 hC hcirc) (MatedCRT.Field.affHcirc s 0 hcirc) :=
    MatedCRT.Field.isWholePlaneGFF_affine hGFF hs 0
  have hDSae := hK γ γ hγ0 hγ2 hα Ω P hC hcirc μ hP hGFF hLQG (s : ℂ) (Complex.ofReal_ne_zero.mpr hs.ne') 0
  have hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (fun ε z => fieldCircleAverage γ (MatedCRT.Field.affHcirc s 0 hcirc ω) ε z)
      (insertionScaledMeasure γ (insertionScaleConst γ γ s (hcirc ω)) ((μ ω).map fun x => x / (s : ℂ))) := by
    filter_upwards [hDSae, insertion_ae_continuousOn hGFF γ] with ω hω hcω
    simp only [hna, sub_zero, add_zero] at hω
    have hsh := isLQGLimit_insertion_shift (hc := hcirc ω) (m := (μ ω).map fun x => x / (s : ℂ)) hs hcω hω
    refine isLQGLimit_congr_pos ?_ hsh
    intro ε hε
    funext z
    exact (fieldCircleAverage_affHcirc_pos γ hs hcirc ω hε z).symm
  have hXm : Measurable fun ω (p : Ioi (0 : ℝ) × ℂ) => hcirc ω p.1 p.2 :=
    measurable_pi_iff.mpr fun p => hGFF.measurable_circle (p.1 : ℝ) p.2 p.1.2
  have hX''m : Measurable fun ω (p : Ioi (0 : ℝ) × ℂ) => MatedCRT.Field.affHcirc s 0 hcirc ω p.1 p.2 :=
    measurable_pi_iff.mpr fun p => hGFF''.measurable_circle (p.1 : ℝ) p.2 p.1.2
  have hX : IdentDistrib (fun ω => circleProcess (hcirc ω))
      (fun ω => circleProcess (MatedCRT.Field.affHcirc s 0 hcirc ω)) P P :=
    ⟨hXm.aemeasurable, hX''m.aemeasurable, MatedCRT.Field.wholePlane_circle_law hGFF hGFF''⟩
  have hT : Measurable fun g : Ioi (0 : ℝ) × ℂ → ℝ => fun p : Ioi (0 : ℝ) × ℂ =>
      g p - γ * Real.circleAverage (fun x => Real.log ‖x‖) p.2 p.1 :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p).sub measurable_const
  have hlaw := hX.comp hT
  have hI := identDistrib_lqgMeasure_of_circleProcess (γ := γ)
    (c := fun ω => fieldCircleAverage γ (hcirc ω))
    (d := fun ω => fieldCircleAverage γ (MatedCRT.Field.affHcirc s 0 hcirc ω))
    (μ := μ)
    (ν := fun ω => insertionScaledMeasure γ (insertionScaleConst γ γ s (hcirc ω)) ((μ ω).map fun x => x / (s : ℂ)))
    (insertion_ae_continuousOn hGFF γ) (insertion_ae_continuousOn hGFF'' γ) hLQG hlim
    (aemeasurable_lqgMeasure_of_circleAverages (γ := γ) (hε := fun ω => fieldCircleAverage γ (hcirc ω))
      (fun r z hr => insertion_measurable_fieldCircleAverage hGFF γ z hr) (insertion_ae_continuousOn hGFF γ) hLQG)
    (aemeasurable_lqgMeasure_of_circleAverages (γ := γ)
      (hε := fun ω => fieldCircleAverage γ (MatedCRT.Field.affHcirc s 0 hcirc ω))
      (fun r z hr => insertion_measurable_fieldCircleAverage hGFF'' γ z hr) (insertion_ae_continuousOn hGFF'' γ) hlim)
    hlaw
  have hfun : (fun ω => ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log s + fieldCircleAverage γ (hcirc ω) s 0)))⁻¹ •
      Measure.map (fun x : ℂ => s⁻¹ • x) (μ ω)) =
      (fun ω => insertionScaledMeasure γ (insertionScaleConst γ γ s (hcirc ω)) ((μ ω).map fun x => x / (s : ℂ))) := by
    funext ω
    have hscal : ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log s + fieldCircleAverage γ (hcirc ω) s 0)))⁻¹
        = ENNReal.ofReal (Real.exp (γ * -insertionScaleConst γ γ s (hcirc ω))) := by
      unfold insertionScaleConst
      congr 1
      rw [← Real.exp_neg]
      congr 1
      ring
    have hsc' : (μ ω).map (fun x : ℂ => x / (s : ℂ)) = (μ ω).map (fun x : ℂ => s⁻¹ • x) := by
      congr 1
      funext x
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    rw [hscal, insertionScaledMeasure, withDensity_const, hsc']
  rw [hfun]
  exact hI.symm.map_eq

end MatedCRT.FirstPass.S2l
