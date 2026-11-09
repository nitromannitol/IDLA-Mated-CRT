import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionCoordinateExtensionProof
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionScalingLaw

/-!
# Input K of Proposition 4.2 from its two named inputs: the exact Step and its fixed-`a` form (steps3:678-713)

Task `z1-steps3-insertion-scaling-consumer-assembly`. A bounded consumer integration. It is not an unconditional closure of
Input K and not a closure of Proposition 4.2. Beyond the field data of each statement (a probability space, a whole-plane
GFF, its insertion-`α` LQG measure, `0 < γ < 2`, `α < Q`, and `a > 0`), the exports take exactly the two named inputs of the
Step `InsertionLQGScalingLawStep` (`Proofs/Sec4/Prop42Closure/PlateauScaleLaw.lean:106`):

* `hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0}` (`Proposed/SheffieldWang2016.lean:47`), the staged
  compact-interior form of Sheffield-Wang, arXiv:1605.06171v2, Theorem 1.1, p. 3. It is a literature input carried as an
  explicit hypothesis; its admission as a source is not established here.
* `hDec : LocalDirichletHarmonicDecompositionStep` (`Proofs/Sec4/Prop42Closure/InsertionCoordinate.lean:663`), the local
  Dirichlet/harmonic decomposition (steps3:609-621), a producer residual.

Route. `insertionCoordinateExtensionStep_of_components hSWI hDec` (`InsertionCoordinateExtensionProof.lean:280`) proves the
fixed-map coordinate rule `InsertionCoordinateExtensionStep`. The checked consumer
`insertionLQGScalingLawStep_of_coordinateRule` (`InsertionScalingLaw.lean:157`) turns that rule into the Step. Both are
used unchanged. No further hypothesis is added: no norm hypothesis, no finiteness of the ambient zero-boundary limit, no
raw-circle covariance premise and no local-finiteness premise on `ℂ`.

Fixed `a`. `insertionLQGScalingLaw_fixed_a_of_components` displays the witnesses that the existential in the Step hides:
the affine field `affHC a 0 hC hcirc`, `affHcirc a 0 hcirc`; the normalized pushed-forward measure
`insertionScaledMeasure γ c (μ.map (· / a))` with `c = insertionScaleConst γ α a (hcirc ω)`; the positive scalar
`exp (γ c)`; the `IsLQGMeasureOfField` property of the affine field; and the equality in law. Its proof repeats the body
of the consumer with these witnesses, reusing the same lemmas and the same measure decoder.

Credit to Leonardo Bonanno's imported infrastructure, by exact module. The new file names no Bonanno declaration. Two
MatedCRT field laws it calls are built on it: `MatedCRT.Field.wholePlane_circle_law` (`Proofs/Field/WholePlaneCircleLaw.lean`,
whose header credits Bonanno for the circle-average interface and GMC estimates), via its companion bridge
`Proofs/Field/WholePlaneCircleBridge.lean`, which uses Bonanno's `LQGDimension.IsGFFCircleAverage` interface and imports
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge`, `LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux` and
`LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail`. The affine whole-plane law `MatedCRT.Field.isWholePlaneGFF_affine`
(`Proofs/Field/WholePlaneAffine.lean`) is reached through the import chain `Proofs/Field/WholePlaneAffineCov.lean` and
`HarmonicBalls/Steps/Sec11/PairingCovarianceLinearity.lean`, whose header credits Bonanno's LatticeProb formalization of the
ergodic theorem; which of its results the affine proof uses has not been traced here.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory HarmonicBalls
open scoped ENNReal

namespace MatedCRT

/-- **The exact Step `InsertionLQGScalingLawStep`, from its two named inputs.** The fixed-map coordinate rule is
`insertionCoordinateExtensionStep_of_components hSWI hDec`, and the existing consumer
`insertionLQGScalingLawStep_of_coordinateRule` (`InsertionScalingLaw.lean:157`) turns it into the Step. The only
hypotheses are `hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0}` and `hDec : LocalDirichletHarmonicDecompositionStep`. -/
theorem insertionLQGScalingLawStep_of_components
    (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    (hDec : LocalDirichletHarmonicDecompositionStep) : InsertionLQGScalingLawStep :=
  insertionLQGScalingLawStep_of_coordinateRule (insertionCoordinateExtensionStep_of_components hSWI hDec)

/-- **Input K at a fixed scale `a > 0`, with its witnesses displayed.** Under the two named inputs, let `(hC, hcirc)` be a
whole-plane GFF on a probability space `(Ω, P)` and let `μ` be its insertion-`α` LQG measure. For every `a > 0`:
(1) the affine field `(affHC a 0 hC hcirc, affHcirc a 0 hcirc)` is a whole-plane GFF;
(2) its insertion-`α` LQG measure is `μ''(ω) = insertionScaledMeasure γ c(ω) ((μ ω).map (· / a))`, where
`c(ω) = insertionScaleConst γ α a (hcirc ω) = fieldCircleAverage α (hcirc ω) a 0 + Q log a`;
(3) almost surely `exp (γ c(ω)) > 0` and `(μ ω).map (· / a) = ofReal (exp (γ c(ω))) • μ''(ω)`;
(4) `μ'' =_d μ` (`IdentDistrib μ'' μ P P`). -/
theorem insertionLQGScalingLaw_fixed_a_of_components
    (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    (hDec : LocalDirichletHarmonicDecompositionStep)
    (γ α : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hP : IsProbabilityMeasure P)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (hLQG : IsLQGMeasureOfField P γ α hcirc μ)
    (a : ℝ) (ha : 0 < a) :
    IsWholePlaneGFF P (MatedCRT.Field.affHC a 0 hC hcirc) (MatedCRT.Field.affHcirc a 0 hcirc) ∧
    IsLQGMeasureOfField P γ α (MatedCRT.Field.affHcirc a 0 hcirc)
      (fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ))) ∧
    (∀ᵐ ω ∂P, 0 < Real.exp (γ * insertionScaleConst γ α a (hcirc ω)) ∧
      (μ ω).map (fun x : ℂ => x / (a : ℂ)) =
        ENNReal.ofReal (Real.exp (γ * insertionScaleConst γ α a (hcirc ω))) •
          insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ))) ∧
    IdentDistrib
      (fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ)))
      μ P P := by
  have hDS := insertionCoordinateExtensionStep_of_components hSWI hDec
  have hna : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hGFF'' : IsWholePlaneGFF P (MatedCRT.Field.affHC a 0 hC hcirc) (MatedCRT.Field.affHcirc a 0 hcirc) :=
    MatedCRT.Field.isWholePlaneGFF_affine hGFF ha 0
  have hDSae := hDS γ α hγ0 hγ2 hα Ω P hC hcirc μ hP hGFF hLQG (a : ℂ) (Complex.ofReal_ne_zero.mpr ha.ne') 0
  have hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (fun ε z => fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω) ε z)
      (insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ))) := by
    filter_upwards [hDSae, insertion_ae_continuousOn hGFF α] with ω hω hcω
    simp only [hna, sub_zero, add_zero] at hω
    have hsh := isLQGLimit_insertion_shift (hc := hcirc ω) (m := (μ ω).map fun x => x / (a : ℂ)) ha hcω hω
    refine isLQGLimit_congr_pos ?_ hsh
    intro ε hε
    funext z
    exact (fieldCircleAverage_affHcirc_pos α ha hcirc ω hε z).symm
  have hLQGaff : IsLQGMeasureOfField P γ α (MatedCRT.Field.affHcirc a 0 hcirc)
      (fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ))) :=
    hlim
  refine ⟨hGFF'', hLQGaff, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ω =>
      ⟨Real.exp_pos _, (ofReal_exp_smul_insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) _).symm⟩
  · have hXm : Measurable fun ω (p : Ioi (0 : ℝ) × ℂ) => hcirc ω p.1 p.2 :=
      measurable_pi_iff.mpr fun p => hGFF.measurable_circle (p.1 : ℝ) p.2 p.1.2
    have hX''m : Measurable fun ω (p : Ioi (0 : ℝ) × ℂ) => MatedCRT.Field.affHcirc a 0 hcirc ω p.1 p.2 :=
      measurable_pi_iff.mpr fun p => hGFF''.measurable_circle (p.1 : ℝ) p.2 p.1.2
    have hX : IdentDistrib (fun ω => circleProcess (hcirc ω))
        (fun ω => circleProcess (MatedCRT.Field.affHcirc a 0 hcirc ω)) P P :=
      ⟨hXm.aemeasurable, hX''m.aemeasurable, MatedCRT.Field.wholePlane_circle_law hGFF hGFF''⟩
    have hT : Measurable fun g : Ioi (0 : ℝ) × ℂ → ℝ => fun p : Ioi (0 : ℝ) × ℂ =>
        g p - α * Real.circleAverage (fun x => Real.log ‖x‖) p.2 p.1 :=
      measurable_pi_iff.mpr fun p => (measurable_pi_apply p).sub measurable_const
    have hlaw := hX.comp hT
    have hI := identDistrib_lqgMeasure_of_circleProcess (γ := γ)
      (c := fun ω => fieldCircleAverage α (hcirc ω))
      (d := fun ω => fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω))
      (μ := μ)
      (ν := fun ω => insertionScaledMeasure γ (insertionScaleConst γ α a (hcirc ω)) ((μ ω).map fun x => x / (a : ℂ)))
      (insertion_ae_continuousOn hGFF α) (insertion_ae_continuousOn hGFF'' α) hLQG hlim
      (aemeasurable_lqgMeasure_of_circleAverages (γ := γ) (hε := fun ω => fieldCircleAverage α (hcirc ω))
        (fun r z hr => insertion_measurable_fieldCircleAverage hGFF α z hr) (insertion_ae_continuousOn hGFF α) hLQG)
      (aemeasurable_lqgMeasure_of_circleAverages (γ := γ)
        (hε := fun ω => fieldCircleAverage α (MatedCRT.Field.affHcirc a 0 hcirc ω))
        (fun r z hr => insertion_measurable_fieldCircleAverage hGFF'' α z hr) (insertion_ae_continuousOn hGFF'' α) hlim)
      hlaw
    exact hI.symm

end MatedCRT
