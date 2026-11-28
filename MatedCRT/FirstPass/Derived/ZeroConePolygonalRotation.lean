import MatedCRT.FirstPass.Derived.ZeroConeStandardBorelSteps
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhase

/-!
# The rotation law of the zero-cone curve

Gwynne–Miller–Sheffield (arXiv:1705.11161v5, proof of Proposition 3.1, p. 24) use that "the law of `(h, η)` is
invariant under rotations about the origin", where `η` is the space-filling curve parametrized by the quantum area
of the zero cone `h`. For the mating-of-trees coupling `D` and `γ ∈ (0, 2)` this file proves the statement for the
curve: the zero-cone curve `η₀` and its quarter turn `t ↦ i η₀(t)` have the same law.

* `map_quarterTurnCurve_eta0`: `P.map (fun ω => quarterTurnCurve (η₀ ω)) = P.map η₀`.

The proof is the first marginal of the phase-shifted rotation identity of the zero-cone curve
(`MatedCRTHarmonic.GMS4O.p48o_map_zeroConeCurve_phase_shift`, Lattice-Probability): for every angle `θ`,
`(e^{-iθ} η₀, (U - χθ) mod 2πχ)` has the law of `(η₀, U)`. That identity comes from the coupling alone: the
rotation invariance of the laws of the zero-cone field and of the imaginary-geometry field with its uniform phase,
the coordinate-change clause of the curve, the rotation covariance of the dyadic area approximations at every
cutoff, and the area parametrization of `η₀`. At `θ = -π/2` the rotation is the quarter turn.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-- The rotation of a curve by `π/2` is its quarter turn. -/
theorem rotCurve_neg_neg_pi_div_two (c : C(ℝ, ℂ)) :
    IGLaw.rotCurve (-(-(Real.pi / 2))) c = GMS310Transfer.quarterTurnCurve c := by
  ext t
  show Complex.exp (((-(-(Real.pi / 2)) : ℝ) : ℂ) * Complex.I) * c t = Complex.I * c t
  rw [neg_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The rotation law of the zero-cone curve** (Gwynne–Miller–Sheffield, arXiv:1705.11161v5, proof of
Proposition 3.1, p. 24): for the mating-of-trees coupling and `γ ∈ (0, 2)`, the quarter turn `t ↦ i η₀(t)` of the
zero-cone curve parametrized by quantum area has the law of `η₀`. It is the first marginal of the phase-shifted
rotation identity of the zero-cone curve at the angle `-π/2`. -/
theorem map_quarterTurnCurve_eta0
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    P.map (fun ω => GMS310Transfer.quarterTurnCurve (η₀ ω)) = P.map η₀ := by
  have := D.isProbabilityMeasure
  have hr : 0 < 2 * Real.pi * igChi γ := GMS4O.p48o_period_pos D
  have : Fact (0 < 2 * Real.pi * igChi γ) := ⟨hr⟩
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hr D.igField.2.1
  have hη : Measurable η₀ := D.measurable_curves.2.2.1
  have hlaw := GMS4O.p48o_map_zeroConeCurve_phase_shift D hγ (-(Real.pi / 2))
  have hL : AEMeasurable (fun ω => (IGLaw.rotCurve (-(-(Real.pi / 2))) (η₀ ω),
      IGLaw.modRep (2 * Real.pi * igChi γ) (-(igChi γ * -(Real.pi / 2)) + U ω))) P :=
    ((IGLaw.measurable_rotCurve _).comp hη).aemeasurable.prodMk
      ((IGLaw.measurable_modRep _).comp_aemeasurable (aemeasurable_const.add hUm))
  have hR : AEMeasurable (fun ω => (η₀ ω, U ω)) P := hη.aemeasurable.prodMk hUm
  have hfst : (P.map fun ω => (IGLaw.rotCurve (-(-(Real.pi / 2))) (η₀ ω),
      IGLaw.modRep (2 * Real.pi * igChi γ) (-(igChi γ * -(Real.pi / 2)) + U ω))).map Prod.fst =
      (P.map fun ω => (η₀ ω, U ω)).map Prod.fst := by
    rw [hlaw]
  rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hL,
    AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hR] at hfst
  have e : (Prod.fst ∘ fun ω => (IGLaw.rotCurve (-(-(Real.pi / 2))) (η₀ ω),
      IGLaw.modRep (2 * Real.pi * igChi γ) (-(igChi γ * -(Real.pi / 2)) + U ω))) =
      fun ω => GMS310Transfer.quarterTurnCurve (η₀ ω) := by
    funext ω
    exact rotCurve_neg_neg_pi_div_two (η₀ ω)
  rw [e] at hfst
  exact hfst

end MatedCRT.ZeroConePolygonal
