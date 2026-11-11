import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.Proofs.Field.WholePlaneBrownian

/-!
# The radial path of a whole-plane GFF on the rational times is Brownian motion

For a whole-plane Gaussian free field `h^ℂ` with circle averages `h^ℂ_r(z)`, the radial path
`q ↦ h^ℂ_{e^{-q}}(0)`, `q ∈ ℚ≥0`, has the law of the coordinate process of standard Brownian motion
`brownianMotion 0` (MarkovProcess, heat semigroup) restricted to `ℚ≥0`. This is the input `GFFRadialBrownian`
of `ConeMeanZeroRestriction` (Duplantier-Sheffield 2011, Prop. 3.1, eq. (3.2); Berestycki-Powell,
*Gaussian free field, Liouville quantum gravity and Gaussian multiplicative chaos*, Ch. 3).

The proof is the restriction to `ℚ≥0` of the law identity on `ℝ≥0 → ℝ` for the radial process
(`MatedCRT.Field.map_radial_eq_brownian`): both sides are centred Gaussian processes with covariance
`min(s, t)`, and the restriction map is measurable, so the laws push forward to the same law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal NNRat

namespace MatedCRT.ConeMeanZeroRestriction

/-- The radial path of a whole-plane GFF on the rational times `ℚ≥0` is a standard Brownian motion in law
(hypothesis `GFFRadialBrownian`, Duplantier-Sheffield 2011). -/
theorem gffRadialBrownian_holds : GFFRadialBrownian := by
  intro Ω _ P hC hcirc hP hh
  have := hP
  -- restriction of a path `ℝ≥0 → ℝ` to the rational times `ℚ≥0`
  have hR : Measurable (fun (f : ℝ≥0 → ℝ) (q : ℚ≥0) => f (q : ℝ≥0)) :=
    Measurable.of_eval (fun q => measurable_pi_apply _)
  have hY : Measurable (fun ω (t : ℝ≥0) => hcirc ω (Real.exp (-(t : ℝ))) 0) :=
    Measurable.of_eval (fun t => hh.measurable_circle (Real.exp (-(t : ℝ))) 0 (Real.exp_pos _))
  have hW : Measurable (fun (w : MarkovProcess.ContinuousPath ℝ) (t : ℝ≥0) => w t) :=
    Measurable.of_eval (fun t => MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t)
  have key := MatedCRT.Field.map_radial_eq_brownian hh
  have hfun : (fun ω (q : ℚ≥0) => radRat (hcirc ω) q) =
      (fun (f : ℝ≥0 → ℝ) (q : ℚ≥0) => f (q : ℝ≥0)) ∘
        (fun ω (t : ℝ≥0) => hcirc ω (Real.exp (-(t : ℝ))) 0) := rfl
  rw [hfun, ← Measure.map_map hR hY, key, Measure.map_map hR hW]
  rfl

end MatedCRT.ConeMeanZeroRestriction
