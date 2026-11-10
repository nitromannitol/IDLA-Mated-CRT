import HarmonicBalls.Defs.LQG
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces

/-!
# Shape bridge: Lattice-Probability LQG area measures and Harmonic-Balls LQG measures

The predicate `MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf` of Lattice-Probability (a.s. vague convergence on
`ℂ` of `ε^{γ²/2} e^{γ h_ε(z)} dz` along the dyadic scales `2^{-k}`) and the predicate
`HarmonicBalls.IsLQGMeasure` (eq:measure-lim, `HarmonicBalls/Defs/LQG.lean`) describe the same property of a
random measure: the same approximations, the same scales, the same quantifiers. This file proves the
identification, and its specialisations `α₀ = 0` and `α₀ = γ` (the γ-quantum cone) to the Harmonic-Balls
predicate `HarmonicBalls.IsLQGMeasureOfField`.

These are statements about definitions only. They do not assert that any γ-LQG measure exists.

References: Duplantier-Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
arXiv:0808.1560, Proposition 1.1; Bou-Rabee-Gwynne, arXiv:2208.11795, Section 2.2.
-/

namespace MatedCRT.FirstPass.LPBridge

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Lattice-Probability dyadic radius `2^{-k}` is the Harmonic-Balls dyadic scale `(2⁻¹)^k`. -/
theorem dyadicRadius_eq_dyadicScale (k : ℕ) :
    MatedCRTHarmonic.GMSLemma27.dyadicRadius k = HarmonicBalls.dyadicScale k := by
  simp [MatedCRTHarmonic.GMSLemma27.dyadicRadius, HarmonicBalls.dyadicScale, zpow_neg, zpow_natCast, inv_pow]

/-- The Lattice-Probability area measure predicate `IsLQGAreaOf` of the field with circle averages
`(r, z, ω) ↦ hε ω r z` is the Harmonic-Balls predicate `IsLQGMeasure` of `hε`. -/
theorem isLQGAreaOf_iff_isLQGMeasure (γ : ℝ) (hε : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (P : Measure Ω) :
    MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ (fun r z ω => hε ω r z) μ P ↔
      HarmonicBalls.IsLQGMeasure P γ hε μ := by
  have key : ∀ (ω : Ω) (k : ℕ), MatedCRTHarmonic.GMSLemma27.lqgApprox γ (fun r z ω' => hε ω' r z) k ω =
      HarmonicBalls.lqgApprox γ (hε ω) (HarmonicBalls.dyadicScale k) := by
    intro ω k
    simp only [MatedCRTHarmonic.GMSLemma27.lqgApprox, HarmonicBalls.lqgApprox, dyadicRadius_eq_dyadicScale]
  unfold MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf HarmonicBalls.IsLQGMeasure
  apply Filter.eventually_congr
  refine Filter.Eventually.of_forall fun ω => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf hfs => by simpa only [key] using h2 f hf hfs⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf hfs => by simpa only [key] using h2 f hf hfs⟩

/-- The Harmonic-Balls predicate `IsLQGMeasureOfField P γ α₀ hcirc μ` (the γ-LQG measure of
`h = h^ℂ - α₀ log|·|`) is the Lattice-Probability predicate `IsLQGAreaOf` of the circle averages
`fieldCircleAverage α₀ (hcirc ω)`. -/
theorem isLQGMeasureOfField_iff_isLQGAreaOf (γ α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (P : Measure Ω) :
    HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ ↔
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ
        (fun r z ω => HarmonicBalls.fieldCircleAverage α₀ (hcirc ω) r z) μ P :=
  (isLQGAreaOf_iff_isLQGMeasure γ _ μ P).symm

/-- The α₀ = 0 case (no log shift): `IsLQGMeasureOfField P γ 0 hcirc μ` is `IsLQGAreaOf` of the circle
averages `hcirc` themselves. -/
theorem isLQGMeasureOfField_zero_iff_isLQGAreaOf (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (P : Measure Ω) :
    HarmonicBalls.IsLQGMeasureOfField P γ 0 hcirc μ ↔
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ (fun r z ω => hcirc ω r z) μ P := by
  rw [isLQGMeasureOfField_iff_isLQGAreaOf]
  simp only [HarmonicBalls.fieldCircleAverage, zero_mul, sub_zero]

/-- The γ-quantum cone case `α₀ = γ`: `IsLQGMeasureOfField P γ γ hcirc μ` is `IsLQGAreaOf` of the circle
averages `hcirc ω r z - γ · Real.circleAverage (log ‖·‖) z r`. -/
theorem isLQGMeasureOfField_cone_iff_isLQGAreaOf (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (P : Measure Ω) :
    HarmonicBalls.IsLQGMeasureOfField P γ γ hcirc μ ↔
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ
        (fun r z ω => hcirc ω r z - γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r) μ P := by
  rw [isLQGMeasureOfField_iff_isLQGAreaOf]
  simp only [HarmonicBalls.fieldCircleAverage]

end MatedCRT.FirstPass.LPBridge
