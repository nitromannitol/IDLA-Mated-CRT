import MatedCRT.Proofs.Sec3.KilledOccupation.GMCLimit
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationAgreementEvent
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders

/-!
# The Green-weighted cut-off GMC limit

For a disc `D = B_r(z)` and a pole `y`, the occupation identity of Liouville Brownian motion killed on leaving `D`
compares the expected occupation measure with the measure `2 G_D(y, x) μ_h(dx)` on `D`, where `G_D` is the Green
function of `D` (normalization `ΔG = -δ`, Armitage-Gardiner, Section 4.1) and `μ_h` is the γ-LQG measure. This file
writes the second measure as a measurable function of the circle averages of the field.

* `greenOccupationDensity z y r`: the density `x ↦ 1_D(x) · 2 G_D(y, x)` with values in `[0, ∞]`.
* `gmcGreenMeasure γ ρ ρ₂ z y r ψ`: the cut-off GMC limit `gmcLimit γ ρ ρ₂ ψ` of the circle averages `ψ`, weighted
  by `greenOccupationDensity z y r`. It is measurable in `ψ` (`measurable_gmcGreenMeasure`).
* `gmcGreenMeasure_eq_of_gmcLimit_eq`: if the GMC limit of `ψ` is the cut-off of a measure `μ` and
  `D ⊆ closedBall 0 ρ`, then `gmcGreenMeasure γ ρ ρ₂ z y r ψ = μ.withDensity (greenOccupationDensity z y r)`: the
  cut-off is `1` on `D`.
* `ae_gmcGreenMeasure_cone`: on the γ-quantum cone, almost surely, the Green-weighted GMC limit of the circle
  averages `S.hcirc` is `(S.μ ω).withDensity (greenOccupationDensity z y r)`.
-/

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The density `x ↦ 1_D(x) · 2 G_D(y, x)` of the expected occupation measure of Brownian motion started at `y` and
killed on leaving the disc `D = B_r(z)`, with `G_D` the Green function of `D`. -/
noncomputable def greenOccupationDensity (z y : ℂ) (r : ℝ) : ℂ → ℝ≥0∞ :=
  (ball z r).indicator fun x => 2 * ENNReal.ofReal (greenFunction (ball z r) y x)

lemma measurable_greenOccupationDensity (z y : ℂ) (r : ℝ) : Measurable (greenOccupationDensity z y r) :=
  ((ENNReal.measurable_ofReal.comp (measurable_greenFunction_ball_left z y r)).const_mul 2).indicator
    measurableSet_ball

lemma greenOccupationDensity_of_mem {z y : ℂ} {r : ℝ} {x : ℂ} (hx : x ∈ ball z r) :
    greenOccupationDensity z y r x = 2 * ENNReal.ofReal (greenFunction (ball z r) y x) :=
  indicator_of_mem hx _

lemma greenOccupationDensity_of_notMem {z y : ℂ} {r : ℝ} {x : ℂ} (hx : x ∉ ball z r) :
    greenOccupationDensity z y r x = 0 :=
  indicator_of_notMem hx _

/-- The Green-weighted cut-off GMC limit `2 · 1_D(x) G_D(y, x) Γ(ψ)(dx)`, `D = B_r(z)`, of a family `ψ` of circle
averages, with `Γ = gmcLimit γ ρ ρ₂`. -/
noncomputable def gmcGreenMeasure (γ ρ ρ₂ : ℝ) (z y : ℂ) (r : ℝ) (ψ : UnitDiskCircleIndex → ℝ) : Measure ℂ :=
  (gmcLimit γ ρ ρ₂ ψ).withDensity (greenOccupationDensity z y r)

/-- The Green-weighted cut-off GMC limit is a measurable function of the circle averages. -/
theorem measurable_gmcGreenMeasure (γ ρ ρ₂ : ℝ) (z y : ℂ) (r : ℝ) :
    Measurable (gmcGreenMeasure γ ρ ρ₂ z y r) :=
  measurable_withDensity_of_measurable (measurable_gmcLimit γ ρ ρ₂) (measurable_greenOccupationDensity z y r)

/-- The Green-weighted cut-off GMC limit gives no mass to the complement of the disc. -/
lemma gmcGreenMeasure_compl_ball (γ ρ ρ₂ : ℝ) (z y : ℂ) (r : ℝ) (ψ : UnitDiskCircleIndex → ℝ) :
    gmcGreenMeasure γ ρ ρ₂ z y r ψ (ball z r)ᶜ = 0 := by
  have h : ∫⁻ x in (ball z r)ᶜ, greenOccupationDensity z y r x ∂gmcLimit γ ρ ρ₂ ψ =
      ∫⁻ _ in (ball z r)ᶜ, 0 ∂gmcLimit γ ρ ρ₂ ψ :=
    setLIntegral_congr_fun measurableSet_ball.compl fun x hx => greenOccupationDensity_of_notMem hx
  rw [gmcGreenMeasure, withDensity_apply _ measurableSet_ball.compl, h, lintegral_zero]

/-- If the cut-off GMC limit of `ψ` is the cut-off `χ · μ` of a measure `μ`, and the disc `B_r(z)` lies in the
region `closedBall 0 ρ` where `χ = 1`, then the Green-weighted GMC limit of `ψ` is `2 · 1_D G_D(y, ·) · μ`. -/
theorem gmcGreenMeasure_eq_of_gmcLimit_eq {γ ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) {z : ℂ} {r : ℝ}
    (hD : ball z r ⊆ closedBall 0 ρ) (y : ℂ) {ψ : UnitDiskCircleIndex → ℝ} {μ : Measure ℂ}
    (h : gmcLimit γ ρ ρ₂ ψ = μ.withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ρ₂ x)) :
    gmcGreenMeasure γ ρ ρ₂ z y r ψ = μ.withDensity (greenOccupationDensity z y r) := by
  have hχ : Measurable fun x : ℂ => ENNReal.ofReal (gmcCutoff ρ ρ₂ x) :=
    ENNReal.measurable_ofReal.comp (continuous_gmcCutoff ρ ρ₂).measurable
  rw [gmcGreenMeasure, h, ← withDensity_mul μ hχ (measurable_greenOccupationDensity z y r)]
  congr 1
  funext x
  by_cases hx : x ∈ ball z r
  · simp [gmcCutoff_eq_one hρρ₂ (mem_closedBall_zero_iff.1 (hD hx))]
  · simp [greenOccupationDensity_of_notMem hx]

/-- **Cone instance.** For the γ-quantum cone environment `S` (`S.IsValid 𝒮 γ`) and a disc `B_r(z) ⊆ B_ρ(0)` with
`ρ < 1`, almost surely the Green-weighted GMC limit of the circle averages `S.hcirc` is the γ-LQG measure `S.μ ω`
weighted by `2 · 1_D G_D(y, ·)`. -/
theorem ae_gmcGreenMeasure_cone {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (hS : S.IsValid 𝒮 γ) {ρ : ℝ} (hρ : ρ < 1) {z : ℂ} {r : ℝ}
    (hD : ball z r ⊆ ball 0 ρ) (y : ℂ) :
    ∀ᵐ ω ∂S.P, gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r (fun q : UnitDiskCircleIndex => S.hcirc ω q.1.1 q.1.2) =
      (S.μ ω).withDensity (greenOccupationDensity z y r) := by
  filter_upwards [ae_gmcLimit_cone_eq_withDensity S 𝒮 γ hS hρ] with ω hω
  exact gmcGreenMeasure_eq_of_gmcLimit_eq (by linarith) (hD.trans ball_subset_closedBall) y hω

/-- The mass that the weighted LQG measure `2 · 1_D G_D(y, ·) · μ` gives to a measurable set `A`: the integral of
`2 G_D(y, ·)` over `A ∩ D` against `μ`. -/
theorem withDensity_greenOccupationDensity_apply (μ : Measure ℂ) (z y : ℂ) (r : ℝ) {A : Set ℂ}
    (hA : MeasurableSet A) :
    μ.withDensity (greenOccupationDensity z y r) A =
      ∫⁻ x in A ∩ ball z r, 2 * ENNReal.ofReal (greenFunction (ball z r) y x) ∂μ := by
  rw [withDensity_apply _ hA, greenOccupationDensity, lintegral_indicator measurableSet_ball,
    Measure.restrict_restrict measurableSet_ball, inter_comm]

end MatedCRT.KilledOccupation
