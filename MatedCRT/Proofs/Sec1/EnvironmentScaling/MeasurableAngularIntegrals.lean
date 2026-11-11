import MatedCRT.Proofs.Sec1.EnvironmentScaling.AngularLogIntegrability
import MatedCRT.Proofs.Sec1.EnvironmentScaling.GaussianBandProof
import Mathlib.MeasureTheory.Integral.Prod
import MatedCRT.LPStaging.Analysis.AngularIntegralMeasurable

/-!
# Measurable circle averages of random radial families

Fixed-circle measurability component of the lateral observable,
`ℓ(r,z) = a(r,z) - (1/2π) ∫_0^{2π} a(|z + r e^{iθ}|, 0) dθ` for `r > 0`.

The radial-family statements and their proofs are the general ones of
`LatticeProb.AngularIntegralMeasurable` (`MatedCRT/LPStaging/Analysis/AngularIntegralMeasurable.lean`).
This file keeps the lateral-observable names: each statement is the LP statement with the same
hypotheses, its proof cites the LP lemma, and the circle definitions agree with the LP ones by `rfl`.
The Brownian specializations (`aemeasurable_circle_brownian`, `ae_intervalIntegrable_circle_brownian`)
are proved here, from the radial-path lemmas.
-/

open MeasureTheory Set Filter Topology Complex

namespace MatedCRT.Sec1

/-- The exceptional angles of the circle `θ ↦ z + r e^{iθ}`: the angles at which the circle passes
through `0`.  For `r > 0` this set is countable (`countable_circleZeroAngles`), hence null. -/
noncomputable def circleZeroAngles (z : ℂ) (r : ℝ) : Set ℝ :=
  {θ : ℝ | ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ = 0}

/-- The exceptional angles agree with the Lattice-Probability definition. -/
theorem circleZeroAngles_eq_lp :
    circleZeroAngles = LatticeProb.AngularIntegralMeasurable.circleZeroAngles := rfl

/-- For `r > 0` the exceptional angles are countable. -/
lemma countable_circleZeroAngles {z : ℂ} {r : ℝ} (hr : 0 < r) :
    (circleZeroAngles z r).Countable :=
  LatticeProb.AngularIntegralMeasurable.countable_circleZeroAngles hr

/-- The exceptional angles are Lebesgue-null when `r > 0`. -/
lemma volume_circleZeroAngles {z : ℂ} {r : ℝ} (hr : 0 < r) :
    volume (circleZeroAngles z r) = 0 :=
  LatticeProb.AngularIntegralMeasurable.volume_circleZeroAngles hr

/-- The complement of the exceptional angles is measurable when `r > 0`. -/
lemma measurableSet_circleZeroAngles_compl {z : ℂ} {r : ℝ} (hr : 0 < r) :
    MeasurableSet (circleZeroAngles z r)ᶜ :=
  LatticeProb.AngularIntegralMeasurable.measurableSet_circleZeroAngles_compl hr

/-- Joint measurability of the truncated radial family `(s, ω) ↦ 1_{Nᶜ}(ω) X (max s a) ω`. -/
lemma measurable_truncated_radial {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ}
    (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω) {N : Set Ω} (hN : MeasurableSet N)
    (hNc : ∀ ω, ω ∉ N → ContinuousOn (fun s => X s ω) (Ioi 0)) {a : ℝ} (ha : 0 < a) :
    Measurable fun q : ℝ × Ω => Nᶜ.indicator (fun ω => X (max q.1 a) ω) q.2 :=
  LatticeProb.AngularIntegralMeasurable.measurable_truncated_radial hXm hN hNc ha

/-- The truncated circle integrand on `Ω × ℝ` at level `n`: the value `1_{Nᶜ}(ω) X (max |z + r e^{iθ}|
(1/(n+1))) ω` at `(ω, θ)`, with the exceptional angles removed. -/
noncomputable def truncatedCircleIntegrand {Ω : Type*} (X : ℝ → Ω → ℝ) (N : Set Ω) (z : ℂ) (r : ℝ)
    (n : ℕ) : Ω × ℝ → ℝ :=
  (Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ).indicator fun q : Ω × ℝ =>
    Nᶜ.indicator (fun ω => X (max ‖z + (r : ℂ) * exp (I * (q.2 : ℂ))‖ (1 / ((n : ℝ) + 1))) ω) q.1

/-- The circle integrand on `Ω × ℝ`: the value `1_{Nᶜ}(ω) X |z + r e^{iθ}| ω` at `(ω, θ)` for `θ` off the
exceptional angles, and `0` on them. -/
noncomputable def circleIntegrandLimit {Ω : Type*} (X : ℝ → Ω → ℝ) (N : Set Ω) (z : ℂ) (r : ℝ) :
    Ω × ℝ → ℝ :=
  (Prod.snd ⁻¹' (circleZeroAngles z r)ᶜ).indicator fun q : Ω × ℝ =>
    Nᶜ.indicator (fun ω => X ‖z + (r : ℂ) * exp (I * (q.2 : ℂ))‖ ω) q.1

/-- The truncated circle integrand is the Lattice-Probability one. -/
theorem truncatedCircleIntegrand_eq_lp {Ω : Type*} (X : ℝ → Ω → ℝ) (N : Set Ω) (z : ℂ) (r : ℝ)
    (n : ℕ) :
    truncatedCircleIntegrand X N z r n =
      LatticeProb.AngularIntegralMeasurable.truncatedCircleIntegrand X N z r n := rfl

/-- The circle integrand limit is the Lattice-Probability one. -/
theorem circleIntegrandLimit_eq_lp {Ω : Type*} (X : ℝ → Ω → ℝ) (N : Set Ω) (z : ℂ) (r : ℝ) :
    circleIntegrandLimit X N z r =
      LatticeProb.AngularIntegralMeasurable.circleIntegrandLimit X N z r := rfl

/-- Each truncated circle integrand is jointly measurable on `Ω × ℝ`. -/
lemma measurable_truncatedCircleIntegrand {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ}
    (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω) {N : Set Ω} (hN : MeasurableSet N)
    (hNc : ∀ ω, ω ∉ N → ContinuousOn (fun s => X s ω) (Ioi 0)) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (n : ℕ) : Measurable (truncatedCircleIntegrand X N z r n) :=
  LatticeProb.AngularIntegralMeasurable.measurable_truncatedCircleIntegrand hXm hN hNc hr n

/-- **Fixed-circle measurability.**  For a radial family `X s ω` with measurable coordinates on `(0, ∞)` and
almost surely continuous radius, and for fixed `z` and `r > 0`, the circle integral
`ω ↦ ∫_{[0,2π]} X |z + r e^{iθ}| ω dθ` is a.e. measurable.  Circles through zero are included. -/
theorem aemeasurable_circle_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => ∫ θ in Icc 0 (2 * Real.pi), X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω) P :=
  LatticeProb.AngularIntegralMeasurable.aemeasurable_circle_integral P X hXm hXc z hr

/-- **Normalized circle average.**  The normalized integral `(2π)⁻¹ ∫_{[0,2π]} X |z + r e^{iθ}| ω dθ`,
the angular average in the lateral observable `ℓ(r,z)`, is a.e. measurable for fixed `z` and `r > 0`. -/
theorem aemeasurable_circle_average {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => (2 * Real.pi)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω) P :=
  LatticeProb.AngularIntegralMeasurable.aemeasurable_circle_average P X hXm hXc z hr

/-- Mathlib's circle average of a radial function as the normalized integral over `[0, 2π]`. -/
lemma circleAverage_eq_normalized (f : ℝ → ℝ) (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun x : ℂ => f ‖x‖) z r =
      (2 * Real.pi)⁻¹ * ∫ θ in Icc 0 (2 * Real.pi), f ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ :=
  LatticeProb.AngularIntegralMeasurable.circleAverage_eq_normalized f z r

/-- **Lateral circle average.**  For a radial family with measurable coordinates on `(0, ∞)` and a.s.
continuity there, the circle average `ω ↦ Real.circleAverage (fun x ↦ X ‖x‖ ω) z r` of
`lateralEval` (`Defs/QuantumCone.lean`, the `.circle r z` observable) is a.e. measurable for `r > 0`. -/
theorem aemeasurable_realCircleAverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ s : ℝ, 0 < s → Measurable fun ω => X s ω)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => Real.circleAverage (fun x : ℂ => X ‖x‖ ω) z r) P :=
  LatticeProb.AngularIntegralMeasurable.aemeasurable_realCircleAverage P X hXm hXc z hr

/-- **Circles through zero.**  If `‖z‖ = r` and the radial family has the logarithmic majorant
`|X t ω| ≤ C (1 + |log t|)` on `(0, 2r]` almost surely, then the angular integrand
`θ ↦ X |z + r e^{iθ}| ω` is a.s. interval integrable on `[0, 2π]`. -/
theorem ae_intervalIntegrable_circle_through_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Ioi 0)) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : ‖z‖ = r)
    (hlog : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 2 * r → |X t ω| ≤ C * (1 + |Real.log t|)) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun θ : ℝ => X ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ ω)
      volume 0 (2 * Real.pi) :=
  LatticeProb.AngularIntegralMeasurable.ae_intervalIntegrable_circle_through_zero P X hXc hr hz hlog

/-- Radial path: the family `s ↦ B (-log s)` is a.s. continuous on `(0, ∞)` when `t ↦ B t ω` is
a.s. continuous (`t = -log|z|`). -/
lemma ae_continuousOn_log_radialPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ → Ω → ℝ} (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω) :
    ∀ᵐ ω ∂P, ContinuousOn (fun s : ℝ => B (-Real.log s) ω) (Ioi 0) :=
  LatticeProb.AngularIntegralMeasurable.ae_continuousOn_log_radialPath hcont

/-- **Radial path, normalized circle average.**  For a radial path `B` with measurable coordinates
`ω ↦ B t ω` and a.s. continuous `t ↦ B t ω`, the normalized angular average
`(2π)⁻¹ ∫_{[0,2π]} B (-log |z + r e^{iθ}|) ω dθ` is a.e. measurable for fixed `z` and `r > 0`. -/
theorem aemeasurable_circle_radialPath {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (hBm : ∀ t : ℝ, Measurable fun ω => B t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => (2 * Real.pi)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), B (-Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖) ω) P :=
  LatticeProb.AngularIntegralMeasurable.aemeasurable_circle_radialPath P B hBm hcont z hr

/-- Sublinear growth gives the logarithmic majorant on `(0, 2r]` for the radial path, when `2r ≤ 1`. -/
lemma ae_log_majorant_radialPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ → Ω → ℝ} {r : ℝ} (hr2 : 2 * r ≤ 1) (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t ω / t) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 2 * r →
      |B (-Real.log t) ω| ≤ C * (1 + |Real.log t|) :=
  LatticeProb.AngularIntegralMeasurable.ae_log_majorant_radialPath hr2 hcont hsub

/-- **Radial path, circles through zero.**  For a radial path with a.s. continuous `t ↦ B t ω` and
sublinear growth `B t ω / t → 0`, and for a circle through zero (`‖z‖ = r`, `2r ≤ 1`), the angular
integrand `θ ↦ B (-log |z + r e^{iθ}|) ω` is a.s. interval integrable on `[0, 2π]`. -/
theorem ae_intervalIntegrable_circle_radialPath {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t ω / t) atTop (𝓝 0)) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hr2 : 2 * r ≤ 1) (hz : ‖z‖ = r) :
    ∀ᵐ ω ∂P, IntervalIntegrable
      (fun θ : ℝ => B (-Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖) ω) volume 0 (2 * Real.pi) :=
  LatticeProb.AngularIntegralMeasurable.ae_intervalIntegrable_circle_radialPath P B hcont hsub hr hr2 hz

/-- **Brownian radial path, normalized circle average.**  For a Brownian motion `B` indexed by
`ℝ≥0` (`IsBrownianReal`), the radial path is read as `t ↦ B t.toNNReal`.  Its
a.s. continuity is `IsBrownianReal.cont`.  The coordinate measurability `hBm` remains a premise, since
`IsBrownianReal` gives measurability only almost everywhere (through `HasLaw`). -/
theorem aemeasurable_circle_brownian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : NNReal → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P)
    (hBm : ∀ t : NNReal, Measurable fun ω => B t ω) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => (2 * Real.pi)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), B (-Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖).toNNReal ω) P :=
  aemeasurable_circle_radialPath P (fun t ω => B t.toNNReal ω) (fun t => hBm t.toNNReal)
    (hB.cont.mono fun _ hω => hω.comp continuous_real_toNNReal) z hr

/-- **Brownian radial path, circles through zero.**  For a Brownian motion `B` indexed by `ℝ≥0`, and a
circle through zero (`‖z‖ = r`, `2r ≤ 1`), the angular integrand `θ ↦ B (-log |z + r e^{iθ}|).toNNReal ω`
is a.s. interval integrable on `[0, 2π]`.  The growth premise is the Gaussian-band sublinear growth
`ae_tendsto_div_real_of_isBrownianReal` (GaussianBandProof), so only `hBm` is assumed. -/
theorem ae_intervalIntegrable_circle_brownian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : NNReal → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P)
    (hBm : ∀ t : NNReal, Measurable fun ω => B t ω) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : 2 * r ≤ 1) (hz : ‖z‖ = r) :
    ∀ᵐ ω ∂P, IntervalIntegrable
      (fun θ : ℝ => B (-Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖).toNNReal ω) volume 0
        (2 * Real.pi) :=
  ae_intervalIntegrable_circle_radialPath P (fun t ω => B t.toNNReal ω)
    (hB.cont.mono fun _ hω => hω.comp continuous_real_toNNReal)
    (ae_tendsto_div_real_of_isBrownianReal hB hBm) hr hr2 hz

end MatedCRT.Sec1
