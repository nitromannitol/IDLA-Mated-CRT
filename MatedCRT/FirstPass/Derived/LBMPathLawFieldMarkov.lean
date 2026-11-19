import MatedCRT.FirstPass.Derived.LBMPathLawFieldDefines
import MatedCRT.FirstPass.Derived.LQGClockMarkov
import MatedCRT.FirstPass.Derived.LQGClockVersionPCAF

/-!
# The rescaled Liouville Brownian law field of a valid environment is Markovian

For `0 < γ < 2` and a valid mated-CRT environment `S` with a measurable version `H` of its field, almost surely
the Borel law field `lbmPathLawField γ (pairJ ⊤ (H ω))` is a Markovian family of path laws
(Berestycki–Gwynne (2020), Definition 7.1).  The clock `F_ω = S.clock ω` has an adapted version `G`, a positive
continuous additive functional of planar Brownian motion (`MatedCRTEnv.IsValid.ae_exists_pcaf_goodClock_clock`),
the Liouville Brownian path agrees almost surely with the rational-time extension `lqgTimeChange G` of the time
change of the path, whose law field is Markov by the strong Markov property of planar Brownian motion at the optional
times `G⁻¹(u)` (`markovAt_lqgTimeChange`), and the time
scale `m = lbmExitMedian γ` preserves the Markov property (`LatticeProb.MarkovAt.timeScalePathKernel`).

* `clockInverse_eq_matedCRT_clockInverse`: the real and the nonnegative right inverses of a clock agree.
* `lbmContinuousPath_eq_lqgTimeChange`: the Liouville Brownian path is almost surely the time change `lqgTimeChange G`.
* `ae_isMarkovianPathFamily_lbmPathLawField`: the quenched Markov property.
-/

set_option autoImplicit false

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The right inverse of a real clock `f` and that of a nonnegative clock `G · b` with `G t b = f t` agree. -/
theorem clockInverse_eq_matedCRT_clockInverse {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {f : ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} (h : ∀ t, (G t b : ℝ) = f t) (v : ℝ≥0) :
    _root_.HarmonicBalls.clockInverse f v = MatedCRT.clockInverse G v b := by
  unfold _root_.HarmonicBalls.clockInverse MatedCRT.clockInverse
  refine congrArg sInf (Set.ext fun t => ?_)
  show (v : ℝ) < f t ↔ v < G t b
  rw [← h t]
  exact NNReal.coe_lt_coe

/-- The Liouville Brownian path of a time-change clock `F` with a version `G` is almost surely the time change
`lqgTimeChange G`. -/
theorem lbmContinuousPath_eq_lqgTimeChange {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw G) (hG : GoodClock planarLaw G) (z : ℂ)
    (hF : ∀ᵐ b ∂planarLaw z, HarmonicBalls.IsTimeChangeClock (F b))
    (hGF : ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t) :
    ∀ᵐ b ∂planarLaw z, lbmContinuousPath F b = lqgTimeChange G b := by
  filter_upwards [ae_exists_path_lqgTimeChange hA hG z, hF, hGF] with b hx hb hbG
  obtain ⟨x, hxv, hxe⟩ := hx
  rw [hxe, lbmContinuousPath_of_isTimeChangeClock hb]
  refine ContinuousMap.ext fun v => ?_
  show b (_root_.HarmonicBalls.clockInverse (F b) v) = x v
  rw [hxv v, clockInverse_eq_matedCRT_clockInverse hbG v]

/-- **The Liouville Brownian law field is Markovian, quenched** (Berestycki–Gwynne (2020), Definition 7.1).  For a
valid environment at `0 < γ < 2` and a measurable version `H` of its field, almost surely the law field
`lbmPathLawField γ (pairJ ⊤ (H ω))` of the rescaled Liouville Brownian motion is a Markovian family of path laws. -/
theorem ae_isMarkovianPathFamily_lbmPathLawField {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, IsMarkovianPathFamily (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) := by
  have hΛ := hS.ae_lbmLawFieldSelection_eq hH hrep (lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS)
  filter_upwards [hS.ae_exists_pcaf_goodClock_clock hrep, hΛ, hS.isLQGClock] with ω hGω hω hclock
  obtain ⟨G, hA, hG, hGa, hGc⟩ := hGω
  choose hg hK using hω
  intro z s
  have hKc : Continuous ⇑(lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω))) :=
    (lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω))).continuous
  have hmark : ∀ (z : ℂ) (u : ℝ≥0), LatticeProb.MarkovAt
      ⇑(lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω))) z u := by
    intro z u
    refine markovAt_lqgTimeChange hA hG hGa hKc ?_ z u
    intro y
    rw [hK y]
    exact Measure.map_congr (lbmContinuousPath_eq_lqgTimeChange hA hG y (hclock y).2 (hGc y))
  exact LatticeProb.MarkovAt.timeScalePathKernel hKc (lbmExitMedian γ).toNNReal s (hmark z _)

/-- **The Liouville Brownian law field is a Markovian time-changed Brownian motion, quenched**
(Berestycki–Gwynne (2020), Definition 7.2): almost surely `lbmPathLawField γ (pairJ ⊤ (H ω))` defines a
time-changed Brownian motion and is Markovian. -/
theorem ae_isMarkovTCBM_lbmPathLawField {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, IsMarkovTCBM (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) := by
  filter_upwards [ae_definesTimeChangedBM_lbmPathLawField hγ hγ2 hS hH hrep,
    ae_isMarkovianPathFamily_lbmPathLawField hγ hγ2 hS hH hrep] with ω h1 h2
  exact ⟨h1, h2⟩

end MatedCRT.FirstPass.Derived
