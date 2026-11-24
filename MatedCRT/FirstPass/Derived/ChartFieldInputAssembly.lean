import MatedCRT.FirstPass.Derived.ChartFieldLBM
import MatedCRT.FirstPass.Derived.WindowChartFieldMeasurable
import MatedCRT.FirstPass.Derived.WindowInverseChartJointLimit

/-!
# The chart input of the joint limit from Lévy's conformal invariance and the window geometry

Assembly of the chart input `BG20NormalizedChartCoreInput` of the joint limit (Berestycki–Gwynne (2020),
arXiv:2003.10320, Lemmas 7.20 and 7.21) from

* Lévy's conformal invariance of planar Brownian motion (`LevyConformalChartStmt`);
* the coordinate change of Liouville Brownian motion (`ChartFieldLBMLimitStmt γ`, Berestycki (2015), Theorem 1.3);
* the window geometry (`WindowFrontierJordanInput`: the frontier of the window domain is a Jordan curve);
* the independence of the two windows (`BG20ChartIndependenceInput`, Berestycki–Gwynne (2020), Lemma 7.21).

## Main statements

* `measurable_windowLBMChartLaw_windowChart`: the chart image, for the normalized inverse chart of a window, of the
  Liouville Brownian law of the field of a joint-limit sample is a measurable function of the sample.
* `BG20ChartIndependenceInput`: the independence conjunct (Lemma 7.21) of `BG20NormalizedChartCoreInput` alone.
* `bg20NormalizedChartCoreInput_of_chartFieldLBMLimit`: the four inputs above give
  `BG20NormalizedChartCoreInput 𝒮`.
* `bg20ChartFieldInput_of_chartFieldLBMLimit`: they give `BG20ChartFieldInput 𝒮`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **The chart image of the Liouville Brownian law of a window is a measurable function of the sample.** For the
window `(a, u, b)` and its normalized inverse chart `windowChart a u b η`, the chart image of the rescaled Liouville
Brownian law of the field of the joint-limit sample `q` from `η(u)` is the window chart law of the sample whose path-law
family is replaced by the Borel law field `lbmPathLawField γ` at the field coordinates. -/
theorem measurable_windowLBMChartLaw_windowChart (γ a u b : ℝ) :
    Measurable (fun q : JointSample => windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q) := by
  have hg : Measurable fun q : JointSample => ((q.1, lbmPathLawField γ q.1.1.1) : JointSample) :=
    measurable_fst.prodMk ((measurable_lbmPathLawField γ).comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  have h : (fun q : JointSample => windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q) =
      (fun q : JointSample => windowChartLaw a u b (windowChart a u b q.1.2) q) ∘
        fun q : JointSample => ((q.1, lbmPathLawField γ q.1.1.1) : JointSample) := rfl
  rw [h]
  exact (measurable_windowChartLaw_windowChart a u b).comp hg

/-- **Literature input (Berestycki–Gwynne (2020), arXiv:2003.10320, Lemma 7.21, on the joint limit).**
PENDING TRUTH CHECK.

In the setting of `BG20NormalizedChartCoreInput`: let `ν''` be a weak limit of the joint laws of the field
coordinates, a measurable coordinate `E`, a version `η'` of the curve and the interpolated walk law, which is almost
surely a linear time change of the Liouville Brownian law field. For times `a < u < b < a' < u' < b'`, the pairs
(chart field, window chart law) of the two windows `(a, u, b)` and `(a', u', b')`, for their normalized inverse charts,
are independent under `ν''`. -/
def BG20ChartIndependenceInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure JointSample, IsProbabilityMeasure ν'' →
    (∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∀ a u b a' u' b' : ℝ, a < u → u < b → b < a' → a' < u' → u' < b' →
      IndepFun (fun q : JointSample => (windowChartField γ a u b (windowChart a u b q.1.2) q,
          windowChartLaw a u b (windowChart a u b q.1.2) q))
        (fun q : JointSample => (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q,
          windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q)) ν''

/-- **The chart input without inverse charts from Lévy's conformal invariance, the coordinate change of Liouville
Brownian motion, the window geometry and the independence of the windows.** The Borel kernel `K` of
`exists_kernel_ae_windowLBMChartLaw_eq` (Berestycki (2015), Theorem 1.3, through `ChartFieldLBMLimitStmt γ`) serves
both windows: its premises are the measurability of the window chart image of the Liouville Brownian law
(`measurable_windowLBMChartLaw_windowChart`) and of the chart field (`measurable_windowChartField_windowChart`), and
its guard, the existence of an inverse chart of the window at `η(u)`, holds almost surely on the joint limit by the
window geometry (`ae_jointLimit_exists_isInverseChart_windowDomain`). -/
theorem bg20NormalizedChartCoreInput_of_chartFieldLBMLimit {𝒮 : SpaceFillingSLEModel}
    (hLevy : LevyConformalChartStmt) (hgap : ∀ γ, 0 < γ → γ < 2 → ChartFieldLBMLimitStmt γ)
    (hG : WindowFrontierJordanInput 𝒮) (hI : BG20ChartIndependenceInput 𝒮) :
    BG20NormalizedChartCoreInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  have := hν''
  obtain ⟨K, hKm, hK⟩ := exists_kernel_ae_windowLBMChartLaw_eq hLevy hγ hγ2 (hgap γ hγ hγ2)
  have hlaw : ∀ {s t r : ℝ}, s < t → t < r →
      ∀ᵐ q ∂ν'', windowLBMChartLaw γ s t r (windowChart s t r q.1.2) q =
        K (windowChartField γ s t r (windowChart s t r q.1.2) q) := by
    intro s t r hst htr
    filter_upwards [hK 𝒮 Ω S hS H hH hrep η' hη' E hE (fun n ω => interpWalkLaw S η' (ε n) ω) ν'' hν''
        hconv s t r (measurable_windowLBMChartLaw_windowChart γ s t r)
        (measurable_windowChartField_windowChart γ s t r),
      ae_jointLimit_exists_isInverseChart_windowDomain hG hγ hγ2 hS hη' hae hH hE
        (Z := fun n ω => interpWalkLaw S η' (ε n) ω) hconv hst htr] with q hq hψ
    exact hq hψ
  exact ⟨K, hKm, hlaw hau hub, hlaw ha'u' hu'b',
    hI γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'⟩

/-- **The chart input of the joint limit** (`BG20ChartFieldInput`) from Lévy's conformal invariance, the coordinate
change of Liouville Brownian motion (Berestycki (2015), Theorem 1.3), the window geometry (Miller–Sheffield,
*Imaginary geometry IV*) and the independence of the windows (Berestycki–Gwynne (2020), Lemma 7.21). -/
theorem bg20ChartFieldInput_of_chartFieldLBMLimit {𝒮 : SpaceFillingSLEModel}
    (hLevy : LevyConformalChartStmt) (hgap : ∀ γ, 0 < γ → γ < 2 → ChartFieldLBMLimitStmt γ)
    (hG : WindowFrontierJordanInput 𝒮) (hI : BG20ChartIndependenceInput 𝒮) : BG20ChartFieldInput 𝒮 :=
  bg20ChartFieldInput_of_coreInput hG (bg20NormalizedChartCoreInput_of_chartFieldLBMLimit hLevy hgap hG hI)

end MatedCRT
