import MatedCRT.FirstPass.Derived.WindowChartLawMeasurable
import MatedCRT.FirstPass.Derived.WindowInteriorJointLimit
import MatedCRT.FirstPass.Derived.InverseChartOfJordan

/-!
# Inverse charts of the windows on the joint limit

For the window `(a, u, b)` of the curve, Berestycki–Gwynne (2020), proof of Lemma 7.21, use that the window domain
`U` (the connected component of the interior of `η([a, b])` containing `η(u)`) has a Jordan frontier: "`∂U` is a
Jordan curve so the desired extension of `φ` follows from [Pom92, Theorem 2.6]". The frontier of `η([a, b])` is made
of arcs of flow lines of the imaginary-geometry field (Miller–Sheffield, *Imaginary geometry IV*, arXiv:1302.4738,
Sections 1.2.3 and 4.3). This file states that geometric fact as the named hypothesis `WindowFrontierJordanInput` and
derives from it the almost sure existence of inverse charts of the windows on a weak limit `ν''` of the joint laws.

* `WindowFrontierJordanInput 𝒮`: for a valid environment and fixed times `a < u < b`, almost surely the frontier of
  the window domain is a Jordan curve.
* `windowDomain_eq_of_coe_eq`: the window domain of a continuous version of a curve is the component of the
  interior of the segment image of the curve itself.
* `ae_jointLimit_exists_isInverseChart_windowDomain`: under `WindowFrontierJordanInput 𝒮`, for `ν''`-almost every
  sample the window `(a, u, b)` has an inverse chart at `η(u)` (the environment statement from
  `MatedCRTEnv.IsValid.ae_fixedTime_mem_interior_image` and `exists_isInverseChart_windowDomain`, transferred to
  `ν''` through the Borel event `measurableSet_setOf_exists_isInverseChart`).
* `BG20NormalizedChartCoreInput 𝒮`: `BG20NormalizedChartLBMInput 𝒮` without its two inverse-chart conjuncts, and
  `bg20ChartFieldInput_of_coreInput : WindowFrontierJordanInput 𝒮 → BG20NormalizedChartCoreInput 𝒮 →
  BG20ChartFieldInput 𝒮`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **Window-geometry input (Miller–Sheffield, *Imaginary geometry IV*, arXiv:1302.4738, Sections 1.2.3 and 4.3;
used in Berestycki–Gwynne (2020), arXiv:2003.10320, proof of Lemma 7.21: "`∂U` is a Jordan curve").**
PENDING TRUTH CHECK.

For `0 < γ < 2`, a valid environment `S` and fixed times `a < u < b`, almost surely the frontier of the window domain
of the curve, the connected component containing `η(u)` of the interior of `η([a, b])`, is a Jordan curve (the image
of the unit circle under a map continuous and injective on it). For a continuous version `η'` of the curve this set is
`windowDomain (η' ω) a u b` (`windowDomain_eq_of_coe_eq`). The frontier of `η([a, b])` for the whole-plane
space-filling SLE_{16/γ²} consists of arcs of the flow lines of the imaginary-geometry field from `η(a)` and `η(b)`. -/
def WindowFrontierJordanInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ a u b : ℝ, a < u → u < b →
    ∀ᵐ ω ∂S.P, LQGMetric.JordanMap.IsJordanCurve
      (frontier (connectedComponentIn (interior (S.η ω '' Icc a b)) (S.η ω u)))

/-- The window domain of a continuous version `η` of a curve `f` is the connected component containing `f(u)` of the
interior of `f([a, b])`. -/
theorem windowDomain_eq_of_coe_eq {η : C(ℝ, ℂ)} {f : ℝ → ℂ} (h : ⇑η = f) (a u b : ℝ) :
    windowDomain η a u b = connectedComponentIn (interior (f '' Icc a b)) (f u) := by
  unfold windowDomain
  rw [h]

/-- **Inverse charts of a window on the joint limit** (Berestycki–Gwynne (2020), proof of Lemma 7.21, for the limit
of the joint laws). Assume `WindowFrontierJordanInput 𝒮`. Let `ν''` be a weak limit of the joint laws of the field
coordinates, a measurable coordinate `E`, a version `η'` of the curve and a sequence of path-law families `Z n`. Then
for fixed times `a < u < b`, for `ν''`-almost every sample the window `(a, u, b)` has an inverse chart at `η(u)`. -/
theorem ae_jointLimit_exists_isInverseChart_windowDomain {𝒮 : SpaceFillingSLEModel}
    (hG : WindowFrontierJordanInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν''))) {a u b : ℝ} (hau : a < u) (hub : u < b) :
    ∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ := by
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  let Data := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)
  have hD : Measurable fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  have hmarg : ν''.map Prod.fst = S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hD hconv
  let B : Set Data := Prod.snd ⁻¹' {η : C(ℝ, ℂ) | ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ}
  have hB : MeasurableSet B := measurable_snd (measurableSet_setOf_exists_isInverseChart a u b)
  have hsrc : ∀ᵐ x ∂(S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data)), x ∈ B := by
    refine (ae_map_iff hD.aemeasurable hB).2 ?_
    filter_upwards [hS.ae_fixedTime_mem_interior_image u, hG γ hγ hγ2 Ω S hS a u b hau hub, hae]
      with ω hω hJ he
    show ∃ ψ, IsInverseChart (windowDomain (η' ω) a u b) (η' ω u) ψ
    refine exists_isInverseChart_windowDomain (η' ω) ?_ ?_
    · rw [he]
      exact hω a b hau hub
    · rw [windowDomain_eq_of_coe_eq he]
      exact hJ
  rw [← hmarg] at hsrc
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hsrc] with q hq
  exact hq

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit, with the normalized inverse charts), without the inverse charts.** As `BG20NormalizedChartLBMInput`, without
the almost sure existence of inverse charts of the two windows (which follows from `WindowFrontierJordanInput`,
`ae_jointLimit_exists_isInverseChart_windowDomain`). For times `a < u < b < a' < u' < b'`:

* the kernel `K` depends measurably on the chart field;
* (Lemma 7.20 without the time change; Berestycki (2015), Theorem 1.3) almost surely the chart image of the
  Liouville Brownian law of the field from `η(u)` is `K` of the chart field, and likewise for the second window;
* (Lemma 7.21) the pairs (chart field, window chart law) of the two windows are independent. -/
def BG20NormalizedChartCoreInput (𝒮 : SpaceFillingSLEModel) : Prop :=
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
    ∃ K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ),
      Measurable K ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
        K (windowChartField γ a u b (windowChart a u b q.1.2) q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (windowChart a' u' b' q.1.2) q =
        K (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q)) ∧
      IndepFun (fun q : JointSample => (windowChartField γ a u b (windowChart a u b q.1.2) q,
          windowChartLaw a u b (windowChart a u b q.1.2) q))
        (fun q : JointSample => (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q,
          windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q)) ν''

/-- The window-geometry input and the input without inverse charts imply `BG20NormalizedChartLBMInput`. -/
theorem bg20NormalizedChartLBMInput_of_coreInput {𝒮 : SpaceFillingSLEModel}
    (hG : WindowFrontierJordanInput 𝒮) (hC : BG20NormalizedChartCoreInput 𝒮) :
    BG20NormalizedChartLBMInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  have := hν''
  obtain ⟨K, hK, hb, hb', hind⟩ :=
    hC γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'
  exact ⟨K,
    ae_jointLimit_exists_isInverseChart_windowDomain hG hγ hγ2 hS hη' hae hH hE
      (Z := fun n ω => interpWalkLaw S η' (ε n) ω) hconv hau hub,
    ae_jointLimit_exists_isInverseChart_windowDomain hG hγ hγ2 hS hη' hae hH hE
      (Z := fun n ω => interpWalkLaw S η' (ε n) ω) hconv ha'u' hu'b',
    hK, hb, hb', hind⟩

/-- **The chart input from the window geometry.** The window-geometry input `WindowFrontierJordanInput` and the
input without inverse charts `BG20NormalizedChartCoreInput` imply `BG20ChartFieldInput`. -/
theorem bg20ChartFieldInput_of_coreInput {𝒮 : SpaceFillingSLEModel}
    (hG : WindowFrontierJordanInput 𝒮) (hC : BG20NormalizedChartCoreInput 𝒮) : BG20ChartFieldInput 𝒮 :=
  bg20ChartFieldInput_of_normalizedChartLBMInput (bg20NormalizedChartLBMInput_of_coreInput hG hC)

end MatedCRT
