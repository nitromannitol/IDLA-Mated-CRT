import MatedCRT.FirstPass.Derived.HN9OfChartLaws
import MatedCRT.FirstPass.Derived.HN9OfJointLimitSpeedRecovery

/-!
# Lemmas 7.20 and 7.21 on the joint limit, for the windows of the curve

Berestycki–Gwynne (2020) state Lemmas 7.20 and 7.21 on a subsequential limit in law `(h, η, P)` of the field, the
curve and the walk laws, for the windows `η([a, b])` of the curve: for `a < u < b`, `U` is the connected component
of the interior of `η([a, b])` containing `η(u)`, and `P^D_0` is the image of the limiting law `P_{η(u)}` under
"stop at the exit from `U` and apply `φ⁻¹`", where `φ : 𝔻 → U` is the conformal map with `φ(0) = η(u)`.

This file states the chart input in that setting (`BG20JointChartLawInput`): on a weak limit `ν''` of the joint laws
of the field coordinates, the coordinate `E`, the curve and the interpolated walk laws, the point is
`windowPoint`, the domain is `windowDomain` (both read off the curve coordinate), and only the inverse chart map
`ψ`, the chart field and the chart Liouville Brownian kernel are existential. It implies `BG20ChartLawInput`
(`bg20ChartLawInput_of_jointChartLaws`; the joint limit with the curve exists along a subsequence,
`exists_subseq_tendsto_integral_prod_of_tendsto_integral`), hence the premise `hN9` exactly as typed.

## Main statements

* `JointSample`, `windowDomain`, `windowChartLaw`, `windowLBMChartLaw`.
* `BG20JointChartLawInput`, `bg20ChartLawInput_of_jointChartLaws`, `hN9_of_bg20JointChartLaws`.
* `randomWalkToLBMStmt_of_markovLimit_bg20JointChartLaws`,
  `closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20JointChartLaws`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20JointChartLaws`: Theorem 2.11 and Theorems 1.4 and
  1.6 in the counted forms with the premises `h1 h2 hN4 h10` and `BG20JointChartLawInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- A sample of the joint limit: field coordinates, the coordinate `E`, the curve and the family of walk laws. -/
abbrev JointSample : Type :=
  (((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily

/-- The domain `U` of the window `(a, u, b)` of the curve `η` (Berestycki–Gwynne (2020), proof of Lemma 7.18): the
connected component of the interior of `η([a, b])` containing `η(u)`. -/
def windowDomain (η : C(ℝ, ℂ)) (a u b : ℝ) : Set ℂ :=
  connectedComponentIn (interior (η '' Icc a b)) (η u)

theorem isOpen_windowDomain (η : C(ℝ, ℂ)) (a u b : ℝ) : IsOpen (windowDomain η a u b) :=
  isOpen_interior.connectedComponentIn

/-- The chart law of the window `(a, u, b)` of a joint-limit sample `q` for the inverse chart map `ψ`: the image of
the limiting law at `η(u)` under "stop at the exit from `U` and apply `ψ`" (the law `P^D_0` of Berestycki–Gwynne
(2020), (7.34), when `ψ` extends `φ⁻¹`). -/
noncomputable def windowChartLaw (a u b : ℝ) (ψ : C(ℂ, ℂ)) (q : JointSample) : Measure (ContinuousPath ℂ) :=
  chartLaw q.2 (q.1.2 u) (windowDomain q.1.2 a u b) ψ

/-- The chart image, for the window `(a, u, b)` and the inverse chart map `ψ`, of the Liouville Brownian law of the
field of the joint-limit sample `q` from `η(u)`. -/
noncomputable def windowLBMChartLaw (γ a u b : ℝ) (ψ : C(ℂ, ℂ)) (q : JointSample) : Measure (ContinuousPath ℂ) :=
  chartLaw (lbmPathLawField γ q.1.1.1) (q.1.2 u) (windowDomain q.1.2 a u b) ψ

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit).** In the setting of the premise `hN9` of `randomWalkToLBMStmt_of_markovLimit_derived`, let `ν''` be a weak
limit of the joint laws of the field coordinates, the coordinate `E`, the curve and the interpolated walk law, which
is almost surely a linear time change of the Liouville Brownian law field. For times
`a < u < b < a' < u' < b'` there are a measurable space `F`, a measurable kernel `K` on `F`, inverse chart maps
`ψ`, `ψ'` and chart fields `hD`, `hD'` of the two windows such that

* the window chart laws depend measurably on the sample;
* (Lemma 7.20 without the time change) almost surely the chart image of the Liouville Brownian law of the field
  from `η(u)` is `K (hD)`, under which almost every path starts at `0` and leaves the unit disc, and likewise for
  the second window;
* (Lemma 7.21) the pairs (chart field, window chart law) of the two windows are independent.

In Berestycki–Gwynne, `ψ` is a continuous extension to `ℂ` of the inverse of the conformal map
`φ : 𝔻 → windowDomain η a u b` with `φ(0) = η(u)` (a homeomorphism of the closures by Pommerenke (1992),
Theorem 2.6, since the boundary is a Jordan curve by the flow-line construction of space-filling SLE), `hD` is the
field `h ∘ φ + Q log |φ'|` on `𝔻`, and `K (hD)` is the law of the Liouville Brownian motion of `hD` from `0`
stopped upon hitting `∂𝔻`, time-changed by the deterministic normalization of `lbmPathLawField`. The identity of
the chart image is the coordinate change of Liouville Brownian motion (Berestycki (2015), Theorem 1.3) and the
independence is Lemma 7.21 (from Duplantier–Miller–Sheffield, Theorem 1.9). Their walk runs at the raw speed `ε⁻¹`;
along a further subsequence `ε m_ε` tends to a deterministic positive limit, and the window chart laws for the two
normalizations differ by the corresponding deterministic time change (`chartLaw_eq_map_timeScalePath`), which
preserves the independence. -/
def BG20JointChartLawInput (𝒮 : SpaceFillingSLEModel) : Prop :=
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
    ∃ (F : Type) (_ : MeasurableSpace F) (K : F → Measure (ContinuousPath ℂ))
      (ψ ψ' : JointSample → C(ℂ, ℂ)) (hD hD' : JointSample → F),
      Measurable K ∧ Measurable hD ∧ Measurable hD' ∧
      Measurable (fun q => windowChartLaw a u b (ψ q) q) ∧
      Measurable (fun q => windowChartLaw a' u' b' (ψ' q) q) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (ψ q) q = K (hD q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (ψ' q) q = K (hD' q)) ∧
      (∀ᵐ q ∂ν'', ∀ᵐ f ∂K (hD q), f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤) ∧
      (∀ᵐ q ∂ν'', ∀ᵐ f ∂K (hD' q), f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤) ∧
      IndepFun (fun q => (hD q, windowChartLaw a u b (ψ q) q))
        (fun q => (hD' q, windowChartLaw a' u' b' (ψ' q) q)) ν''

/-- The chart input on the joint limit implies `BG20ChartLawInput`: extract a joint subsequential limit `ν₂` with
the curve (`exists_subseq_tendsto_integral_prod_of_tendsto_integral`), transfer the time-change premise from `ν'`
to `ν₂`, apply the input to `ν₂` and the windows `(0, 1, 2)` and `(3, 4, 5)`, and take `Ω₂ = ν₂` with the projection
forgetting the curve. -/
theorem bg20ChartLawInput_of_jointChartLaws {𝒮 : SpaceFillingSLEModel}
    (hJ : BG20JointChartLawInput 𝒮) : BG20ChartLawInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have hDm : Measurable fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) := (measurable_pairJ_top.comp hH).prodMk hE
  obtain ⟨φ, hφ, ν₂, hν₂, hlim, hmap⟩ := exists_subseq_tendsto_integral_prod_of_tendsto_integral hDm hη'
    (fun n => aemeasurable_interpWalkLaw hS hη' hae (hε0 n)) hconv
  have hpr : Measurable fun q : JointSample => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hspeed₂ : ∀ᵐ q ∂ν₂, ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z := by
    rw [← hmap] at hspeed
    exact ae_of_ae_map hpr.aemeasurable hspeed
  obtain ⟨F, mF, K, ψ, ψ', hD, hD', hK, hhD, hhD', hm, hm', hb, hb', hk, hk', hind⟩ :=
    hJ γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE (fun k => ε (φ k)) (fun k => hε0 (φ k))
      (hε.comp hφ.tendsto_atTop) ν₂ hν₂ hlim hspeed₂ 0 1 2 3 4 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  refine ⟨JointSample, inferInstance, ν₂, hν₂, fun q => (q.1.1, q.2), F, mF, K,
    ![fun q => q.1.2 1, fun q => q.1.2 4], ![fun q => windowDomain q.1.2 0 1 2, fun q => windowDomain q.1.2 3 4 5],
    ![ψ, ψ'], ![hD, hD'], hpr, hmap, hK, Fin.forall_fin_two.2 ⟨hhD, hhD'⟩,
    Fin.forall_fin_two.2 ⟨fun q => isOpen_windowDomain _ _ _ _, fun q => isOpen_windowDomain _ _ _ _⟩,
    Fin.forall_fin_two.2 ⟨hm, hm'⟩, Fin.forall_fin_two.2 ⟨hb, hb'⟩, Fin.forall_fin_two.2 ⟨hk, hk'⟩, hind⟩

/-- **Berestycki–Gwynne (2020), Lemma 7.18, from Lemmas 7.20 and 7.21 on the joint limit.** The premise `hN9` of
`randomWalkToLBMStmt_of_markovLimit_derived`, exactly as typed, from `BG20JointChartLawInput`. -/
theorem hN9_of_bg20JointChartLaws {𝒮 : SpaceFillingSLEModel} (hJ : BG20JointChartLawInput 𝒮) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z :=
  hN9_of_bg20ChartLaws (bg20ChartLawInput_of_jointChartLaws hJ)

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) with Lemma 7.18 reduced to Lemmas 7.20 and 7.21 on the
joint limit.** The remaining premises are `h1 h2 hN4 h10` and `BG20JointChartLawInput`. -/
theorem randomWalkToLBMStmt_of_markovLimit_bg20JointChartLaws {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hJ : BG20JointChartLawInput 𝒮) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_bg20ChartLaws h1 h2 hN4 h10 (bg20ChartLawInput_of_jointChartLaws hJ)

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20JointChartLawInput` (Lemma 7.20 without the time change, and Lemma 7.21, on the joint limit); the
remaining premises are `h1 h2 hN4 h10 hJ`. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20JointChartLaws
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hJ : BG20JointChartLawInput 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20ChartLaws ν h1 h2 hN4 h10
    (bg20ChartLawInput_of_jointChartLaws hJ)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20JointChartLawInput` (Lemma 7.20 without the time change, and Lemma 7.21, on the joint limit); the
remaining premises are `h1 h2 hN4 h10 hJ`. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20JointChartLaws
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hJ : BG20JointChartLawInput 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20ChartLaws ν h1 h2 hN4 h10
    (bg20ChartLawInput_of_jointChartLaws hJ)

end MatedCRT
