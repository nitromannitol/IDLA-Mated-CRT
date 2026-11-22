import MatedCRT.FirstPass.Derived.HN8OfRevuzLintegralGlue
import LatticeProb.Prob.IndependentDetermination

/-!
# The time-change constant of the joint limit is deterministic, from two independent local recoveries

The premise `hN9` of `randomWalkToLBMStmt_of_markovLimit_derived` (and of its refinements
`randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8` and the counted forms of Theorems 1.4 and 1.6 built on it)
is the statement of Berestycki–Gwynne (2020), Lemma 7.18: if almost surely a subsequential joint limit of the field
coordinates and the interpolated walk laws is a linear time change of the Liouville Brownian law field, then the
constant of the time change is deterministic.

Berestycki–Gwynne prove Lemma 7.18 from three lemmas. On the joint subsequential limit `(h, η, P)` they attach to
two disjoint time windows of the curve two triples (the field and the curve in the window, seen in a conformal chart
of the unit disk, and the chart image of the limiting path stopped at its exit from the window), and show:

* Lemma 7.20: the chart image of the limiting path is the chart Liouville Brownian motion time-changed by the same
  constant `c` (from the LQG coordinate change of Liouville Brownian motion, Berestycki (2015), Theorem 1.3, and of
  the adjacency graph of the cells);
* Lemma 7.21: the two triples are independent (from the independence of the past and future curve-decorated
  quantum surfaces, Duplantier–Miller–Sheffield, Theorem 1.9, and the locality of the walk on the mated-CRT map);
* Lemma 7.22: the laws of a Liouville Brownian motion and of its time change by a different constant, jointly with
  the field, are mutually singular, so that `c` is a measurable function of each triple.

The last sentence of their proof then concludes: `c` is independent of itself, hence almost surely constant.

The literature content of Lemmas 7.20–7.22 is the input `BG20LocalSpeedRecoveryInput`: in the setting of `hN9`, on
some probability space mapping onto the limit law `ν'` there are two independent random elements (the two triples)
and measurable real functions of them, each of which equals every admissible time-change constant almost surely.
This file proves the rest: by the zero-one argument `LatticeProb.exists_ae_eq_const_of_indepFun_of_ae_eq`
(two independent almost surely equal random variables are almost surely constant), the constant is deterministic;
the event that the limiting family is the time change of the Liouville Brownian law field with a given constant is
measurable (`measurableSet_forall_eq_timeScalePathKernel_lbmPathLawField`); and `hN9` exactly as typed follows from
the input (`hN9_of_bg20LocalSpeedRecovery`).

## Main statements

* `BG20LocalSpeedRecoveryInput`: the input (Berestycki–Gwynne (2020), Lemmas 7.20, 7.21 and 7.22).
* `hN9_of_bg20LocalSpeedRecovery`: the premise `hN9` from `BG20LocalSpeedRecoveryInput`.
* `bg20LocalSpeedRecoveryInput_of_hN9`: conversely, `hN9` implies `BG20LocalSpeedRecoveryInput`, so the input is
  no stronger than `hN9`; it isolates the literature content of the proof of Lemma 7.18.
* `randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery`,
  `closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery`: Theorem 2.11 and Theorems 1.4 and
  1.6 in the counted forms, with the premises `h1 h2 hN4 h10` and `BG20LocalSpeedRecoveryInput` in place of `hN9`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- The event that the limiting family `p.2` is the time change by the constant `c` of the Liouville Brownian law
field at the field coordinates `p.1.1` is measurable. -/
theorem measurableSet_forall_eq_timeScalePathKernel_lbmPathLawField (γ : ℝ) (c : ℝ≥0) :
    MeasurableSet {p : ((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily |
      ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z} := by
  let g : C(ProbabilityMeasure (ContinuousPath ℂ), ProbabilityMeasure (ContinuousPath ℂ)) :=
    ⟨fun μ => μ.map (LatticeProb.timeScalePath c),
      ProbabilityMeasure.continuous_map (ContinuousMap.continuous_precomp _)⟩
  have hF : Measurable fun p : ((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily =>
      g.comp (lbmPathLawField γ p.1.1) :=
    (ContinuousMap.continuous_postcomp g).measurable.comp
      ((measurable_lbmPathLawField γ).comp (measurable_fst.comp measurable_fst))
  convert measurableSet_eq_fun measurable_snd hF using 1
  ext p
  exact (ContinuousMap.ext_iff (f := p.2) (g := g.comp (lbmPathLawField γ p.1.1))).symm

/-- **Literature input (Berestycki–Gwynne (2020), Lemmas 7.20, 7.21 and 7.22).** In the setting of the premise
`hN9` of `randomWalkToLBMStmt_of_markovLimit_derived` (a valid environment `S`, measurable versions `η'` and `H` of
its curve and field, a measurable `E`, cell sizes `ε n → 0`, and a weak limit `ν'` of the joint laws of the field
coordinates and the interpolated walk laws, which is almost surely a linear time change of the Liouville Brownian
law field), there are a probability space `(Ω₂, P₂)`, a measurable map `pr` with `pr_* P₂ = ν'`, two
independent random elements `X₁`, `X₂` of measurable spaces `T₁`, `T₂`, and measurable `g₁ : T₁ → ℝ`,
`g₂ : T₂ → ℝ`, such that almost surely every admissible time-change constant of `pr ω₂` equals both `g₁ (X₁ ω₂)`
and `g₂ (X₂ ω₂)`.

In Berestycki–Gwynne, `Ω₂` carries the joint subsequential limit `(h, η, P)` and `pr` forgets the curve; `X₁` and
`X₂` are the triples `(h^D, η^D, P^D_0)` of two disjoint time windows, which are independent (Lemma 7.21), and
`g₁`, `g₂` recover the constant from a triple (Lemma 7.20 and the mutual singularity of Lemma 7.22, whose
elementary part is `LatticeProb.mutuallySingular_map_graph_of_ae_ne`). Their walk runs at the raw speed
`ε⁻¹`, while `interpWalkLaw` is normalized by the median `m_ε`; along a further subsequence `ε m_ε` tends to a
deterministic positive limit (end of the proof of their Theorem 1.2), which multiplies both recovered constants by
the same deterministic factor. -/
def BG20LocalSpeedRecoveryInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
    (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
        (𝓝 (∫ p, f p ∂ν'))) →
    (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (_ : IsProbabilityMeasure P₂)
      (pr : Ω₂ → ((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily)
      (T₁ T₂ : Type) (_ : MeasurableSpace T₁) (_ : MeasurableSpace T₂) (X₁ : Ω₂ → T₁) (X₂ : Ω₂ → T₂)
      (g₁ : T₁ → ℝ) (g₂ : T₂ → ℝ),
      Measurable pr ∧ P₂.map pr = ν' ∧ Measurable X₁ ∧ Measurable X₂ ∧ IndepFun X₁ X₂ P₂ ∧
      Measurable g₁ ∧ Measurable g₂ ∧
      ∀ᵐ ω₂ ∂P₂, ∀ c : ℝ≥0, c ≠ 0 →
        (∀ z, (pr ω₂).2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ (pr ω₂).1.1) z) →
        (c : ℝ) = g₁ (X₁ ω₂) ∧ (c : ℝ) = g₂ (X₂ ω₂)

/-- **Berestycki–Gwynne (2020), Lemma 7.18, from Lemmas 7.20–7.22.** The premise `hN9` of
`randomWalkToLBMStmt_of_markovLimit_derived`, exactly as typed, follows from `BG20LocalSpeedRecoveryInput`: the two
recoveries `g₁ ∘ X₁`, `g₂ ∘ X₂` are independent and agree almost surely, so the recovered constant is independent
of itself and hence almost surely equal to a deterministic `c₀ > 0`; the event of the time change by `c₀` is
measurable, so it transfers from `P₂` to `ν' = pr_* P₂`. -/
theorem hN9_of_bg20LocalSpeedRecovery {𝒮 : SpaceFillingSLEModel}
    (hLoc : BG20LocalSpeedRecoveryInput 𝒮) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  obtain ⟨Ω₂, _, P₂, _, pr, T₁, T₂, _, _, X₁, X₂, g₁, g₂, hpr, hmap, hX₁, -, hind, hg₁, hg₂, hrec⟩ :=
    hLoc γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  have hspeed₂ : ∀ᵐ ω₂ ∂P₂, ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, (pr ω₂).2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ (pr ω₂).1.1) z := by
    rw [← hmap] at hspeed
    exact ae_of_ae_map hpr.aemeasurable hspeed
  have hG : (fun ω₂ => g₁ (X₁ ω₂)) =ᵐ[P₂] fun ω₂ => g₂ (X₂ ω₂) := by
    filter_upwards [hspeed₂, hrec] with ω₂ hω₂ hr
    obtain ⟨c, hc, hcz⟩ := hω₂
    obtain ⟨h1, h2⟩ := hr c hc hcz
    rw [← h1, ← h2]
  obtain ⟨a, ha⟩ := LatticeProb.exists_ae_eq_const_of_indepFun_of_ae_eq (hg₁.comp hX₁)
    (hind.comp hg₁ hg₂) hG
  have hall : ∀ᵐ ω₂ ∂P₂, ∃ c : ℝ≥0, c ≠ 0 ∧ (c : ℝ) = a ∧
      ∀ z, (pr ω₂).2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ (pr ω₂).1.1) z := by
    filter_upwards [hspeed₂, hrec, ha] with ω₂ hω₂ hr hω
    obtain ⟨c, hc, hcz⟩ := hω₂
    exact ⟨c, hc, (hr c hc hcz).1.trans hω, hcz⟩
  obtain ⟨_, c₀, hc₀, hc₀a, -⟩ := hall.exists
  refine ⟨c₀, hc₀, ?_⟩
  rw [← hmap]
  refine (ae_map_iff hpr.aemeasurable
    (measurableSet_forall_eq_timeScalePathKernel_lbmPathLawField γ c₀)).2 ?_
  filter_upwards [hall] with ω₂ hω₂
  obtain ⟨c, -, hca, hcz⟩ := hω₂
  have hcc : c = c₀ := NNReal.coe_injective (hca.trans hc₀a.symm)
  rw [← hcc]
  exact hcz

/-- **`BG20LocalSpeedRecoveryInput` is no stronger than `hN9`.** Conversely, `hN9` implies the input: take
`Ω₂ = ν'`, the identity for `pr`, constant `X₁ = X₂` and `g₁ = g₂ = c₀`. Every admissible constant `c` equals `c₀`
almost surely, since both are the ratio of the exit-time medians from `B_{1/2}` of the Liouville Brownian law field
and of the limiting family at `0` (`coe_eq_medianOf_div_of_map_timeScalePath`), and the first median is nonzero for
almost every value of the data (`ae_medianOf_exitCdf_lbmPathLawField_ne_zero`, transferred to `ν'` through its data
marginal `map_fst_eq_map_of_tendsto_integral`). -/
theorem bg20LocalSpeedRecoveryInput_of_hN9 {𝒮 : SpaceFillingSLEModel}
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    BG20LocalSpeedRecoveryInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  haveI := hS.isProbabilityMeasure
  obtain ⟨c₀, hc₀, hc₀ae⟩ :=
    hN9 γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  have hDm : Measurable fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) := (measurable_pairJ_top.comp hH).prodMk hE
  have hfst : ν'.map Prod.fst = S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hDm hconv
  have hmed := FirstPass.Derived.ae_medianOf_exitCdf_lbmPathLawField_ne_zero hγ hγ2 hS hH hrep hE
  rw [← hfst] at hmed
  have hmed' : ∀ᵐ p ∂ν', medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2))
      (lbmPathLawField γ p.1.1 0 : Measure (ContinuousPath ℂ))) ≠ 0 :=
    ae_of_ae_map measurable_fst.aemeasurable hmed
  refine ⟨((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily, inferInstance, ν', hν', id, Unit, Unit,
    inferInstance, inferInstance, fun _ => (), fun _ => (), fun _ => (c₀ : ℝ), fun _ => (c₀ : ℝ),
    measurable_id, Measure.map_id, measurable_const, measurable_const, indepFun_const_left () _,
    measurable_const, measurable_const, ?_⟩
  filter_upwards [hc₀ae, hmed'] with p hp hm c hc hcz
  have hlaw : ∀ a : ℝ≥0, (∀ z, p.2 z = LatticeProb.timeScalePathKernel a (lbmPathLawField γ p.1.1) z) →
      (p.2 0 : Measure (ContinuousPath ℂ)) =
        (lbmPathLawField γ p.1.1 0 : Measure (ContinuousPath ℂ)).map (timeScalePath a) := by
    intro a ha
    rw [ha 0]
    rfl
  have h1 := coe_eq_medianOf_div_of_map_timeScalePath (Metric.ball (0 : ℂ) (1 / 2)) Metric.isOpen_ball hc _ _
    (hlaw c hcz) hm
  have h2 := coe_eq_medianOf_div_of_map_timeScalePath (Metric.ball (0 : ℂ) (1 / 2)) Metric.isOpen_ball hc₀ _ _
    (hlaw c₀ hp) hm
  exact ⟨h1.trans h2.symm, h1.trans h2.symm⟩

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) with Lemma 7.18 reduced to Lemmas 7.20–7.22.**
`randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8` with the premise `hN9` supplied by
`hN9_of_bg20LocalSpeedRecovery`; the remaining premises are `h1 h2 hN4 h10` and `BG20LocalSpeedRecoveryInput`. -/
theorem randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hLoc : BG20LocalSpeedRecoveryInput 𝒮) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_derived_noHN5_noHN8 h1 h2 hN4 h10 (hN9_of_bg20LocalSpeedRecovery hLoc)

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with `h11` supplied by
`randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery`. The premise `hN9` of
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` (Berestycki–Gwynne (2020), Lemma 7.18) is
replaced by `BG20LocalSpeedRecoveryInput` (Lemmas 7.20–7.22); the remaining premises are `h1 h2 hN4 h10 hLoc`. Same
conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hLoc : BG20LocalSpeedRecoveryInput 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2 hN4 h10
    (hN9_of_bg20LocalSpeedRecovery hLoc)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with `h11` supplied by
`randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery`. The premise `hN9` of
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` (Berestycki–Gwynne (2020), Lemma 7.18) is
replaced by `BG20LocalSpeedRecoveryInput` (Lemmas 7.20–7.22); the remaining premises are `h1 h2 hN4 h10 hLoc`. Same
conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hLoc : BG20LocalSpeedRecoveryInput 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν h1 h2 hN4 h10
    (hN9_of_bg20LocalSpeedRecovery hLoc)

end MatedCRT
