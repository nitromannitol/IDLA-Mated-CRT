import MatedCRT.FirstPass.Derived.HN9OfLocalSpeedRecovery
import MatedCRT.FirstPass.Derived.JointSubsequentialLimit

/-!
# Lemma 7.18 from Lemmas 7.20–7.22 stated on the joint limit of the field, the curve and the walk laws

Berestycki–Gwynne (2020) prove Lemma 7.18 on a subsequential limit in law of the triple `(h, η, P^ε)` of the
field, the curve and the walk law. The premise `hN9` of `randomWalkToLBMStmt_of_markovLimit_derived` concerns a
weak limit `ν'` of the pairs (field coordinates, interpolated walk law) only, without the curve. This file adds the
curve: the joint laws of (field coordinates, curve, walk law) along the same cell sizes are tight (the first two
coordinates have a fixed law, and the laws of (field coordinates, walk law) converge), so by Prokhorov's theorem
they converge along a subsequence to a law `ν''` whose image under forgetting the curve is `ν'`
(`exists_subseq_tendsto_integral_prod_of_tendsto_integral`).

The input `BG20JointLimitSpeedRecoveryInput` is then the conclusion of Lemmas 7.20–7.22 on such a joint limit
itself: there are two independent measurable observables of the joint limit (in Berestycki–Gwynne, the triples of
two disjoint time windows of the curve; Lemma 7.21) and measurable real functions of them which equal every
admissible time-change constant almost surely (Lemmas 7.20 and 7.22). It implies `BG20LocalSpeedRecoveryInput`
(`bg20LocalSpeedRecoveryInput_of_jointLimit`) and hence `hN9` exactly as typed.

## Main statements

* `BG20JointLimitSpeedRecoveryInput`, `bg20LocalSpeedRecoveryInput_of_jointLimit`,
  `hN9_of_bg20JointLimitSpeedRecovery`.
* `randomWalkToLBMStmt_of_markovLimit_bg20JointLimitSpeedRecovery`,
  `closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20JointLimitSpeedRecovery`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20JointLimitSpeedRecovery`: Theorem 2.11 and
  Theorems 1.4 and 1.6 in the counted forms with the premises `h1 h2 hN4 h10` and
  `BG20JointLimitSpeedRecoveryInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- **Literature input (Berestycki–Gwynne (2020), Lemmas 7.20, 7.21 and 7.22, on the joint limit).** In the setting
of the premise `hN9` of `randomWalkToLBMStmt_of_markovLimit_derived`, let `ν''` be a weak limit of the joint laws of
the field coordinates, the coordinate `E`, the curve and the interpolated walk law, which is almost surely a linear
time change of the Liouville Brownian law field. Then there are two independent measurable observables `X₁`, `X₂`
of the joint limit and measurable `g₁`, `g₂` such that almost surely every admissible time-change constant equals
both `g₁ (X₁ q)` and `g₂ (X₂ q)`.

In Berestycki–Gwynne, `X₁` and `X₂` are the triples `(h^D, η^D, P^D_0)` of two disjoint time windows of the curve,
which are independent (Lemma 7.21), and `g₁`, `g₂` recover the constant from a triple (Lemma 7.20 and the mutual
singularity of Lemma 7.22). Their walk runs at the raw speed `ε⁻¹`, while `interpWalkLaw` is normalized by the median
`m_ε`; along a further subsequence `ε m_ε` tends to a deterministic positive limit (end of the proof of their
Theorem 1.2), which multiplies both recovered constants by the same deterministic factor. -/
def BG20JointLimitSpeedRecoveryInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure ((((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily), IsProbabilityMeasure ν'' →
    (∀ f : ((((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∃ (T₁ T₂ : Type) (_ : MeasurableSpace T₁) (_ : MeasurableSpace T₂)
      (X₁ : (((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily → T₁)
      (X₂ : (((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily → T₂)
      (g₁ : T₁ → ℝ) (g₂ : T₂ → ℝ),
      Measurable X₁ ∧ Measurable X₂ ∧ IndepFun X₁ X₂ ν'' ∧ Measurable g₁ ∧ Measurable g₂ ∧
      ∀ᵐ q ∂ν'', ∀ c : ℝ≥0, c ≠ 0 →
        (∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
        (c : ℝ) = g₁ (X₁ q) ∧ (c : ℝ) = g₂ (X₂ q)

/-- The input on the joint limit implies `BG20LocalSpeedRecoveryInput`: given the weak limit `ν'`, extract a joint
subsequential limit `ν''` with the curve (`exists_subseq_tendsto_integral_prod_of_tendsto_integral`), transfer the
time-change premise from `ν'` to `ν''`, and take `Ω₂ = ν''` with the projection forgetting the curve. -/
theorem bg20LocalSpeedRecoveryInput_of_jointLimit {𝒮 : SpaceFillingSLEModel}
    (hJoint : BG20JointLimitSpeedRecoveryInput 𝒮) : BG20LocalSpeedRecoveryInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  haveI := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have hDm : Measurable fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) := (measurable_pairJ_top.comp hH).prodMk hE
  obtain ⟨φ, hφ, ν₂, hν₂, hlim, hmap⟩ := exists_subseq_tendsto_integral_prod_of_tendsto_integral hDm hη'
    (fun n => aemeasurable_interpWalkLaw hS hη' hae (hε0 n)) hconv
  have hpr : Measurable fun q : (((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily =>
      (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hspeed₂ : ∀ᵐ q ∂ν₂, ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z := by
    rw [← hmap] at hspeed
    exact ae_of_ae_map hpr.aemeasurable hspeed
  obtain ⟨T₁, T₂, mT₁, mT₂, X₁, X₂, g₁, g₂, hX₁, hX₂, hind, hg₁, hg₂, hrec⟩ :=
    hJoint γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE (fun k => ε (φ k)) (fun k => hε0 (φ k))
      (hε.comp hφ.tendsto_atTop) ν₂ hν₂ hlim hspeed₂
  exact ⟨(((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily, inferInstance, ν₂, hν₂,
    fun q => (q.1.1, q.2), T₁, T₂, mT₁, mT₂, X₁, X₂, g₁, g₂, hpr, hmap, hX₁, hX₂, hind, hg₁, hg₂, hrec⟩

/-- **Berestycki–Gwynne (2020), Lemma 7.18, from Lemmas 7.20–7.22 on the joint limit.** The premise `hN9` of
`randomWalkToLBMStmt_of_markovLimit_derived`, exactly as typed, from `BG20JointLimitSpeedRecoveryInput`
(`bg20LocalSpeedRecoveryInput_of_jointLimit` and `hN9_of_bg20LocalSpeedRecovery`). -/
theorem hN9_of_bg20JointLimitSpeedRecovery {𝒮 : SpaceFillingSLEModel}
    (hJoint : BG20JointLimitSpeedRecoveryInput 𝒮) :
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
  hN9_of_bg20LocalSpeedRecovery (bg20LocalSpeedRecoveryInput_of_jointLimit hJoint)

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) with Lemma 7.18 reduced to Lemmas 7.20–7.22 on the
joint limit.** The remaining premises are `h1 h2 hN4 h10` and `BG20JointLimitSpeedRecoveryInput`. -/
theorem randomWalkToLBMStmt_of_markovLimit_bg20JointLimitSpeedRecovery {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hJoint : BG20JointLimitSpeedRecoveryInput 𝒮) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_jointLimit hJoint)

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20JointLimitSpeedRecoveryInput` (Lemmas 7.20–7.22 on the joint limit); the remaining premises are
`h1 h2 hN4 h10 hJoint`. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20JointLimitSpeedRecovery
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hJoint : BG20JointLimitSpeedRecoveryInput 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery ν h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_jointLimit hJoint)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20JointLimitSpeedRecoveryInput` (Lemmas 7.20–7.22 on the joint limit); the remaining premises are
`h1 h2 hN4 h10 hJoint`. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20JointLimitSpeedRecovery
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hJoint : BG20JointLimitSpeedRecoveryInput 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery ν h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_jointLimit hJoint)

end MatedCRT
