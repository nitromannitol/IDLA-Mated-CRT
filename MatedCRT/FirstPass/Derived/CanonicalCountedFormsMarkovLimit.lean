import MatedCRT.FirstPass.Derived.ConvergenceOfIDLAOfMarkovLimit
import MatedCRT.FirstPass.Derived.CanonicalNormalizedLaw
import MatedCRT.FirstPass.Derived.CanonicalHasReferenceEnvironments
import MatedCRT.FirstPass.SLERef.CanonicalScaleInvariance

/-!
# Theorems 1.4 and 1.6 at the canonical space-filling SLE model, from the Markovian time-change structure

The counted forms `MatedCRT.closed_1_4_quantumConeScaling_coneDimension_markovLimit` and
`MatedCRT.closed_1_6_quantumConeScaling_coneDimension_markovLimit` of Theorems 1.4 and 1.6 take, for a model `𝒮` of
whole-plane space-filling SLE, the normalized law `h1 : HasNormalizedSLELaw 𝒮 ν` and the three closure properties
`h2 : SLEModelClosureInput 𝒮` of its SLE predicate, and in place of Berestycki–Gwynne (2020), Theorem 1.2, the three
inputs `hN8'`, `hN5`, `hN9` of its proof. For the canonical model `ProbeMi.canonicalSLEModel ν` (curve modulo
increasing reparametrization, with a free Lebesgue-area representative):

* `h1` is `hasNormalizedSLELaw_canonicalSLEModel` under `SLECodeZeroOnlyAtOrigin ν` (for `κ > 4`, `ν κ`-almost
  every code is the code of a path that visits `0` only at time `0`);
* closure under increasing reparametrization and monotonicity of independence are
  `ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`;
* scale invariance `SLEScaleInvarianceInput` stays a binder, or is supplied by `ProbeMi.canonicalSLEModel_scale` from
  the scale invariance `ProbeMi.SLECodeScaleInvariant ν` of the code law (the `_of_codeScale` forms).

The `_of_coupling` forms replace the reference environments `HasReferenceEnvironments` by the hypotheses of
`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`: mating-of-trees couplings on the sample
space `ℝ` whose Lebesgue-parametrized curve has code law `ν (16/γ²)`, and the fixed-start convergence and strict
monotonicity of the dyadic Liouville clocks of the normalized whole-plane Gaussian free field.

These are the forms of `CanonicalCountedForms` and `CanonicalCountedFormsCodeScale` with the binder `hBGref`
(Berestycki–Gwynne (2020), Theorem 1.2) replaced at its position by
* `hN8'`: Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant
  (Garban–Rhodes–Vargas; a literature input);
* `hN5`: subsequential limits of the interpolated walk laws are Markovian time changes of Brownian motion
  (Berestycki–Gwynne (2020), Lemma 7.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki–Gwynne (2020), Lemma 7.18).

## Main statements

* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical`: Theorems 1.4 and 1.6 at the canonical model
  from `hZO hscale hN4 h10 hN8' hN5 hN9`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling`: the same from
  `hZO hscale hN4 hcpl hfix hfixsm hN8' hN5 hN9`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale`: Theorems 1.4 and 1.6 at the
  canonical model from `hZO hSC hN4 h10 hN8' hN5 hN9`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_of_codeScale`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_of_codeScale`: the same from
  `hZO hSC hN4 hcpl hfix hfixsm hN8' hN5 hN9`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **Theorem 1.4 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_4_quantumConeScaling_coneDimension_markovLimit`, with the normalized law supplied by
`hasNormalizedSLELaw_canonicalSLEModel` and the reparametrization and independence-monotonicity clauses by
`ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`. Remaining binders:
* `hZO`: for `κ > 4`, `ν κ`-almost every code is the code of a path that visits `0` only at time `0`; for the law of
  whole-plane space-filling SLE parametrized by Lebesgue measure with `η 0 = 0` this is what one expects from
  Duplantier–Miller–Sheffield (arXiv:1409.7055, p. 24) together with the translation invariance of the Lebesgue
  parametrization (Holden–Sun, Lemma 2.3);
* `hscale`: scale invariance of the SLE predicate of the model (Miller–Sheffield, *Imaginary Geometry IV*, §1.2.3);
* `hN4`: the uniform-start invariance principle for the mated-CRT map walk (Gwynne–Miller–Sheffield 2021,
  Theorem 3.4);
* `h10`: reference environments of the model;
* `hN8'`: Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant
  (Garban–Rhodes–Vargas; a literature input);
* `hN5`: subsequential limits of the interpolated walk laws are Markovian time changes of Brownian motion
  (Berestycki–Gwynne (2020), Lemma 7.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki–Gwynne (2020), Lemma 7.18). -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν))
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  MatedCRT.closed_1_4_quantumConeScaling_coneDimension_markovLimit ν
    (hasNormalizedSLELaw_canonicalSLEModel hZO)
    ⟨hscale, ProbeMi.canonicalSLEModel_reparam ν, ProbeMi.canonicalSLEModel_indepMono ν⟩ hN4 h10 hN8' hN5 hN9

/-- **Theorem 1.6 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_6_quantumConeScaling_coneDimension_markovLimit`, with the normalized law supplied by
`hasNormalizedSLELaw_canonicalSLEModel` and the reparametrization and independence-monotonicity clauses by
`ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`. Remaining binders, as in
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical`:
* `hZO`: for `κ > 4`, `ν κ`-almost every code is the code of a path that visits `0` only at time `0`; for the law of
  whole-plane space-filling SLE parametrized by Lebesgue measure with `η 0 = 0` this is what one expects from
  Duplantier–Miller–Sheffield (arXiv:1409.7055, p. 24) together with the translation invariance of the Lebesgue
  parametrization (Holden–Sun, Lemma 2.3);
* `hscale`: scale invariance of the SLE predicate of the model (Miller–Sheffield, *Imaginary Geometry IV*, §1.2.3);
* `hN4`: the uniform-start invariance principle for the mated-CRT map walk (Gwynne–Miller–Sheffield 2021,
  Theorem 3.4);
* `h10`: reference environments of the model;
* `hN8'`: Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant
  (Garban–Rhodes–Vargas; a literature input);
* `hN5`: subsequential limits of the interpolated walk laws are Markovian time changes of Brownian motion
  (Berestycki–Gwynne (2020), Lemma 7.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki–Gwynne (2020), Lemma 7.18). -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν))
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  MatedCRT.closed_1_6_quantumConeScaling_coneDimension_markovLimit ν
    (hasNormalizedSLELaw_canonicalSLEModel hZO)
    ⟨hscale, ProbeMi.canonicalSLEModel_reparam ν, ProbeMi.canonicalSLEModel_indepMono ν⟩ hN4 h10 hN8' hN5 hN9

/-- **Theorem 1.4 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical` with the reference environments `h10` supplied by
`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`. Remaining binders: `hZO`, `hscale`,
`hN4`, `hN8'`, `hN5`, `hN9` as in `closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν))
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hfix : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T))
    (hfixsm : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
          StrictMono (LatticeProb.limitAfterPositiveTimes
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical ν hZO hscale hN4
    (MatedCRT.Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix hfixsm)
    hN8' hN5 hN9

/-- **Theorem 1.6 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical` with the reference environments `h10` supplied by
`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`. Remaining binders: `hZO`, `hscale`,
`hN4`, `hN8'`, `hN5`, `hN9` as in `closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν))
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hfix : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T))
    (hfixsm : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
          StrictMono (LatticeProb.limitAfterPositiveTimes
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical ν hZO hscale hN4
    (MatedCRT.Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix hfixsm)
    hN8' hN5 hN9

/-- **Theorem 1.4 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_4_quantumConeScaling_coneDimension_markovLimit`, with the normalized law supplied by
`hasNormalizedSLELaw_canonicalSLEModel`, the reparametrization and independence-monotonicity clauses by
`ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`, and the scale-invariance clause by
`ProbeMi.canonicalSLEModel_scale`. Remaining binders:
* `hZO`: for `κ > 4`, `ν κ`-almost every code is the code of a path that visits `0` only at time `0`; for the law of
  whole-plane space-filling SLE parametrized by Lebesgue measure with `η 0 = 0` this is what one expects from
  Duplantier–Miller–Sheffield (arXiv:1409.7055, p. 24) together with the translation invariance of the Lebesgue
  parametrization (Holden–Sun, Lemma 2.3);
* `hSC`: scale invariance of the code law, a hypothesis on `ν`: whenever a random continuous path `ηL` has code law
  `ν κ` (`4 < κ`), so has its area-preserving rescaling `s ↦ r ηL (s / r ^ 2)` for every `r > 0`; its motivation is
  the scale invariance of whole-plane space-filling SLE modulo time parametrization (Miller–Sheffield, *Imaginary
  Geometry IV*, §1.2.3);
* `hN4`: the uniform-start invariance principle for the mated-CRT map walk (Gwynne–Miller–Sheffield 2021,
  Theorem 3.4);
* `h10`: reference environments of the model;
* `hN8'`: Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant
  (Garban–Rhodes–Vargas; a literature input);
* `hN5`: subsequential limits of the interpolated walk laws are Markovian time changes of Brownian motion
  (Berestycki–Gwynne (2020), Lemma 7.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki–Gwynne (2020), Lemma 7.18). -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hSC : ProbeMi.SLECodeScaleInvariant ν)
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 h10 hN8' hN5 hN9

/-- **Theorem 1.6 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_6_quantumConeScaling_coneDimension_markovLimit`, with the normalized law supplied by
`hasNormalizedSLELaw_canonicalSLEModel`, the reparametrization and independence-monotonicity clauses by
`ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`, and the scale-invariance clause by
`ProbeMi.canonicalSLEModel_scale`. Remaining binders, as in
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale`:
* `hZO`: for `κ > 4`, `ν κ`-almost every code is the code of a path that visits `0` only at time `0`; for the law of
  whole-plane space-filling SLE parametrized by Lebesgue measure with `η 0 = 0` this is what one expects from
  Duplantier–Miller–Sheffield (arXiv:1409.7055, p. 24) together with the translation invariance of the Lebesgue
  parametrization (Holden–Sun, Lemma 2.3);
* `hSC`: scale invariance of the code law, a hypothesis on `ν`: whenever a random continuous path `ηL` has code law
  `ν κ` (`4 < κ`), so has its area-preserving rescaling `s ↦ r ηL (s / r ^ 2)` for every `r > 0`; its motivation is
  the scale invariance of whole-plane space-filling SLE modulo time parametrization (Miller–Sheffield, *Imaginary
  Geometry IV*, §1.2.3);
* `hN4`: the uniform-start invariance principle for the mated-CRT map walk (Gwynne–Miller–Sheffield 2021,
  Theorem 3.4);
* `h10`: reference environments of the model;
* `hN8'`: Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant
  (Garban–Rhodes–Vargas; a literature input);
* `hN5`: subsequential limits of the interpolated walk laws are Markovian time changes of Brownian motion
  (Berestycki–Gwynne (2020), Lemma 7.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki–Gwynne (2020), Lemma 7.18). -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hSC : ProbeMi.SLECodeScaleInvariant ν)
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 h10 hN8' hN5 hN9

/-- **Theorem 1.4 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling` with the scale-invariance clause
supplied by `ProbeMi.canonicalSLEModel_scale`. Remaining binders: `hZO`, `hSC`, `hN4`, `hN8'`, `hN5`, `hN9` as in
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_of_codeScale
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hSC : ProbeMi.SLECodeScaleInvariant ν)
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hfix : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T))
    (hfixsm : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
          StrictMono (LatticeProb.limitAfterPositiveTimes
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 hcpl hfix hfixsm hN8' hN5 hN9

/-- **Theorem 1.6 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling` with the scale-invariance clause
supplied by `ProbeMi.canonicalSLEModel_scale`. Remaining binders: `hZO`, `hSC`, `hN4`, `hN8'`, `hN5`, `hN9` as in
`closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_codeScale`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling_of_codeScale
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hSC : ProbeMi.SLECodeScaleInvariant ν)
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hfix : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T))
    (hfixsm : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
          StrictMono (LatticeProb.limitAfterPositiveTimes
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t))
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid (ProbeMi.canonicalSLEModel ν) γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_canonical_of_coupling ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 hcpl hfix hfixsm hN8' hN5 hN9

end MatedCRT.FirstPass.Derived

