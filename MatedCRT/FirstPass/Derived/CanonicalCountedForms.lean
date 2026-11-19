import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20Reference
import MatedCRT.FirstPass.Derived.CanonicalNormalizedLaw
import MatedCRT.FirstPass.Derived.CanonicalHasReferenceEnvironments

/-!
# Theorems 1.4 and 1.6 at the canonical space-filling SLE model

The counted forms `closed_1_4_quantumConeScaling_coneDimension_bg20ref` and
`closed_1_6_quantumConeScaling_coneDimension_bg20ref` of Theorems 1.4 and 1.6 take, for a model `𝒮` of whole-plane
space-filling SLE, the normalized law `h1 : HasNormalizedSLELaw 𝒮 ν` and the three closure properties
`h2 : SLEModelClosureInput 𝒮` of its SLE predicate. For the canonical model `ProbeMi.canonicalSLEModel ν` (curve
modulo increasing reparametrization, with a free Lebesgue-area representative):

* `h1` is `hasNormalizedSLELaw_canonicalSLEModel` under `SLECodeZeroOnlyAtOrigin ν` (for `κ > 4`, `ν κ`-almost
  every code is the code of a path that visits `0` only at time `0`);
* closure under increasing reparametrization and monotonicity of independence are
  `ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`;
* scale invariance `SLEScaleInvarianceInput` stays a binder.

The `_of_coupling` forms replace the reference environments `HasReferenceEnvironments` by the hypotheses of
`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`: mating-of-trees couplings on the sample
space `ℝ` whose Lebesgue-parametrized curve has code law `ν (16/γ²)`, and the fixed-start convergence and strict
monotonicity of the dyadic Liouville clocks of the normalized whole-plane Gaussian free field.

## Main statements

* `closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical`,
  `closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical`: Theorems 1.4 and 1.6 at the canonical model
  from `hZO hscale hN4 h10 hBGref`.
* `closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling`,
  `closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling`: the same from
  `hZO hscale hN4 hcpl hfix hfixsm hBGref`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Theorem 1.4 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_4_quantumConeScaling_coneDimension_bg20ref`, with the normalized law supplied by
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
* `hBGref`: Berestycki–Gwynne (2020), Theorem 1.2, on one reference environment with normalized law `ν`. -/
theorem closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν))
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν))
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  MatedCRT.closed_1_4_quantumConeScaling_coneDimension_bg20ref ν
    (hasNormalizedSLELaw_canonicalSLEModel hZO)
    ⟨hscale, ProbeMi.canonicalSLEModel_reparam ν, ProbeMi.canonicalSLEModel_indepMono ν⟩ hN4 h10 hBGref

/-- **Theorem 1.6 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_6_quantumConeScaling_coneDimension_bg20ref`, with the normalized law supplied by
`hasNormalizedSLELaw_canonicalSLEModel` and the reparametrization and independence-monotonicity clauses by
`ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`. Remaining binders, as in
`closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical`:
* `hZO`: for `κ > 4`, `ν κ`-almost every code is the code of a path that visits `0` only at time `0`; for the law of
  whole-plane space-filling SLE parametrized by Lebesgue measure with `η 0 = 0` this is what one expects from
  Duplantier–Miller–Sheffield (arXiv:1409.7055, p. 24) together with the translation invariance of the Lebesgue
  parametrization (Holden–Sun, Lemma 2.3);
* `hscale`: scale invariance of the SLE predicate of the model (Miller–Sheffield, *Imaginary Geometry IV*, §1.2.3);
* `hN4`: the uniform-start invariance principle for the mated-CRT map walk (Gwynne–Miller–Sheffield 2021,
  Theorem 3.4);
* `h10`: reference environments of the model;
* `hBGref`: Berestycki–Gwynne (2020), Theorem 1.2, on one reference environment with normalized law `ν`. -/
theorem closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν))
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
    (h10 : HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν))
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  MatedCRT.closed_1_6_quantumConeScaling_coneDimension_bg20ref ν
    (hasNormalizedSLELaw_canonicalSLEModel hZO)
    ⟨hscale, ProbeMi.canonicalSLEModel_reparam ν, ProbeMi.canonicalSLEModel_indepMono ν⟩ hN4 h10 hBGref

/-- **Theorem 1.4 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical` with the reference environments `h10` supplied by
`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`. Remaining binders: `hZO`, `hscale`,
`hN4`, `hBGref` as in `closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling
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
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical ν hZO hscale hN4
    (MatedCRT.Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix hfixsm)
    hBGref

/-- **Theorem 1.6 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical` with the reference environments `h10` supplied by
`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`. Remaining binders: `hZO`, `hscale`,
`hN4`, `hBGref` as in `closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling
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
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical ν hZO hscale hN4
    (MatedCRT.Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix hfixsm)
    hBGref

end MatedCRT.FirstPass.Derived
