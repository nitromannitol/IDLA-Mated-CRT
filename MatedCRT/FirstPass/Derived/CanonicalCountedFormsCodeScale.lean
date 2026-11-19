import MatedCRT.FirstPass.Derived.CanonicalCountedForms
import MatedCRT.FirstPass.SLERef.CanonicalScaleInvariance

/-!
# Theorems 1.4 and 1.6 at the canonical space-filling SLE model, with scale invariance of the code law

The forms of `MatedCRT.FirstPass.Derived.CanonicalCountedForms` take scale invariance of the SLE predicate of the
canonical model, `hscale : SLEScaleInvarianceInput (ProbeMi.canonicalSLEModel ν)`, as a binder. For the canonical
model this field follows from a property of the family `ν` of code laws alone, `ProbeMi.SLECodeScaleInvariant ν`
(a random continuous path whose code has law `ν κ` keeps that code law after the area-preserving rescaling
`s ↦ r c (s / r ^ 2)`), through `ProbeMi.canonicalSLEModel_scale`. The four theorems below are the forms of
`CanonicalCountedForms` with the binder `hscale` replaced at its position by `hSC : ProbeMi.SLECodeScaleInvariant ν`.

## Main statements

* `closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale`,
  `closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale`: Theorems 1.4 and 1.6 at the
  canonical model from `hZO hSC hN4 h10 hBGref`.
* `closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling_of_codeScale`,
  `closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling_of_codeScale`: the same from
  `hZO hSC hN4 hcpl hfix hfixsm hBGref`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Theorem 1.4 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_4_quantumConeScaling_coneDimension_bg20ref`, with the normalized law supplied by
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
* `hBGref`: Berestycki–Gwynne (2020), Theorem 1.2, on one reference environment with normalized law `ν`. -/
theorem closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hSC : ProbeMi.SLECodeScaleInvariant ν)
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
  closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 h10 hBGref

/-- **Theorem 1.6 at the canonical space-filling SLE model** `ProbeMi.canonicalSLEModel ν`, in the counted form
`closed_1_6_quantumConeScaling_coneDimension_bg20ref`, with the normalized law supplied by
`hasNormalizedSLELaw_canonicalSLEModel`, the reparametrization and independence-monotonicity clauses by
`ProbeMi.canonicalSLEModel_reparam` and `ProbeMi.canonicalSLEModel_indepMono`, and the scale-invariance clause by
`ProbeMi.canonicalSLEModel_scale`. Remaining binders, as in
`closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale`:
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
* `hBGref`: Berestycki–Gwynne (2020), Theorem 1.2, on one reference environment with normalized law `ν`. -/
theorem closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale
    (ν : ℝ → Measure SLEPathCode)
    (hZO : SLECodeZeroOnlyAtOrigin ν)
    (hSC : ProbeMi.SLECodeScaleInvariant ν)
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
  closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 h10 hBGref

/-- **Theorem 1.4 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling` with the scale-invariance clause supplied
by `ProbeMi.canonicalSLEModel_scale`. Remaining binders: `hZO`, `hSC`, `hN4`, `hBGref` as in
`closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling_of_codeScale
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
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfIDLAStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_4_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 hcpl hfix hfixsm hBGref

/-- **Theorem 1.6 at the canonical space-filling SLE model, from mating-of-trees couplings.** The form
`closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling` with the scale-invariance clause supplied
by `ProbeMi.canonicalSLEModel_scale`. Remaining binders: `hZO`, `hSC`, `hN4`, `hBGref` as in
`closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_codeScale`, and
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier–Miller–Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point). -/
theorem closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling_of_codeScale
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
    (hBGref : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ConvergenceOfDivSandpileStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_1_6_quantumConeScaling_coneDimension_bg20ref_canonical_of_coupling ν hZO
    (ProbeMi.canonicalSLEModel_scale ν hSC) hN4 hcpl hfix hfixsm hBGref

end MatedCRT.FirstPass.Derived
