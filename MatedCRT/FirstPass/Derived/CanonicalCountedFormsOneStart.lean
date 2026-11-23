import MatedCRT.FirstPass.Derived.CanonicalInputsOfCoupling
import MatedCRT.FirstPass.Derived.MatingOfTreesCouplingReal
import MatedCRT.FirstPass.Derived.WholePlaneClockFixedStartOfLocalLimit

/-!
# Theorems 1.4 and 1.6 at the canonical model from couplings and two statements on the Gaussian Liouville clock

The two hypotheses `hfix` (fixed-start convergence of the dyadic Liouville clocks of the normalized whole-plane GFF)
and `hfixsm` (strict monotonicity of their limit) of the reference environments are replaced by two statements for the
whole-plane GFF of `LatticeProb.Gauss` (Berestycki 2015):

* `hloc`: from every start, almost surely for the joint law of the field and planar Brownian motion, the dyadic clocks
  `A_{n+1}` converge locally uniformly on `[0, ∞)` to a continuous, nonnegative, nondecreasing limit
  (`Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit`);
* `hone`: almost surely in the field, for all rationals `0 < a < b`, from the origin, almost surely the increment of the
  dyadic clocks over `[a, b]` has positive lower limit (`Sec1.wholePlane_fixedStart_strictMono_of_oneStart`).

The couplings may also live on any standard Borel probability space (`forall_exists_coupling_real_of_standardBorel`).

## Main statements

* `exists_canonical_inputs_of_coupling_standardBorel_localLimit_oneStart`: some family `ν` gives `h1`, `h2` and `h10`
  at the canonical model, from couplings on standard Borel spaces, `hloc` and `hone`.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart`:
  Theorems 1.4 and 1.6 at the canonical model from `hcpl hloc hone hN4 hN9`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **`h1`, `h2` and `h10` at a canonical model from couplings on standard Borel spaces and the Gaussian clock
statements.** If for every `γ ∈ (0, 2)` there is a mating-of-trees coupling on a standard Borel probability space, and
the statements `hloc` (locally uniform convergence of the dyadic clocks from every start) and `hone` (positive
increments from the origin) hold for every `γ ∈ (0, 2)` and every whole-plane GFF of `LatticeProb.Gauss`, then for some
family `ν` the canonical model `ProbeMi.canonicalSLEModel ν` has normalized law `ν`, the three closure properties, and
reference environments. -/
theorem exists_canonical_inputs_of_coupling_standardBorel_localLimit_oneStart
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω), StandardBorelSpace Ω ∧
        ∃ (P : Measure Ω) (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
          (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2),
          IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hloc : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
        ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
          ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
            ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
              |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                  (q.2 s.toNNReal))) - F t| < η)
    (hone : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
          0 < liminf (fun k => ENNReal.ofReal (∫ v in (a : ℝ)..(b : ℝ),
            HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k)
                (w v.toNNReal)))) atTop) :
    ∃ ν : ℝ → Measure SLEPathCode,
      HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν ∧
      SLEModelClosureInput (ProbeMi.canonicalSLEModel ν) ∧
      HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) :=
  exists_canonical_inputs_of_coupling_wholePlane_fixedStart
    (forall_exists_coupling_real_of_standardBorel hcpl)
    (Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit hloc)
    (Sec1.wholePlane_fixedStart_strictMono_of_oneStart hone
      (Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit hloc))

/-- **Theorem 1.4 at the canonical space-filling SLE model, from couplings, the Gaussian clock statements, `hN4` and
`hN9`.** The form `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling` with
`hfix` supplied by `Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit` and `hfixsm` by
`Sec1.wholePlane_fixedStart_strictMono_of_oneStart`, from
* `hloc`: for every `γ ∈ (0, 2)`, every whole-plane GFF of `LatticeProb.Gauss` and every start, almost surely for the
  joint law the dyadic clocks converge locally uniformly to a continuous, nonnegative, nondecreasing limit;
* `hone`: for every `γ ∈ (0, 2)` and every whole-plane GFF of `LatticeProb.Gauss`, almost surely in the field, for all
  rationals `0 < a < b`, from the origin, almost surely the increment of the dyadic clocks over `[a, b]` has positive
  lower limit (Berestycki 2015). -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart
    (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hloc : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
        ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
          ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
            ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
              |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                  (q.2 s.toNNReal))) - F t| < η)
    (hone : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
          0 < liminf (fun k => ENNReal.ofReal (∫ v in (a : ℝ)..(b : ℝ),
            HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k)
                (w v.toNNReal)))) atTop)
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
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
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling ν hcpl
    (Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit hloc)
    (Sec1.wholePlane_fixedStart_strictMono_of_oneStart hone
      (Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit hloc)) hN4 hN9

/-- **Theorem 1.6 at the canonical space-filling SLE model, from couplings, the Gaussian clock statements, `hN4` and
`hN9`.** The form `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling` with
`hfix` and `hfixsm` supplied from `hloc` and `hone` as in
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart`. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling_localLimit_oneStart
    (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hloc : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
        ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
          ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
            ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
              |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                  (q.2 s.toNNReal))) - F t| < η)
    (hone : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
          0 < liminf (fun k => ENNReal.ofReal (∫ v in (a : ℝ)..(b : ℝ),
            HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k)
                (w v.toNNReal)))) atTop)
    (hN4 : GMS21UniformStartInput (ProbeMi.canonicalSLEModel ν))
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
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling ν hcpl
    (Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit hloc)
    (Sec1.wholePlane_fixedStart_strictMono_of_oneStart hone
      (Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit hloc)) hN4 hN9

end MatedCRT.FirstPass.Derived
