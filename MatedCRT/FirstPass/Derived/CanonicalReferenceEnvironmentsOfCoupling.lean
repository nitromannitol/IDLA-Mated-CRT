import MatedCRT.FirstPass.Derived.CanonicalCountedFormsOfCouplingClock

/-!
# Reference environments of the canonical model from mating-of-trees couplings alone

The reference environments of the canonical space-filling SLE model `ProbeMi.canonicalSLEModel ν`
(`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`) rest on the couplings of
Duplantier-Miller-Sheffield (arXiv:1409.7055, Theorem 1.9) and on two statements on the Liouville clock of the
normalized whole-plane Gaussian free field from a fixed start (Berestycki 2015, arXiv:1301.3356):

* `hfix`: from Lebesgue-almost every start, the dyadic clocks converge uniformly on compact time intervals;
* `hfixsm`: from Lebesgue-almost every start, their limit is strictly increasing.

Both are theorems. `hfix` follows from the locally uniform limit of the dyadic clocks of the whole-plane GFF of
`LatticeProb.Gauss` at the insertion `0` for every `0 < γ < 2` (`gaussianClock_localLimit_of_lt_two`, from
Harmonic-Balls-LQG) by `Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit`; `hfixsm` follows from it and the
one-start event (`gaussianClock_oneStart`, from Harmonic-Balls-LQG) by
`Sec1.wholePlane_fixedStart_strictMono_of_oneStart`. Hence the premises `h1` (normalized law), `h2` (closure
properties) and `h10` (reference environments) of the counted forms hold at the canonical model as soon as, for every
`γ ∈ (0, 2)`, some mating-of-trees coupling has a Lebesgue-parametrized curve with code law `ν (16/γ²)`.

For an arbitrary model `𝒮` the reference environments do not follow from anything about laws: they fail for the model
whose SLE predicate is `False`. The statements here are at the canonical model.

## Main statements

* `wholePlane_fixedStart_uniformCauchy`, `wholePlane_fixedStart_strictMono`: the fixed-start clock statements `hfix`
  and `hfixsm` for every `γ ∈ (0, 2)`.
* `hasReferenceEnvironments_canonicalSLEModel_of_coupling`: `h10` at the canonical model from the couplings.
* `canonicalSLEModel_inputs_of_coupling`: `h1`, `h2` and `h10` at the canonical model from the couplings.
* `exists_canonical_inputs_of_coupling_standardBorel`: from couplings on standard Borel probability spaces, with no
  law prescribed for the curve, some family `ν` gives `h1`, `h2` and `h10` at the canonical model.
* `exists_referenceModel_of_coupling`, `sleReferenceInput_of_coupling`, `sleFrozenReferenceInput_of_coupling`: the
  reference model of `SLEReferenceInput ν` and `SLEFrozenReferenceInput ν` is the canonical model.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Fixed-start convergence of the Liouville clock (`hfix`)** for every `γ ∈ (0, 2)`: for every normalized
whole-plane Gaussian free field `Y'` with a jointly continuous, measurable version `c'` of its circle averages, for
every `T`, from Lebesgue-almost every start `y`, almost surely for the joint law of the field and planar Brownian
motion from `y`, the dyadic clocks `lqgClockApprox γ (c' Y') ε_k` form a uniformly Cauchy sequence on `[0, T]`. -/
theorem wholePlane_fixedStart_uniformCauchy : ∀ γ : ℝ, 0 < γ → γ < 2 →
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
            atTop (Icc 0 T) :=
  Sec1.wholePlane_fixedStart_uniformCauchy_of_localLimit gaussianClock_localLimit_of_lt_two

/-- **Strict increase of the fixed-start Liouville clock (`hfixsm`)** for every `γ ∈ (0, 2)`: for every normalized
whole-plane Gaussian free field `Y'` with a jointly continuous, measurable version `c'` of its circle averages, from
Lebesgue-almost every start `y`, almost surely for the joint law of the field and planar Brownian motion from `y`, the
limit of the dyadic clocks along positive times is strictly increasing. -/
theorem wholePlane_fixedStart_strictMono : ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
      {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
      IsNormalizedWPGFF Y' P' →
      (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
      (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
      ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
        StrictMono (LatticeProb.limitAfterPositiveTimes
          fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t) :=
  Sec1.wholePlane_fixedStart_strictMono_of_oneStart gaussianClock_oneStart wholePlane_fixedStart_uniformCauchy

section CodeLaw

variable (ν : ℝ → Measure SLEPathCode)

/-- **`h10` at the canonical model from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees coupling on the
sample space `ℝ` has a Lebesgue-parametrized curve whose code has law `ν (16/γ²)`, then the canonical model
`ProbeMi.canonicalSLEModel ν` has reference environments. -/
theorem hasReferenceEnvironments_canonicalSLEModel_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) :=
  Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl
    wholePlane_fixedStart_uniformCauchy wholePlane_fixedStart_strictMono

/-- **`h1`, `h2` and `h10` at the canonical model from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees
coupling on the sample space `ℝ` has a Lebesgue-parametrized curve whose code has law `ν (16/γ²)`, then the canonical
model `ProbeMi.canonicalSLEModel ν` has normalized law `ν`, the three closure properties, and reference
environments. -/
theorem canonicalSLEModel_inputs_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν ∧
      SLEModelClosureInput (ProbeMi.canonicalSLEModel ν) ∧
      HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) :=
  ⟨hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl,
    sleModelClosureInput_canonicalSLEModel_of_coupling hcpl,
    hasReferenceEnvironments_canonicalSLEModel_of_coupling ν hcpl⟩

/-- **A reference model for `ν` from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees coupling on the
sample space `ℝ` has a Lebesgue-parametrized curve whose code has law `ν (16/γ²)`, then some model (the canonical
model `ProbeMi.canonicalSLEModel ν`) has normalized law `ν` and reference environments: the first clause of
`SLEReferenceInput ν` and of `SLEFrozenReferenceInput ν`. -/
theorem exists_referenceModel_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    ∃ 𝒮ref : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮ref ν ∧ HasReferenceEnvironments 𝒮ref :=
  ⟨ProbeMi.canonicalSLEModel ν, hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl,
    hasReferenceEnvironments_canonicalSLEModel_of_coupling ν hcpl⟩

/-- **`SLEReferenceInput ν` from couplings and the five cited statements.** If for every `γ ∈ (0, 2)` some
mating-of-trees coupling on the sample space `ℝ` has a Lebesgue-parametrized curve whose code has law `ν (16/γ²)`,
and every model with normalized law `ν` satisfies the five cited statements, then `ν` is a reference law. -/
theorem sleReferenceInput_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hcited : ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLECitedInputs 𝒮) :
    SLEReferenceInput ν :=
  ⟨exists_referenceModel_of_coupling ν hcpl, hcited⟩

/-- **`SLEFrozenReferenceInput ν` from couplings and the two estimates.** If for every `γ ∈ (0, 2)` some
mating-of-trees coupling on the sample space `ℝ` has a Lebesgue-parametrized curve whose code has law `ν (16/γ²)`,
and every model with normalized law `ν` satisfies the corrected Lemma 3.2 and the fixed-time truncated quenched laws,
then `ν` carries the minimal reference package. -/
theorem sleFrozenReferenceInput_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (hest : ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLEFrozenEstimates 𝒮) :
    SLEFrozenReferenceInput ν :=
  ⟨exists_referenceModel_of_coupling ν hcpl, hest⟩

end CodeLaw

/-- **`h1`, `h2` and `h10` at a canonical model from couplings on standard Borel spaces.** If for every `γ ∈ (0, 2)`
there is a mating-of-trees coupling on some standard Borel probability space (no law prescribed for its curve), then
for some family `ν` (the code laws of the Lebesgue-parametrized curves, transferred to the sample space `ℝ`) the
canonical model `ProbeMi.canonicalSLEModel ν` has normalized law `ν`, the three closure properties, and reference
environments. -/
theorem exists_canonical_inputs_of_coupling_standardBorel
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω), StandardBorelSpace Ω ∧
        ∃ (P : Measure Ω) (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
          (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2),
          IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ ν : ℝ → Measure SLEPathCode,
      HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν ∧
      SLEModelClosureInput (ProbeMi.canonicalSLEModel ν) ∧
      HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) :=
  exists_canonical_inputs_of_coupling_standardBorel_localLimit_oneStart hcpl
    gaussianClock_localLimit_of_lt_two gaussianClock_oneStart

end MatedCRT.FirstPass.Derived
