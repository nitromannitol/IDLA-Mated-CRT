import MatedCRT.FirstPass.Derived.HasReferenceEnvironmentsOfCoupling
import MatedCRT.FirstPass.Derived.CanonicalSLECoupling

/-!
# Reference environments of the canonical space-filling SLE model

For the canonical (null-robust) model `ProbeMi.canonicalSLEModel ν` of whole-plane space-filling
SLE, the clause "the model recognizes the curve of a mating-of-trees coupling as an SLE against
every sub-σ-algebra independent of its Lebesgue-parametrized curve" is a consequence of the
coupling itself, as soon as `ν (16/γ²)` is the law of the rational-time code of that
Lebesgue-parametrized curve: the curve is a measurable, almost surely Lebesgue-area representative
of the area-parametrized curve (fields `measurable_curves`, `spaceFilling` and `areaParam`),
and the σ-algebra of its code is contained in the σ-algebra of the curve.

Hence, for the canonical model, the reference environments reduce to the existence of
mating-of-trees couplings on the sample space `ℝ` (Duplantier-Miller-Sheffield) and the
fixed-start convergence and strict monotonicity of the dyadic Liouville clocks of the normalized
whole-plane Gaussian free field (Berestycki 2015, fixed starting point).

## Main statements

* `canonicalSLEModel_isSLE_of_coupling_of_indep`: the recognition clause for every independent
  sub-σ-algebra.
* `hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`: reference environments
  of the canonical model from couplings whose curve has code law `ν (16/γ²)` and the fixed-start
  clock.
* `exists_hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`: from couplings
  alone (no law prescribed) and the fixed-start clock, some family `ν` (the code laws of the
  couplings) gives a canonical model with reference environments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- **Recognition of the coupling curve by the canonical model.** If the Lebesgue-parametrized
curve `ηL` of a mating-of-trees coupling has code law `ν (16/γ²)`, then the canonical model
`ProbeMi.canonicalSLEModel ν` recognizes the area-parametrized curve `η` as an SLE with
parameter `κ' = 16/γ²` against every sub-σ-algebra independent of `ηL`. -/
theorem canonicalSLEModel_isSLE_of_coupling_of_indep
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {ν : ℝ → Measure SLEPathCode}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hlaw : P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    ∀ 𝓕 : MeasurableSpace Ω, 𝓕 ≤ mΩ →
      Indep 𝓕 (MeasurableSpace.comap ηL inferInstance) P →
      @SpaceFillingSLEModel.IsSLE (ProbeMi.canonicalSLEModel ν) Ω mΩ P 𝓕 (16 / γ ^ 2)
        (fun ω => ⇑(η ω)) := by
  have hcode : MeasurableSpace.comap (fun ω => slePathCode (ηL ω)) inferInstance ≤
      MeasurableSpace.comap ηL inferInstance := by
    change MeasurableSpace.comap (slePathCode ∘ ηL) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono MatedCRT.FirstPass.Derived.measurableEmbedding_slePathCode.measurable.comap_le
  have hmeas : Measurable (fun ω => slePathCode (ηL ω)) :=
    MatedCRT.FirstPass.Derived.measurableEmbedding_slePathCode.measurable.comp D.measurable_curves.1
  have hrepr : ∀ᵐ ω ∂P, ProbeMi.IsLebesgueRepresentativeFree (⇑(η ω)) (ηL ω) := by
    filter_upwards [MatedCRT.FirstPass.Derived.ae_isLebesgueRepresentative_of_coupling D
      (η := fun ω => ⇑(η ω)) (Eventually.of_forall fun _ => rfl)] with ω hω
    obtain ⟨h0, hsurj, hproper, hvol, φ, _, hφ⟩ := hω
    exact ⟨h0, hsurj, hproper, hvol, φ, hφ⟩
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  intro 𝓕 h𝓕 hind
  exact ⟨hP, h𝓕, ηL, hmeas, hrepr, hlaw,
    (indep_of_indep_of_le_right hind hcode).symm⟩

/-- **Reference environments of the canonical model.** Suppose that for every `γ ∈ (0, 2)` there
is a mating-of-trees coupling on the sample space `ℝ` whose Lebesgue-parametrized curve has code
law `ν (16/γ²)`, and that the dyadic Liouville clocks of the normalized whole-plane Gaussian free
field converge from Lebesgue-almost every fixed start, with a strictly increasing limit
(Berestycki 2015, fixed starting point). Then the canonical model `ProbeMi.canonicalSLEModel ν`
has reference environments. -/
theorem hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart
    (ν : ℝ → Measure SLEPathCode)
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
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)) :
    HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) := by
  refine hasReferenceEnvironments_of_coupling_wholePlane_fixedStart _ (fun γ hγ0 hγ2 => ?_)
    hfix hfixsm
  obtain ⟨P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D, hlaw⟩ := hcpl γ hγ0 hγ2
  exact ⟨P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D,
    canonicalSLEModel_isSLE_of_coupling_of_indep D hlaw⟩

/-- **A canonical model with reference environments.** If for every `γ ∈ (0, 2)` there is a
mating-of-trees coupling on the sample space `ℝ` (no law prescribed for its curve), and the dyadic
Liouville clocks of the normalized whole-plane Gaussian free field converge from Lebesgue-almost
every fixed start, with a strictly increasing limit, then for some family `ν` the canonical model
`ProbeMi.canonicalSLEModel ν` has reference environments: `ν κ` is the code law of the
Lebesgue-parametrized curve of the coupling with `γ = 4/√κ`. -/
theorem exists_hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
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
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)) :
    ∃ ν : ℝ → Measure SLEPathCode, HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) := by
  choose P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D using hcpl
  have hν : ∃ ν : ℝ → Measure SLEPathCode, ∀ γ (hγ0 : 0 < γ) (hγ2 : γ < 2),
      (P γ hγ0 hγ2).map (fun ω => slePathCode (ηL γ hγ0 hγ2 ω)) = ν (16 / γ ^ 2) := by
    refine ⟨fun κ => if h : 0 < 4 / Real.sqrt κ ∧ 4 / Real.sqrt κ < 2 then
      (P _ h.1 h.2).map (fun ω => slePathCode (ηL _ h.1 h.2 ω)) else 0, fun γ hγ0 hγ2 => ?_⟩
    have e : 4 / Real.sqrt (16 / γ ^ 2) = γ := by
      have h16 : (16 : ℝ) / γ ^ 2 = (4 / γ) ^ 2 := by rw [div_pow]; norm_num
      rw [h16, Real.sqrt_sq (by positivity)]
      field_simp
    have key : ∀ a (ha0 : 0 < a) (ha2 : a < 2), a = γ →
        (P γ hγ0 hγ2).map (fun ω => slePathCode (ηL γ hγ0 hγ2 ω)) =
          (P a ha0 ha2).map (fun ω => slePathCode (ηL a ha0 ha2 ω)) := by
      rintro a _ _ rfl
      rfl
    have hmem : 0 < 4 / Real.sqrt (16 / γ ^ 2) ∧ 4 / Real.sqrt (16 / γ ^ 2) < 2 := by
      rw [e]
      exact ⟨hγ0, hγ2⟩
    dsimp only
    rw [dite_eq_left hmem]
    exact key _ _ _ e
  obtain ⟨ν, hν⟩ := hν
  exact ⟨ν, hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν
    (fun γ hγ0 hγ2 => ⟨P γ hγ0 hγ2, X γ hγ0 hγ2, X₀ γ hγ0 hγ2, hIG₀ γ hγ0 hγ2, B γ hγ0 hγ2,
      B' γ hγ0 hγ2, B₀ γ hγ0 hγ2, B₀' γ hγ0 hγ2, U γ hγ0 hγ2, ηL γ hγ0 hγ2, η γ hγ0 hγ2,
      η₀ γ hγ0 hγ2, bm γ hγ0 hγ2, D γ hγ0 hγ2, hν γ hγ0 hγ2⟩) hfix hfixsm⟩

end MatedCRT.Sec1
