import MatedCRT.FirstPass.Derived.HN8OfRevuzLintegralGlue
import MatedCRT.FirstPass.Derived.CanonicalNormalizedLaw
import MatedCRT.FirstPass.Derived.CanonicalHasReferenceEnvironments
import MatedCRT.FirstPass.SLERef.CanonicalScaleInvariance
import LatticeProb.LQG.CouplingFixedTimeFiber
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii

/-!
# Normalized law, closure properties and reference environments of the canonical model from couplings

Let `ν` be a family of laws on `SLEPathCode` such that, for every `γ ∈ (0, 2)`, some mating-of-trees coupling on the
sample space `ℝ` has a Lebesgue-parametrized curve `ηL` whose rational-time code has law `ν (16/γ²)`. Then, for the
canonical model `ProbeMi.canonicalSLEModel ν`:

* the normalized law `HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν` holds. At a fixed time the area-parametrized
  curve `η` has a singleton fibre (`MoTInput.ae_fixedTime_singleton_fiber_of_coupling`, from the contour relation of the
  boundary-length Brownian motion and the field `onlyMerge`), and `η = ηL ∘ φ` with `φ` an increasing bijection fixing
  `0` and `ηL 0 = 0` (fields `spaceFilling` and `areaParam`). Hence `ηL` visits `0` only at time `0`, so `ν κ`-almost
  every code is the code of such a path (`SLECodeZeroOnlyAtOrigin ν`), which is the hypothesis of
  `hasNormalizedSLELaw_canonicalSLEModel`;
* the closure properties `SLEModelClosureInput (ProbeMi.canonicalSLEModel ν)` hold. Increasing reparametrization and
  monotonicity of independence hold for every canonical model; scale invariance follows from
  `ProbeMi.SLECodeScaleInvariant ν`, and this holds because the law of `ηL` is invariant under the area-preserving
  rescaling `s ↦ r ηL (s / r²)` (`IGLaw.IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii`, from the
  imaginary-geometry coordinate change `igMap`) and the code of the rescaled path is a measurable function of the code
  of `ηL` (`ProbeMi.codeScale`);
* the reference environments `HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν)` hold under the fixed-start
  convergence and strict monotonicity of the dyadic Liouville clocks of the normalized whole-plane Gaussian free
  field (Berestycki 2015, fixed starting point), by
  `Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`.

Consequently Theorems 1.4 and 1.6 in the counted forms `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
and `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` hold at the canonical model from the couplings,
the fixed-start clock, and the two remaining inputs `hN4` and `hN9` of the counted forms: the premises `h1`, `h2` and
`h10` are proved.

## Main statements

* `ae_eq_zero_of_igCurve_eq_zero_of_coupling`: the Lebesgue-parametrized curve of a coupling visits `0` only at
  time `0`, almost surely.
* `sleCodeZeroOnlyAtOrigin_of_coupling`, `sleCodeScaleInvariant_of_coupling`: the two hypotheses on `ν`.
* `hasNormalizedSLELaw_canonicalSLEModel_of_coupling`, `sleModelClosureInput_canonicalSLEModel_of_coupling`: `h1` and
  `h2` at the canonical model.
* `exists_codeLaw_of_coupling`: from couplings with no law prescribed, the family `ν` of their code laws.
* `exists_canonical_inputs_of_coupling_wholePlane_fixedStart`: some `ν` gives `h1`, `h2` and `h10` at the canonical
  model, from bare couplings and the fixed-start clock.
* `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling`: Theorems 1.4 and 1.6 at
  the canonical model from `hcpl hfix hfixsm hN4 hN9`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.LQGMetric _root_.MatedCRTHarmonic _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

section Coupling

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The Lebesgue-parametrized curve of a coupling visits the origin only at time `0`.** Almost surely, `ηL t = 0`
forces `t = 0`: with `η = ηL ∘ φ`, `φ` an increasing bijection fixing `0`, and `ηL 0 = 0`, a time `t` with `ηL t = 0`
gives `η (φ⁻¹ t) = η 0`, and the fibre of `η` at the fixed time `0` is a singleton. -/
theorem ae_eq_zero_of_igCurve_eq_zero_of_coupling
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ t, ηL ω t = 0 → t = 0 := by
  filter_upwards [ae_isLebesgueRepresentative_of_coupling D (η := fun ω => ⇑(η ω))
      (Eventually.of_forall fun _ => rfl),
    MatedCRTHarmonic.MoTInput.ae_fixedTime_singleton_fiber_of_coupling D 0] with ω hrep hfib t ht
  obtain ⟨h0, -, -, -, φ, hφ0, hφ⟩ := hrep
  have hφ' : ∀ s, η ω s = ηL ω (φ s) := hφ
  have h1 : η ω (φ.symm t) = η ω 0 := by
    rw [hφ' (φ.symm t), hφ' 0, OrderIso.apply_symm_apply, hφ0, ht, h0]
  calc t = φ (φ.symm t) := (φ.apply_symm_apply t).symm
    _ = 0 := by rw [hfib _ h1, hφ0]

end Coupling

/-- For `κ > 4`, the parameter `γ = 4 / √κ` lies in `(0, 2)`. -/
theorem four_div_sqrt_mem_Ioo {κ : ℝ} (hκ : 4 < κ) : 0 < 4 / Real.sqrt κ ∧ 4 / Real.sqrt κ < 2 := by
  have h2 : 2 < Real.sqrt κ := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hs : 0 < Real.sqrt κ := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hs]
  linarith

/-- For `κ > 0`, `16 / (4 / √κ)² = κ`. -/
theorem sixteen_div_sq_four_div_sqrt {κ : ℝ} (hκ : 0 < κ) : 16 / (4 / Real.sqrt κ) ^ 2 = κ := by
  rw [div_pow, Real.sq_sqrt hκ.le]
  field_simp
  norm_num

/-- The area-preserving rescaling `ProbeMi.scaleCurve r` is the rescaling `GMS4b.curveRescale r⁻¹ (r⁻¹ ^ 2)`. -/
theorem scaleCurve_eq_curveRescale (r : ℝ) (c : C(ℝ, ℂ)) :
    ProbeMi.scaleCurve r c = GMS4b.curveRescale r⁻¹ (r⁻¹ ^ 2) c := by
  ext s
  rw [ProbeMi.scaleCurve_apply, GMS4b.curveRescale_apply, inv_inv, inv_pow, ← div_eq_inv_mul]

section CodeLaw

variable {ν : ℝ → Measure SLEPathCode}

/-- **The origin is visited once, from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees coupling on `ℝ`
has a Lebesgue-parametrized curve with code law `ν (16/γ²)`, then for `κ > 4`, `ν κ`-almost every code is the code
of a path visiting `0` only at time `0`. -/
theorem sleCodeZeroOnlyAtOrigin_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    SLECodeZeroOnlyAtOrigin ν := by
  intro κ hκ
  obtain ⟨hγ0, hγ2⟩ := four_div_sqrt_mem_Ioo hκ
  obtain ⟨P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D, hlaw⟩ := hcpl _ hγ0 hγ2
  rw [sixteen_div_sq_four_div_sqrt (by linarith)] at hlaw
  exact ae_mem_zeroOnlyAtOriginCode_of_map_eq _ P ηL
    (measurableEmbedding_slePathCode.measurable.comp D.measurable_curves.1) hlaw
    (ae_eq_zero_of_igCurve_eq_zero_of_coupling D)

/-- **Scale invariance of the code law, from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees coupling on
`ℝ` has a Lebesgue-parametrized curve with code law `ν (16/γ²)`, then `ν` is invariant under the area-preserving
rescalings: every random continuous path whose code has law `ν κ` (`κ > 4`) keeps that code law after
`s ↦ r ηL (s / r²)`. -/
theorem sleCodeScaleInvariant_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    ProbeMi.SLECodeScaleInvariant ν := by
  intro Ω' mΩ' P' κ r ηL' _ hκ hr hm' hlaw'
  obtain ⟨hγ0, hγ2⟩ := four_div_sqrt_mem_Ioo hκ
  obtain ⟨P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D, hlaw⟩ := hcpl _ hγ0 hγ2
  rw [sixteen_div_sq_four_div_sqrt (by linarith)] at hlaw
  have hcode := measurableEmbedding_slePathCode
  have hηL : Measurable ηL := D.measurable_curves.1
  have hcs : Measurable (fun x : SLEPathCode => ProbeMi.codeScale (r, x)) :=
    ProbeMi.measurable_codeScale.comp (measurable_const.prodMk measurable_id)
  have hsc : Measurable (fun ω => ProbeMi.scaleCurve r (ηL ω)) := by
    rw [← hcode.measurable_comp_iff]
    have e : (slePathCode ∘ fun ω => ProbeMi.scaleCurve r (ηL ω)) =
        (fun x => ProbeMi.codeScale (r, x)) ∘ (slePathCode ∘ ηL) := by
      funext ω
      exact (ProbeMi.codeScale_slePathCode r (ηL ω)).symm
    rw [e]
    exact hcs.comp (hcode.measurable.comp hηL)
  have hinv : (ν κ).map (fun x => ProbeMi.codeScale (r, x)) = ν κ := by
    calc (ν κ).map (fun x => ProbeMi.codeScale (r, x))
        = P.map ((fun x => ProbeMi.codeScale (r, x)) ∘ fun ω => slePathCode (ηL ω)) := by
          rw [← hlaw]
          exact Measure.map_map hcs (hcode.measurable.comp hηL)
      _ = P.map (slePathCode ∘ fun ω => ProbeMi.scaleCurve r (ηL ω)) := by
          congr 1
          funext ω
          exact ProbeMi.codeScale_slePathCode _ _
      _ = (P.map fun ω => ProbeMi.scaleCurve r (ηL ω)).map slePathCode :=
          (Measure.map_map hcode.measurable hsc).symm
      _ = (P.map ηL).map slePathCode := by
          congr 1
          simp_rw [scaleCurve_eq_curveRescale]
          exact IGLaw.IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii D
            (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D) (inv_pos.2 hr)
      _ = ν κ := by
          rw [Measure.map_map hcode.measurable hηL]
          exact hlaw
  let _inst : MeasurableSpace Ω' := mΩ'
  calc P'.map (fun ω => slePathCode (ProbeMi.scaleCurve r (ηL' ω)))
      = P'.map ((fun x => ProbeMi.codeScale (r, x)) ∘ fun ω => slePathCode (ηL' ω)) := by
        congr 1
        funext ω
        exact (ProbeMi.codeScale_slePathCode _ _).symm
    _ = (P'.map fun ω => slePathCode (ηL' ω)).map (fun x => ProbeMi.codeScale (r, x)) :=
        (Measure.map_map hcs hm').symm
    _ = ν κ := by rw [hlaw', hinv]

/-- **`h1` at the canonical model, from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees coupling on `ℝ`
has a Lebesgue-parametrized curve with code law `ν (16/γ²)`, then the canonical model has normalized law `ν`. -/
theorem hasNormalizedSLELaw_canonicalSLEModel_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν :=
  hasNormalizedSLELaw_canonicalSLEModel (sleCodeZeroOnlyAtOrigin_of_coupling hcpl)

/-- **`h2` at the canonical model, from couplings.** If for every `γ ∈ (0, 2)` some mating-of-trees coupling on `ℝ`
has a Lebesgue-parametrized curve with code law `ν (16/γ²)`, then the SLE predicate of the canonical model is closed
under positive scalings, increasing reparametrizations and smaller independent σ-algebras. -/
theorem sleModelClosureInput_canonicalSLEModel_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    SLEModelClosureInput (ProbeMi.canonicalSLEModel ν) :=
  ⟨ProbeMi.canonicalSLEModel_scale ν (sleCodeScaleInvariant_of_coupling hcpl),
    ProbeMi.canonicalSLEModel_reparam ν, ProbeMi.canonicalSLEModel_indepMono ν⟩

end CodeLaw

/-- **The code laws of a family of couplings.** If for every `γ ∈ (0, 2)` there is a mating-of-trees coupling on `ℝ`,
then some family `ν` is, at `16/γ²`, the code law of the Lebesgue-parametrized curve of such a coupling, for every
`γ ∈ (0, 2)`. -/
theorem exists_codeLaw_of_coupling
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ ν : ℝ → Measure SLEPathCode, ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2) := by
  choose P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D using hcpl
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
  refine ⟨P γ hγ0 hγ2, X γ hγ0 hγ2, X₀ γ hγ0 hγ2, hIG₀ γ hγ0 hγ2, B γ hγ0 hγ2, B' γ hγ0 hγ2,
    B₀ γ hγ0 hγ2, B₀' γ hγ0 hγ2, U γ hγ0 hγ2, ηL γ hγ0 hγ2, η γ hγ0 hγ2, η₀ γ hγ0 hγ2, bm γ hγ0 hγ2,
    D γ hγ0 hγ2, ?_⟩
  dsimp only
  rw [dite_eq_left hmem]
  exact key _ _ _ e

/-- **`h1`, `h2` and `h10` at a canonical model, from couplings and the fixed-start clock.** If for every
`γ ∈ (0, 2)` there is a mating-of-trees coupling on the sample space `ℝ` (Duplantier-Miller-Sheffield; no law
prescribed for its curve), and the dyadic Liouville clocks of the normalized whole-plane Gaussian free field
converge uniformly on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing
limit (Berestycki 2015, fixed starting point), then for some family `ν` the canonical model
`ProbeMi.canonicalSLEModel ν` has normalized law `ν`, the three closure properties, and reference environments. -/
theorem exists_canonical_inputs_of_coupling_wholePlane_fixedStart
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
    ∃ ν : ℝ → Measure SLEPathCode,
      HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν ∧
      SLEModelClosureInput (ProbeMi.canonicalSLEModel ν) ∧
      HasReferenceEnvironments (ProbeMi.canonicalSLEModel ν) := by
  obtain ⟨ν, hν⟩ := exists_codeLaw_of_coupling hcpl
  exact ⟨ν, hasNormalizedSLELaw_canonicalSLEModel_of_coupling hν,
    sleModelClosureInput_canonicalSLEModel_of_coupling hν,
    Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hν hfix hfixsm⟩

/-- **Theorem 1.4 at the canonical space-filling SLE model, from couplings, the fixed-start clock, `hN4` and `hN9`.**
The counted form `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` at
`ProbeMi.canonicalSLEModel ν`, with `h1` (`hasNormalizedSLELaw_canonicalSLEModel_of_coupling`), `h2`
(`sleModelClosureInput_canonicalSLEModel_of_coupling`) and `h10`
(`Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart`) proved. Remaining binders:
* `hcpl`: for every `γ ∈ (0, 2)`, a mating-of-trees coupling on the sample space `ℝ` (Duplantier-Miller-Sheffield)
  whose Lebesgue-parametrized curve has code law `ν (16/γ²)`;
* `hfix`, `hfixsm`: the dyadic Liouville clocks of the normalized whole-plane Gaussian free field converge uniformly
  on compact time intervals from Lebesgue-almost every fixed start, with a strictly increasing limit
  (Berestycki 2015, fixed starting point);
* `hN4`: the uniform-start invariance principle for the mated-CRT map walk (Gwynne-Miller-Sheffield 2021,
  Theorem 3.4);
* `hN9`: the time-change constant of a limit is deterministic (Berestycki-Gwynne (2020), Lemma 7.18). -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling
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
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t))
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
  MatedCRT.closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν
    (hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl)
    (sleModelClosureInput_canonicalSLEModel_of_coupling hcpl) hN4
    (Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix hfixsm) hN9

/-- **Theorem 1.6 at the canonical space-filling SLE model, from couplings, the fixed-start clock, `hN4` and `hN9`.**
The counted form `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8` at
`ProbeMi.canonicalSLEModel ν`, with `h1`, `h2` and `h10` proved as in
`closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling`; the remaining binders
`hcpl`, `hfix`, `hfixsm`, `hN4` and `hN9` are the same. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8_canonical_of_coupling
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
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t))
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
  MatedCRT.closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8 ν
    (hasNormalizedSLELaw_canonicalSLEModel_of_coupling hcpl)
    (sleModelClosureInput_canonicalSLEModel_of_coupling hcpl) hN4
    (Sec1.hasReferenceEnvironments_canonical_of_coupling_wholePlane_fixedStart ν hcpl hfix hfixsm) hN9

end MatedCRT.FirstPass.Derived
