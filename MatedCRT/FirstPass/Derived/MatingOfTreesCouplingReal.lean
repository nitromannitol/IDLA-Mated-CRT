import LatticeProb.LQG.MatingOfTreesCouplingLaw
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import MatedCRT.FirstPass.Derived.SimilarityLawInvariance

/-!
# Mating-of-trees couplings on the sample space `ℝ`

`HasReferenceEnvironments` asks for environments on the sample space `ℝ`, and its producers from couplings
(`Sec1.hasReferenceEnvironments_of_coupling_wholePlane_fixedStart`) ask for mating-of-trees couplings on `ℝ`. This file
removes that restriction for standard Borel sample spaces: a mating-of-trees coupling on a standard Borel probability
space gives one on `ℝ`, with the same law of the Lebesgue-parametrized curve.

The coupling is first written as a measurable random element `V` of the standard Borel data space `CouplingData`
(`IsMatingOfTreesCoupling.exists_couplingData`). A standard Borel space `Ω` embeds measurably into `ℝ`
(`exists_measurableEmbedding_real`); along a measurable embedding `f : Ω → ℝ`, `V` extends to a measurable
`V' : ℝ → CouplingData` with `V' ∘ f = V` (`MeasurableEmbedding.exists_measurable_extend`). Under the image measure
`P.map f`:

* every clause of the coupling that is a property of the law of `V` (the laws of the fields and of the Brownian paths,
  the independence statements, the uniform law, the law of the boundary-length pair) passes to `V'` by the law
  transfer lemmas of `MatingOfTreesCouplingLaw`, since `(P.map f).map V' = P.map V`;
* every almost sure clause passes pathwise: for a measurable embedding, `∀ᵐ x ∂(P.map f), p x` is equivalent to
  `∀ᵐ ω ∂P, p (f ω)` for every predicate `p` (`MeasurableEmbedding.ae_map_iff`), measurable or not, and
  `V' (f ω) = V ω`. This covers the only-merge clause, whose event need not be measurable;
* the probability bounds and the moment bounds pass by `MeasurableEmbedding.map_apply` and
  `MeasurableEmbedding.lintegral_map`, which hold for all sets and all functions.

## Main statements

* `isCouplingData_map_of_measurableEmbedding`: the transfer along a measurable embedding.
* `exists_isMatingOfTreesCoupling_real_of_standardBorel`: a coupling on a standard Borel space gives a coupling on `ℝ`
  whose Lebesgue-parametrized curve has the same code law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **Transfer of a mating-of-trees coupling along a measurable embedding.** If the coordinates of a measurable random
element `V` of the data space form a mating-of-trees coupling under `P`, `f : Ω → Ω'` is a measurable embedding and
`V' : Ω' → CouplingData` is measurable with `V' (f ω) = V ω` for every `ω`, then the coordinates of `V'` form a
mating-of-trees coupling under `P.map f`. -/
theorem isCouplingData_map_of_measurableEmbedding {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData} {f : Ω → Ω'}
    (hC : IsCouplingData γ P V) (hV : Measurable V) (hf : MeasurableEmbedding f) (hV' : Measurable V')
    (hVf : ∀ ω, V' (f ω) = V ω) :
    IsCouplingData γ (P.map f) V' := by
  have hC' : IsMatingOfTreesCoupling γ P (fun ω => (V ω).X) (fun ω => (V ω).X₀) (fun ω => (V ω).hIG)
      (fun t ω => (V ω).B t) (fun t ω => (V ω).B' t) (fun t ω => (V ω).B₀ t)
      (fun t ω => (V ω).B₀' t) (fun ω => (V ω).U) (fun ω => (V ω).ηL) (fun ω => (V ω).η)
      (fun ω => (V ω).η₀) (fun ω => (V ω).bm) := hC
  have hlaw : (P.map f).map V' = P.map V := by
    rw [Measure.map_map hV' hf.measurable]
    congr 1
    funext ω
    exact hVf ω
  have hpre : ∀ p : CouplingData → Prop, f ⁻¹' {x | p (V' x)} = {ω | p (V ω)} := by
    intro p
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, hVf]
  show IsMatingOfTreesCoupling γ (P.map f) (fun ω => (V' ω).X) (fun ω => (V' ω).X₀) (fun ω => (V' ω).hIG)
    (fun t ω => (V' ω).B t) (fun t ω => (V' ω).B' t) (fun t ω => (V' ω).B₀ t)
    (fun t ω => (V' ω).B₀' t) (fun ω => (V' ω).U) (fun ω => (V' ω).ηL) (fun ω => (V' ω).η)
    (fun ω => (V' ω).η₀) (fun ω => (V' ω).bm)
  exact {
    isProbabilityMeasure := hC.isProbabilityMeasure_of_map_eq hV hV' hlaw
    gff := hC.gff_of_map_eq hV hV' hlaw
    gff₀ := hC.gff₀_of_map_eq hV hV' hlaw
    bm_B := (hC.bm_of_map_eq hV hV' hlaw).1
    bm_B' := (hC.bm_of_map_eq hV hV' hlaw).2.1
    bm_B₀ := (hC.bm_of_map_eq hV hV' hlaw).2.2.1
    bm_B₀' := (hC.bm_of_map_eq hV hV' hlaw).2.2.2
    indep_cone := (hC.indep_cone_of_map_eq hV hV' hlaw).1
    indep_cone₀ := (hC.indep_cone_of_map_eq hV hV' hlaw).2
    igField := hC.igField_of_map_eq hV hV' hlaw
    indep_curve := hC.indep_curve_of_map_eq hV hV' hlaw
    measurable_curves := measurable_curves_of_measurable hV'
    igMap := by
      obtain ⟨Φ, hΦ, hpos, hη, hcov, hloc⟩ := hC'.igMap
      refine ⟨Φ, hΦ, hpos, ?_, fun z₀ s φ hs => ?_, fun W hW hWb δ hδ => ?_⟩
      · refine hf.ae_map_iff.2 ?_
        simp only [hVf]
        exact hη
      · refine hf.ae_map_iff.2 ?_
        simp only [hVf]
        exact hcov z₀ s φ hs
      · obtain ⟨g, hg, hgae⟩ := hloc W hW hWb δ hδ
        refine ⟨g, hg, hf.ae_map_iff.2 ?_⟩
        simp only [hVf]
        exact hgae
    spaceFilling := by
      refine hf.ae_map_iff.2 ?_
      simp only [hVf]
      exact hC'.spaceFilling
    areaParam := by
      refine hf.ae_map_iff.2 ?_
      simp only [hVf]
      exact hC'.areaParam
    areaParam₀ := by
      refine hf.ae_map_iff.2 ?_
      simp only [hVf]
      exact hC'.areaParam₀
    segmentsContainBalls := by
      intro R hR r hr N
      obtain ⟨C, hCb⟩ := hC'.segmentsContainBalls R hR r hr N
      refine ⟨C, fun ε hε => ?_⟩
      rw [hf.map_apply, hpre (fun v => ¬ SegmentsContainBalls v.ηL R r ε)]
      exact hCb ε hε
    coverage := by
      obtain ⟨c, hc, C, hCb⟩ := hC'.coverage
      refine ⟨c, hc, C, fun M hM => ?_⟩
      rw [hf.map_apply, hpre (fun v => ¬ ball (0 : ℂ) 1 ⊆ v.η '' Icc (-M) M)]
      exact hCb M hM
    cellMoments := by
      obtain ⟨h1, h2, h3⟩ := hC'.cellMoments
      refine ⟨fun p hp => ?_, fun p hp hp' => ?_, fun p hp => ?_⟩
      · rw [hf.lintegral_map]
        simp only [hVf]
        exact h1 p hp
      · rw [hf.lintegral_map]
        simp only [hVf]
        exact h2 p hp hp'
      · rw [hf.lintegral_map]
        simp only [hVf]
        exact h3 p hp
    boundaryLawBM := hC.boundaryLawBM_of_map_eq hV hV' hlaw
    boundaryLength := by
      obtain ⟨BL, hBL, hbm, hres⟩ := hC'.boundaryLength
      refine ⟨BL, hBL, ?_, fun b₀ hb₀ => ?_⟩
      · refine hf.ae_map_iff.2 ?_
        simp only [hVf]
        exact hbm
      · refine hf.ae_map_iff.2 ?_
        simp only [hVf]
        exact hres b₀ hb₀
    merge := by
      refine hf.ae_map_iff.2 ?_
      simp only [hVf]
      exact hC'.merge
    onlyMerge := by
      refine hf.ae_map_iff.2 ?_
      simp only [hVf]
      exact hC'.onlyMerge
    visitBound := by
      obtain ⟨k, hk⟩ := hC'.visitBound
      refine ⟨k, hf.ae_map_iff.2 ?_⟩
      simp only [hVf]
      exact hk }

/-- **Couplings on standard Borel spaces give couplings on `ℝ`.** A mating-of-trees coupling on a standard Borel
probability space gives a mating-of-trees coupling on the sample space `ℝ` whose Lebesgue-parametrized curve has the
same law, hence the same code law. -/
theorem exists_isMatingOfTreesCoupling_real_of_standardBorel {Ω : Type} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} {γ : ℝ} {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ (P' : Measure ℝ) (X' X₀' hIG' : ℝ → Field) (C C' C₀ C₀' : ℝ≥0 → ℝ → ℝ) (U' : ℝ → ℝ)
      (ηL' η' η₀' : ℝ → C(ℝ, ℂ)) (bm' : ℝ → Path2),
      IsMatingOfTreesCoupling γ P' X' X₀' hIG' C C' C₀ C₀' U' ηL' η' η₀' bm' ∧
      P'.map (fun ω => slePathCode (ηL' ω)) = P.map (fun ω => slePathCode (ηL ω)) := by
  obtain ⟨V, hV, hCV, hcoord, -⟩ := hC.exists_couplingData
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real (α := Ω)
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  obtain ⟨V', hV', hV'f⟩ := hf.exists_measurable_extend hV fun _ => ⟨V (Classical.arbitrary Ω)⟩
  have hVf : ∀ ω, V' (f ω) = V ω := fun ω => congrFun hV'f ω
  refine ⟨P.map f, fun x => (V' x).X, fun x => (V' x).X₀, fun x => (V' x).hIG, fun t x => (V' x).B t,
    fun t x => (V' x).B' t, fun t x => (V' x).B₀ t, fun t x => (V' x).B₀' t, fun x => (V' x).U,
    fun x => (V' x).ηL, fun x => (V' x).η, fun x => (V' x).η₀, fun x => (V' x).bm,
    isCouplingData_map_of_measurableEmbedding hCV hV hf hV' hVf, ?_⟩
  have hcode : Measurable fun x => slePathCode (V' x).ηL :=
    measurableEmbedding_slePathCode.measurable.comp (CouplingData.measurable_ηL.comp hV')
  rw [Measure.map_map hcode hf.measurable]
  congr 1
  funext ω
  simp only [Function.comp_apply, hVf, (hcoord ω).2.2.2.1]

/-- **Couplings on `ℝ` with a prescribed code law, from couplings on standard Borel spaces.** If for every
`γ ∈ (0, 2)` some mating-of-trees coupling on a standard Borel probability space has a Lebesgue-parametrized curve
with code law `ν (16/γ²)`, then so does some mating-of-trees coupling on the sample space `ℝ`. -/
theorem forall_exists_coupling_real_codeLaw_of_standardBorel {ν : ℝ → Measure SLEPathCode}
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω), StandardBorelSpace Ω ∧
        ∃ (P : Measure Ω) (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
          (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2),
          IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
          P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2) := by
  intro γ hγ0 hγ2
  obtain ⟨Ω, _, _, P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D, hlaw⟩ := hcpl γ hγ0 hγ2
  obtain ⟨P', X', X₀', hIG', C, C', C₀, C₀', U', ηL', η', η₀', bm', D', hlaw'⟩ :=
    exists_isMatingOfTreesCoupling_real_of_standardBorel D
  exact ⟨P', X', X₀', hIG', C, C', C₀, C₀', U', ηL', η', η₀', bm', D', hlaw'.trans hlaw⟩

/-- **Couplings on `ℝ` from couplings on standard Borel spaces.** If for every `γ ∈ (0, 2)` there is a
mating-of-trees coupling on a standard Borel probability space, then there is one on the sample space `ℝ`. -/
theorem forall_exists_coupling_real_of_standardBorel
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω), StandardBorelSpace Ω ∧
        ∃ (P : Measure Ω) (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
          (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2),
          IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm := by
  intro γ hγ0 hγ2
  obtain ⟨Ω, _, _, P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D⟩ := hcpl γ hγ0 hγ2
  obtain ⟨P', X', X₀', hIG', C, C', C₀, C₀', U', ηL', η', η₀', bm', D', -⟩ :=
    exists_isMatingOfTreesCoupling_real_of_standardBorel D
  exact ⟨P', X', X₀', hIG', C, C', C₀, C₀', U', ηL', η', η₀', bm', D'⟩

end MatedCRT.FirstPass.Derived
