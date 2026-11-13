import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianPathFacts
import MatedCRT.Proofs.MatingOfTrees.BrownianLocalMin

/-!
# The Peanosphere of a valid environment

For a valid environment `S` (`MatedCRTEnv.IsValid`), the mating-of-trees coupling carries a
continuous version `η'` of the space-filling curve `S.η`. This file shows that almost surely the
boundary-length pair `S.bm ω` and the version `η' ω` form a Peanosphere in the sense of
Bonanno's `MatedCRTHarmonic.RouteM.Peanosphere` (continuity, surjectivity and transience of the
curve, the identification of times by the contour functions (Duplantier–Miller–Sheffield (2014),
Lemmas 8.8 and 8.14), recurrence of both Brownian coordinates on both half-lines, and distinct
local-minimum values), and that the cells `H^ε_{εx} = η([ε(x - 1), εx])` of Definition 1.2 are the
images of the cell intervals under the version.

* `ae_exists_lrCoord_lt_of_isCorrelatedBM2`: each coordinate of a correlated two-sided Brownian
  path goes below every level at arbitrarily late and arbitrarily early times, almost surely;
* `ae_peanosphere_of_isMatingOfTreesCoupling`: the Peanosphere of a mating-of-trees coupling
  (after Bonanno's `MoTInput.ae_peanosphere`);
* `MatedCRTEnv.IsValid.ae_peanosphere_cell_of_ae_eq`: the Peanosphere and the cell identity for
  every version of the curve;
* `MatedCRTEnv.IsValid.exists_curve_peanosphere`: a continuous version of the curve with both.
-/

open MeasureTheory Filter Set
open scoped NNReal

namespace MatedCRT

/-- Each coordinate of a correlated two-sided Brownian path goes below every level `M` at some
time after `T` and at some time before `-T`, for all `M` and `T`, almost surely (recurrence of
linear Brownian motion on both half-lines). -/
theorem ae_exists_lrCoord_lt_of_isCorrelatedBM2 {γ : ℝ}
    {μ : Measure MatedCRTHarmonic.MatedCRT.Path2}
    (hμ : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ) (i : Fin 2) :
    ∀ᵐ ω ∂μ, ∀ M T : ℝ,
      (∃ t ≥ T, MatedCRTHarmonic.MatedCRT.lrCoord i t ω < M) ∧
        (∃ t ≤ -T, MatedCRTHarmonic.MatedCRT.lrCoord i t ω < M) := by
  have hpos := MatedCRTHarmonic.MatedCRT.BrownianPathFacts.ae_unboundedBelowInt
    (MatedCRTHarmonic.MatedCRT.coordinate_isPreBrownianReal hμ i)
    (fun n => MatedCRTHarmonic.MatedCRT.measurable_lrCoord (i, (n : ℝ)))
  have hneg := MatedCRTHarmonic.MatedCRT.BrownianPathFacts.ae_unboundedBelowInt
    (MatedCRTHarmonic.MatedCRT.coordinate_neg_isPreBrownianReal hμ i)
    (fun n => MatedCRTHarmonic.MatedCRT.measurable_lrCoord (i, -(n : ℝ)))
  filter_upwards [hpos, hneg] with ω hpos hneg M T
  obtain ⟨m, hm⟩ := exists_nat_gt (-M)
  have hkT : T ≤ (⌈max T 0⌉₊ : ℝ) := (le_max_left T 0).trans (Nat.le_ceil (max T 0))
  obtain ⟨n, hkn, hn⟩ := hpos m ⌈max T 0⌉₊
  obtain ⟨n', hkn', hn'⟩ := hneg m ⌈max T 0⌉₊
  have hTn : T ≤ (n : ℝ) := hkT.trans (by exact_mod_cast hkn)
  have hTn' : T ≤ (n' : ℝ) := hkT.trans (by exact_mod_cast hkn')
  have hmM : -(m : ℝ) ≤ M := by linarith
  refine ⟨⟨(n : ℝ), hTn, ?_⟩, ⟨-(n' : ℝ), by linarith, ?_⟩⟩
  · exact lt_of_lt_of_le hn hmM
  · exact lt_of_lt_of_le hn' hmM

/-- Almost surely, the area-parametrized curve `η` and the boundary-length pair `bm` of a
mating-of-trees coupling form a Peanosphere: the curve is continuous, surjective and transient
(it is an increasing reparametrization of the Lebesgue-parametrized space-filling SLE `ηL`), it
identifies exactly the times identified by the contour functions (Duplantier–Miller–Sheffield
(2014), Lemmas 8.8 and 8.14), and both coordinates of `bm` are recurrent on both half-lines with
distinct local-minimum values (`bm` has the correlated two-sided Brownian law). After Bonanno's
`MoTInput.ae_peanosphere`. -/
theorem ae_peanosphere_of_isMatingOfTreesCoupling {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀
      bm) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.RouteM.Peanosphere (bm ω) (η ω) := by
  have hbm : AEMeasurable bm P := D.measurable_curves.2.2.2.aemeasurable
  have hL := ae_of_ae_map hbm (ae_exists_lrCoord_lt_of_isCorrelatedBM2 D.boundaryLawBM 0)
  have hR := ae_of_ae_map hbm (ae_exists_lrCoord_lt_of_isCorrelatedBM2 D.boundaryLawBM 1)
  have hMin := ae_of_ae_map hbm (MatedCRTHarmonic.MatedCRT.ae_locMinDistinct D.boundaryLawBM)
  filter_upwards [D.spaceFilling, D.areaParam, D.merge, D.onlyMerge, hL, hR, hMin]
    with ω hspace harea hmerge honly hlimL hlimR hmin
  obtain ⟨hsurjL, htransL, -, -⟩ := hspace
  obtain ⟨⟨φ, -, hηeq⟩, -⟩ := harea
  have hηfun : ⇑(η ω) = ⇑(ηL ω) ∘ φ := funext hηeq
  refine ⟨(η ω).continuous, fun z => ?_, ?_, hmerge, honly, hlimL, hlimR, hmin⟩
  · obtain ⟨t, ht⟩ := hsurjL z
    exact ⟨φ.symm t, by rw [hηeq, φ.apply_symm_apply, ht]⟩
  · rw [hηfun]
    exact htransL.comp φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact

/-- For a valid environment and every version `η'` of the curve (`η' ω = S.η ω` almost surely),
almost surely the boundary-length pair `S.bm ω` and `η' ω` form a Peanosphere, and the cells
`H^ε_{εx} = S.η ω ([ε(x - 1), εx])` (Definition 1.2) are the images of the cell intervals under
`η' ω`, for every `ε` and every `x`. -/
theorem MatedCRTEnv.IsValid.ae_peanosphere_cell_of_ae_eq {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    (∀ᵐ ω ∂S.P, MatedCRTHarmonic.RouteM.Peanosphere (S.bm ω) (η' ω)) ∧
      (∀ᵐ ω ∂S.P, ∀ ε : ℝ, ∀ x : ℤ,
        cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ηc, _, hC, hae⟩ := hS.matingOfTrees
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_peanosphere_of_isMatingOfTreesCoupling hC, hae, hη'] with ω hP hω hω'
    rw [hω', ← hω.1]
    exact hP
  · filter_upwards [hη'] with ω hω ε x
    rw [cell, hω]

/-- For a valid environment, the curve of the mating-of-trees coupling is a continuous version
`η'` of `S.η` such that almost surely `S.bm ω` and `η' ω` form a Peanosphere and the cells
`H^ε_{εx}` of `S.η ω` (Definition 1.2) are the images `η' ω ([ε(x - 1), εx])`. -/
theorem MatedCRTEnv.IsValid.exists_curve_peanosphere {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ η' : Ω → C(ℝ, ℂ), (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) ∧
      (∀ᵐ ω ∂S.P, MatedCRTHarmonic.RouteM.Peanosphere (S.bm ω) (η' ω)) ∧
      (∀ᵐ ω ∂S.P, ∀ ε : ℝ, ∀ x : ℤ,
        cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ηc, _, _, hae⟩ := hS.matingOfTrees
  have hηc : ∀ᵐ ω ∂S.P, ⇑(ηc ω) = S.η ω := hae.mono fun _ h => h.1
  exact ⟨ηc, hηc, MatedCRTEnv.IsValid.ae_peanosphere_cell_of_ae_eq S hS hηc⟩

end MatedCRT
