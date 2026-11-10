import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # FIRST PASS S2k: plateau values of a rational-indexed family (Tonelli step of the closure proof)

Written argument: `notes/fp-gaps/CHATGPT-closure-inside-cycle.md`, section 4.1, the plateau set (9) and the Tonelli
identity (10): `∫₁² ℙ[r ∈ 𝒫] dr = 0`. Only general measure theory is used here. The random variables `R q`
(rational `q`) are assumed measurable; their identification with the maximal radii of the closed harmonic balls
(Bou-Rabee–Gwynne, Proposition 1.3) is an input of the caller and is not used in this file. -/

open MeasureTheory Set

namespace MatedCRT.FirstPass.S2k

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The plateau values of a rational-indexed family `R : ℚ → Ω → ℝ` at an outcome `ω`: the values `r` with
`R p ω = R q ω = r` for some rationals `0 < p < q`. -/
def plateauValues (R : ℚ → Ω → ℝ) (ω : Ω) : Set ℝ :=
  {r | ∃ p q : ℚ, 0 < p ∧ p < q ∧ R p ω = r ∧ R q ω = r}

omit [MeasurableSpace Ω] in
/-- For every outcome the plateau values form a countable set: each plateau value is a value of `R` at a rational. -/
theorem plateauValues_countable (R : ℚ → Ω → ℝ) (ω : Ω) : (plateauValues R ω).Countable := by
  refine (Set.countable_range (fun q : ℚ => R q ω)).mono ?_
  rintro r ⟨p, _, _, _, hp, _⟩
  exact ⟨p, hp⟩

/-- The graph `{(ω, r) : r ∈ plateauValues R ω}` is measurable in the product σ-algebra, when each `R q` is measurable:
it is a countable union over rationals `p, q` of equality tests between measurable functions. -/
theorem measurableSet_plateauGraph (R : ℚ → Ω → ℝ) (hR : ∀ q, Measurable (R q)) :
    MeasurableSet {x : Ω × ℝ | x.2 ∈ plateauValues R x.1} := by
  have hset : {x : Ω × ℝ | x.2 ∈ plateauValues R x.1}
      = ⋃ p : ℚ, ⋃ q : ℚ, {x : Ω × ℝ | 0 < p ∧ p < q ∧ R p x.1 = x.2 ∧ R q x.1 = x.2} := by
    ext x
    simp only [plateauValues, mem_ofPred_eq, mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun q => ?_
  by_cases h : 0 < p ∧ p < q
  · have hEq : {x : Ω × ℝ | 0 < p ∧ p < q ∧ R p x.1 = x.2 ∧ R q x.1 = x.2}
        = {x : Ω × ℝ | R p x.1 = x.2} ∩ {x : Ω × ℝ | R q x.1 = x.2} := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, h.1, h.2, true_and]
    rw [hEq]
    exact (measurableSet_eq_fun ((hR p).comp measurable_fst) measurable_snd).inter
      (measurableSet_eq_fun ((hR q).comp measurable_fst) measurable_snd)
  · have hEq : {x : Ω × ℝ | 0 < p ∧ p < q ∧ R p x.1 = x.2 ∧ R q x.1 = x.2} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hx
      exact h ⟨hx.1, hx.2.1⟩
    rw [hEq]
    exact MeasurableSet.empty

/-- **Tonelli step (10) of `ConeHalfBallClosureInsideStep`.** For a finite measure `P` on `Ω` and measurable
rational-indexed `R`, for Lebesgue-almost every `r ∈ [1,2]` the plateau event `{r ∈ 𝒫}` is `P`-null. Equivalently
`∫₁² ℙ[r ∈ 𝒫] dr = 0`, the integral being taken with respect to the Lebesgue measure restricted to `[1,2]`. -/
theorem plateau_measure_ae_zero (P : Measure Ω) [IsFiniteMeasure P] (R : ℚ → Ω → ℝ)
    (hR : ∀ q, Measurable (R q)) :
    ∀ᵐ r ∂(volume.restrict (Icc (1 : ℝ) 2)), P {ω | r ∈ plateauValues R ω} = 0 := by
  set E : Set (Ω × ℝ) := {x : Ω × ℝ | x.2 ∈ plateauValues R x.1} with hE
  have hEm : MeasurableSet E := measurableSet_plateauGraph R hR
  -- each fibre over an outcome is Lebesgue-null: the plateau values are countable
  have hfib : ∀ ω, (volume.restrict (Icc (1 : ℝ) 2)) (Prod.mk ω ⁻¹' E) = 0 := by
    intro ω
    have hcount : volume (plateauValues R ω) = 0 := (plateauValues_countable R ω).measure_zero volume
    have hle : (volume.restrict (Icc (1 : ℝ) 2)) (plateauValues R ω) ≤ volume (plateauValues R ω) :=
      Measure.restrict_apply_le _ _
    rw [hcount] at hle
    exact nonpos_iff_eq_zero.1 hle
  -- Tonelli on `P ⊗ Leb|[1,2]`, computed in the two orders
  have hzero : (P.prod (volume.restrict (Icc (1 : ℝ) 2))) E = 0 := by
    rw [Measure.prod_apply hEm]
    simp only [hfib, lintegral_zero]
  rw [Measure.prod_apply_symm hEm] at hzero
  have hpt : (fun r : ℝ => P ((fun ω => (ω, r)) ⁻¹' E)) =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_right hEm)).1 hzero
  filter_upwards [hpt] with r hr
  exact hr
