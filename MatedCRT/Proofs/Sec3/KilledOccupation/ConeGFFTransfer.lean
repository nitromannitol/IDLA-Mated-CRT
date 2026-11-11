import Mathlib
import MatedCRT.Defs.Setting

/-!
# Law of the cone's circle averages on the unit disk (eq:gff), for the killed-occupation clock chain

Printed source (`paper/idla_mated_crt-corrected.tex`, Definition `def:quantum-cone` and display `eq:gff`,
lines 427-445), verbatim:

  `h|_{B_1} \overset{d}{=} ( h^{\C} - \gamma \log |\cdot| )|_{B_1} .`
  (the whole-plane GFF `h^{\C}` normalized so that its circle average over the disk is zero)

The Lean form `ConeUnitDiskGFFLaw` is the equality in law of the circle-average process of the cone on the
unit disk, indexed by the circles `closedBall z r ⊆ B_1`, with the circle averages of a whole-plane GFF
`hc` (`HarmonicBalls.IsWholePlaneGFF`, normalized by `h^ℂ_1(0) = 0`) shifted by `-γ · (average of log|·|)`
(`HarmonicBalls.fieldCircleAverage`). It is an equality in law (`IdentDistrib`), not a pathwise identity.

PENDING TRUTH CHECK (operator to file in the math queue): the printed `eq:gff` is a law identity for the
restriction `h|_{B_1}` alone. It does not carry the base clock `dA` of the occupation identity
(`lem:occ-base`, tex:140-151), which the killed-occupation reduction `frozenLBMGreenOccupationRescaled_of_appendixB`
(OccupationAssembly.lean:178) leaves as a free family. The S6 chain (`hS6`) therefore needs in addition a
joint law of `(hcirc, dA)` or a cone-side identification of `dA` as the limit of the regularized base clocks;
this file does not state it.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The circles `closedBall z r ⊆ B_1` with positive radius: the index set of the circle averages of a field
on the unit disk. -/
def UnitDiskCircleIndex : Set (ℝ × ℂ) :=
  {q | 0 < q.1 ∧ closedBall q.2 q.1 ⊆ ball (0 : ℂ) 1}

/-- **eq:gff in circle-average form** (printed source in the module docstring): for every `γ ∈ (0,2)` and every
valid environment `S` (`S.IsValid 𝒮 γ`), the circle averages of the quantum cone on the unit disk have the law of
the circle averages of `h^ℂ - γ log|·|` on the unit disk for some whole-plane GFF `hc` normalized by `h^ℂ_1(0)=0`.
PENDING TRUTH CHECK. -/
def ConeUnitDiskGFFLaw : Prop :=
  ∀ (𝒮 : SpaceFillingSLEModel) (γ : ℝ), 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
        (hc : Ω' → ℝ → ℂ → ℝ),
        IsProbabilityMeasure P' ∧ HarmonicBalls.IsWholePlaneGFF P' hC' hc ∧
        IdentDistrib (fun ω (q : UnitDiskCircleIndex) => S.hcirc ω q.1.1 q.1.2)
          (fun ω' (q : UnitDiskCircleIndex) => HarmonicBalls.fieldCircleAverage γ (hc ω') q.1.1 q.1.2)
          S.P P'

/-- A family of random variables with measurable coordinates is measurable into the product σ-algebra on the unit
disk index set (positive radii only). -/
lemma measurable_unitDiskCircle {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ → ℂ → ℝ)
    (hf : ∀ r z, 0 < r → Measurable fun ω => f ω r z) :
    Measurable fun ω (q : UnitDiskCircleIndex) => f ω q.1.1 q.1.2 :=
  Measurable.of_eval fun q : UnitDiskCircleIndex => hf q.1.1 q.1.2 q.2.1

/-- Equality in law of a measurable family, transported through a product with a fixed σ-finite measure: the
push-forward of `P ⊗ Q` by `(ω, b) ↦ (X ω, b)` depends only on the law of `X`. -/
lemma map_prod_eq_of_identDistrib {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} {P' : Measure Ω'} [SFinite P] [SFinite P']
    {X : Ω → α} {X' : Ω' → α} (hXm : Measurable X) (hX'm : Measurable X') (hX : IdentDistrib X X' P P')
    (Q : Measure β) [SFinite Q] :
    (P.prod Q).map (fun p => (X p.1, p.2)) = (P'.prod Q).map (fun p => (X' p.1, p.2)) := by
  have hA := Measure.map_prod_map P Q hXm measurable_id
  have hB := Measure.map_prod_map P' Q hX'm measurable_id
  rw [Measure.map_id] at hA hB
  calc (P.prod Q).map (fun p => (X p.1, p.2))
      = (P.prod Q).map (Prod.map X id) := rfl
    _ = (P.map X).prod Q := hA.symm
    _ = (P'.map X').prod Q := by rw [hX.map_eq]
    _ = (P'.prod Q).map (Prod.map X' id) := hB
    _ = (P'.prod Q).map (fun p => (X' p.1, p.2)) := rfl

/-- Probability of an event of the form `{(ω, b) : (X ω, b) ∈ E}` is the same for `X` and `X'` when they have the
same law: the transfer principle used to move the clock chain from the cone to the whole-plane GFF. -/
lemma prod_preimage_eq_of_identDistrib {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} {P' : Measure Ω'} [SFinite P] [SFinite P']
    {X : Ω → α} {X' : Ω' → α} (hXm : Measurable X) (hX'm : Measurable X') (hX : IdentDistrib X X' P P')
    (Q : Measure β) [SFinite Q] {E : Set (α × β)} (hE : MeasurableSet E) :
    (P.prod Q) ((fun p => (X p.1, p.2)) ⁻¹' E) = (P'.prod Q) ((fun p => (X' p.1, p.2)) ⁻¹' E) := by
  have hm : Measurable (fun p : Ω × β => (X p.1, p.2)) := (hXm.comp measurable_fst).prodMk measurable_snd
  have hm' : Measurable (fun p : Ω' × β => (X' p.1, p.2)) :=
    (hX'm.comp measurable_fst).prodMk measurable_snd
  rw [← Measure.map_apply hm hE, ← Measure.map_apply hm' hE,
    map_prod_eq_of_identDistrib hXm hX'm hX Q]

end MatedCRT.KilledOccupation
