import MatedCRT.Proofs.Sec4.Prop42Closure.RestrictedLaw
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureFunctional
import MatedCRT.Proofs.Sec4.Prop42Closure.WholePlaneLQGMeasurable
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureLocalityProof

/-! # Derivation of the restricted LQG law `ConeWholePlaneRestrictedLQGLawStep` (gap G1 of Proposition 4.2)

Inputs: `ConeWholePlaneFieldLawStep` (fact (2) for the fields, IDLA eq. (2.4), `ConeWholePlaneSteps.lean`), the locality
input (A) `LQGMeasureLocalityFunctionalStep` (`LQGMeasureFunctional.lean`; proved, see the next paragraph), and the a.e.
measurability of the LQG measures (cone: `IsConeField.aemeasurable_lqgMeasure`; whole-plane: (B),
`aemeasurable_wholePlaneLQGMeasure`). Measure passage: `identDistrib_restrict_of_finiteDim` (`RestrictedLaw.lean`).

Input (A) is no longer an open input: `LQGMeasureLocalityFunctionalStep_proof` (`LQGMeasureLocalityProof.lean`, steps2:651-794,
commit 48b2c75) proves it with no hypothesis. The reduced-input consumer `coneWholePlaneRestrictedLQGLawStep_of_fieldLaw`
(end of this file) supplies it internally; `coneWholePlaneRestrictedLQGLawStep_of_inputs` keeps (A) as an explicit
hypothesis, for compatibility.

Argument. Let `S = B_1` and let `𝒬` be the countable π-system of open subsets of `S` from `exists_traceSystem`. For each
`Q ∈ 𝒬`, (A) gives a measurable `Λ_Q` with `μ(Q) = Λ_Q(h|_{B_1})` a.s. for the cone field and for the whole-plane field.
Since `𝒬` is countable, these identities hold simultaneously a.s. The restricted fields have the same law (fact (2)), so for
each finite `I ⊆ 𝒬` the vectors `(μ(Q))_{Q∈I}` have the same law in both models: each is the image of the same
measurable map `(Λ_Q)_{Q∈I}` applied to a random element with that common law. This is the hypothesis `hfd` of
`identDistrib_restrict_of_finiteDim`, which gives the equality in law of `μ|_{B_1}` and `μ'|_{B_1}`. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory
open MatedCRT.RestrictedLaw
open scoped ENNReal

/-- Restriction to the unit ball is a measurable map on `Measure ℂ` (through `Measure.measurable_coe`). -/
theorem measurable_restrict_ball : Measurable fun μ : Measure ℂ => μ.restrict (ball (0 : ℂ) 1) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.restrict_apply hs]
  exact Measure.measurable_coe (hs.inter measurableSet_ball)

/-- Two random elements with the same law, compared a.s. with one measurable map `G`, give equal probabilities for the
events `F ⁻¹' s` and `F' ⁻¹' s`. -/
theorem measure_preimage_eq_of_ae {Ω Ω' E T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [MeasurableSpace T] {P : Measure Ω} {P' : Measure Ω'} {X : Ω → E} {X' : Ω' → E}
    (hXX : IdentDistrib X X' P P') {G : E → T} (hG : Measurable G) {F : Ω → T} {F' : Ω' → T}
    (hF : ∀ᵐ ω ∂P, F ω = G (X ω)) (hF' : ∀ᵐ ω' ∂P', F' ω' = G (X' ω')) {s : Set T} (hs : MeasurableSet s) :
    P (F ⁻¹' s) = P' (F' ⁻¹' s) := by
  have h1 : P (F ⁻¹' s) = P (X ⁻¹' (G ⁻¹' s)) := by
    apply measure_congr
    apply Filter.eventuallyEqSet_iff.2
    filter_upwards [hF] with ω hω
    simp only [Set.mem_preimage, hω]
  have h2 : P' (F' ⁻¹' s) = P' (X' ⁻¹' (G ⁻¹' s)) := by
    apply measure_congr
    apply Filter.eventuallyEqSet_iff.2
    filter_upwards [hF'] with ω hω
    simp only [Set.mem_preimage, hω]
  rw [h1, h2, ← Measure.map_apply_of_aemeasurable hXX.aemeasurable_fst (hG hs),
    ← Measure.map_apply_of_aemeasurable hXX.aemeasurable_snd (hG hs), hXX.map_eq]

/-- Almost surely the γ-LQG measure of a whole-plane field is locally finite (its LQG limit is a Radon measure). -/
theorem ae_locallyFinite_of_lqgMeasureOfField {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hL : IsLQGMeasureOfField P γ γ hcirc μ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
  have hL' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage γ (hcirc ω)) (μ ω) := hL
  filter_upwards [hL'] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- **`ConeWholePlaneRestrictedLQGLawStep`, derived.** From fact (2) for the fields (`ConeWholePlaneFieldLawStep`) and the
locality functional (A) (`LQGMeasureLocalityFunctionalStep`), the restrictions to `B_1` of the cone LQG measure and of the
whole-plane LQG measure have the same law. The a.e. measurability (B) of the whole-plane LQG measure is proved, not assumed. -/
theorem coneWholePlaneRestrictedLQGLawStep_of_inputs (hFL : ConeWholePlaneFieldLawStep)
    (hLoc : LQGMeasureLocalityFunctionalStep) : ConeWholePlaneRestrictedLQGLawStep := by
  intro γ hγ0 hγ2 Ω mΩ P hC hcirc μ hcone Ω' mΩ' P' hC' hcirc' μ' hP' hGFF' hL'
  have : IsProbabilityMeasure P := hcone.1
  have : IsProbabilityMeasure P' := hP'
  -- (1) fact (2) for the fields: the restricted fields have the same law
  have hXY : IdentDistrib (coneFieldOnB1 hC hcirc) (wholePlaneFieldOnB1 γ hC' hcirc') P P' :=
    hFL γ hγ0 hγ2 Ω P hC hcirc μ hcone Ω' P' hC' hcirc' hP' hGFF'
  -- (2) a countable trace π-system of the open ball `B_1`
  obtain ⟨𝒬, hQc, hpi, hQ, hSQ, hgen⟩ := exists_traceSystem ℂ isOpen_ball
  -- (3) the locality functionals of the members of `𝒬` (open subsets of `B_1`)
  have hΛ := fun (Q : Set ℂ) (hQ' : Q ∈ 𝒬) => hLoc γ hγ0 hγ2 Q (hQ Q hQ').1 (hQ Q hQ').2
  choose! Λ hΛmeas hΛcone hΛwp using hΛ
  have : Countable 𝒬 := hQc.to_subtype
  -- (4) almost surely, all masses of members of `𝒬` are the functionals of the restricted fields
  have hconeAE : ∀ᵐ ω ∂P, ∀ Q : 𝒬, μ ω Q.1 = Λ Q.1 (coneFieldOnB1 hC hcirc ω) :=
    ae_all_iff.2 fun Q => hΛcone Q.1 Q.2 Ω P hC hcirc μ hcone
  have hwpAE : ∀ᵐ ω' ∂P', ∀ Q : 𝒬, μ' ω' Q.1 = Λ Q.1 (wholePlaneFieldOnB1 γ hC' hcirc' ω') :=
    ae_all_iff.2 fun Q => hΛwp Q.1 Q.2 Ω' P' hC' hcirc' μ' hP' hGFF' hL'
  -- (5) measurability (cone: IsConeField.aemeasurable_lqgMeasure; whole-plane: (B)) and finiteness on `B_1`
  have hμ : AEMeasurable μ P := hcone.aemeasurable_lqgMeasure
  have hμ' : AEMeasurable μ' P' := aemeasurable_wholePlaneLQGMeasure hGFF' hL'
  have hXm : AEMeasurable (fun ω => (μ ω).restrict (ball (0 : ℂ) 1)) P :=
    measurable_restrict_ball.comp_aemeasurable hμ
  have hXm' : AEMeasurable (fun ω' => (μ' ω').restrict (ball (0 : ℂ) 1)) P' :=
    measurable_restrict_ball.comp_aemeasurable hμ'
  have hXS : ∀ ω, (μ ω).restrict (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)ᶜ = 0 := fun ω => by
    rw [Measure.restrict_apply' measurableSet_ball, Set.compl_inter_self, measure_empty]
  have hX'S : ∀ ω', (μ' ω').restrict (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)ᶜ = 0 := fun ω' => by
    rw [Measure.restrict_apply' measurableSet_ball, Set.compl_inter_self, measure_empty]
  have hXfin : ∀ᵐ ω ∂P, (μ ω).restrict (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ≠ ∞ := by
    filter_upwards [ae_isLocallyFiniteMeasure_of_isConeField hcone] with ω hω
    rw [Measure.restrict_apply' measurableSet_ball, Set.inter_self]
    exact (measure_ball_lt_top (μ := μ ω)).ne
  have hX'fin : ∀ᵐ ω' ∂P', (μ' ω').restrict (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ≠ ∞ := by
    filter_upwards [ae_locallyFinite_of_lqgMeasureOfField hL'] with ω' hω'
    rw [Measure.restrict_apply' measurableSet_ball, Set.inter_self]
    exact (measure_ball_lt_top (μ := μ' ω')).ne
  -- (6) the finite-dimensional laws of the masses on `𝒬` agree
  have hXs : ∀ (ν : Measure ℂ) (Q : Set ℂ), Q ⊆ ball (0 : ℂ) 1 → ν.restrict (ball (0 : ℂ) 1) Q = ν Q := by
    intro ν Q hQS
    rw [Measure.restrict_apply' measurableSet_ball, Set.inter_eq_left.2 hQS]
  have hfd : ∀ (I : Finset 𝒬) (s : Set (I → ℝ≥0∞)), MeasurableSet s →
      P ((fun (ω : Ω) (i : I) => massFamily 𝒬 ((μ ω).restrict (ball (0 : ℂ) 1)) i.1) ⁻¹' s) =
        P' ((fun (ω' : Ω') (i : I) => massFamily 𝒬 ((μ' ω').restrict (ball (0 : ℂ) 1)) i.1) ⁻¹' s) := by
    intro I s hs
    have hG : Measurable (fun (x : (TestB1 → ℝ) × (CircleB1 → ℝ)) (i : I) => Λ i.1.1 x) :=
      Measurable.of_eval fun (i : I) => hΛmeas i.1.1 i.1.2
    refine measure_preimage_eq_of_ae hXY hG ?_ ?_ hs
    · filter_upwards [hconeAE] with ω hω
      funext i
      simp only [massFamily]
      rw [hXs (μ ω) i.1.1 (hQ i.1.1 i.1.2).2]
      exact hω i.1
    · filter_upwards [hwpAE] with ω' hω'
      funext i
      simp only [massFamily]
      rw [hXs (μ' ω') i.1.1 (hQ i.1.1 i.1.2).2]
      exact hω' i.1
  -- (7) measure passage from the masses on `𝒬` to the restricted laws
  exact identDistrib_restrict_of_finiteDim (𝒬 := 𝒬) (S := ball (0 : ℂ) 1) hpi
    (fun Q hQ' => ⟨(hQ Q hQ').1.measurableSet, (hQ Q hQ').2⟩) hSQ hgen hXm hXm' hXS hX'S hXfin hX'fin hfd

/-- **`ConeWholePlaneRestrictedLQGLawStep`, reduced inputs.** The restricted-law consumer with the locality input (A)
supplied internally by the proof `LQGMeasureLocalityFunctionalStep_proof` (steps2:651-794, commit 48b2c75). Its only
remaining input is fact (2) for the fields, `ConeWholePlaneFieldLawStep`; the conclusion is that of
`coneWholePlaneRestrictedLQGLawStep_of_inputs`, which it specializes at the proved locality Step. -/
theorem coneWholePlaneRestrictedLQGLawStep_of_fieldLaw (hFL : ConeWholePlaneFieldLawStep) :
    ConeWholePlaneRestrictedLQGLawStep :=
  coneWholePlaneRestrictedLQGLawStep_of_inputs hFL LQGMeasureLocalityFunctionalStep_proof

end MatedCRT
