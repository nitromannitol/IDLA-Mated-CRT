import MatedCRT.FirstPass.S2g.HalfBallGood
import MatedCRT.FirstPass.S2g.FullImage
import MatedCRT.FirstPass.S2g.GoodSetMoments

/-!
# Reduction of the good-set step to the whole-plane source (q1, fp-S2g)

`ConeHalfBallGoodMeasureLawStep` (`S2g/HalfBallGood.lean`) asks for a measurable set `G` of measures, contained in the
pathwise half-ball inputs, with `μ ω ∈ G` almost surely for a quantum cone field. This file reduces it to three inputs:

* `SourceHalfBallPathwiseStep` (NEW, open): almost surely the pathwise inputs hold for the whole-plane source
  (harmonic balls of Armstrong-Kuusi-Mourrat, Thm 1.1 and Thm 5.5 of the HB paper, Duplantier-Sheffield LQG measure).
* `CandidateConeLogLocalCodeLawStd` (EXTERNAL candidate, not frozen): the moment law of a quantum cone agrees with the
  moment law of a whole-plane source realized on a standard Borel space with measurable measure map. This strengthens
  `FrozenConeLogLocalCodeLaw` (`FirstPass/Frozen/S2h.lean:29`) by the standard-Borel and measurability clauses that the
  Lusin-type full-image lemma `exists_measurable_subset_image_full_law` needs.
* `CandidateMomentSeparation` (EXTERNAL candidate, not frozen): a countable family of test functions on `B_1` determines
  locally finite measures on `B_{3/4}`.

The frozen inputs `FrozenUniversalMeasurabilityOfAnalytic` (`FirstPass/Frozen/S1c.lean:40`) and
`FrozenLQGTestIntegralMeasurable` (`FirstPass/Frozen/S1c.lean`, field-level measurability of `ω ↦ ∫ φ dμ_ω` for cone
fields) are used as hypotheses. Terminology: quantum cone and LQG measure (Duplantier-Miller-Sheffield), harmonic balls
(Armstrong-Kuusi-Mourrat), Green functions and obstacle problem (Armitage-Gardiner).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- **OPEN NEW step (q1, fp-S2g; not frozen).** Almost surely the pathwise half-ball inputs hold for the whole-plane source
`μ ω` of the LQG measure `IsLQGMeasureOfField P γ γ hcirc μ` on the whole-plane GFF `IsWholePlaneGFF P hC hcirc`, with
`α₀ = γ < Q`. Written argument: H1, H3-H6 of `notes/fp-gaps/CHATGPT-q1-open-steps.md` Section 3, from
`ExistenceHarmonicBallsStmt` (HB Draft/Section5.lean:192) and `IsRegularizedClusterFamily` (Draft/Section5.lean:88). -/
def SourceHalfBallPathwiseStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → ∀ᵐ ω ∂P, ConePathwiseHalfBallInputs (μ ω)

/-- **CANDIDATE EXTERNAL (q1; NOT frozen; pending operator approval).** Moment law of a quantum cone against a whole-plane
source on a standard Borel space. For `0 < γ < 2`, every γ-quantum cone field has, for every countable family of
continuous compactly supported test functions in `B_1`, the same law of moment vectors `ω ↦ (∫ φ_k dμ_ω)_k` as a
whole-plane source LQG measure on a standard Borel space with measurable measure map `μ'`
(Duplantier-Sheffield 2011, Invent. Math., arXiv:0808.1560; the quantum cone restriction identity of Fact 2.2 in
arXiv:2211.04891). The cone moment maps are AE measurable by `FrozenLQGTestIntegralMeasurable`; the equality is the law
statement of `FrozenConeLogLocalCodeLaw`. -/
def CandidateConeLogLocalCodeLawStd : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsProbabilityMeasure P' ∧ Measurable μ' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      IsLQGMeasureOfField P' γ γ hcirc' μ' ∧
      ∀ φs : ℕ → ℂ → ℝ, (∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ ball (0 : ℂ) 1) →
        P.map (fun ω => momentVec φs (μ ω)) = P'.map (fun ω' => momentVec φs (μ' ω'))

/-- **CANDIDATE EXTERNAL (q1; NOT frozen; pending operator approval).** Countable determination of locally finite measures
on `B_{3/4}` by test functions supported in `B_1`: finite Radon measures on the open set `B_1` are determined by their
integrals against a countable dense subset of `C_c(B_1)` (Riesz uniqueness plus separability of each `C_c(K_n)`;
standard, e.g. Parthasarathy 1967, Thm II.6.6). -/
def CandidateMomentSeparation : Prop :=
  ∃ φs : ℕ → ℂ → ℝ, (∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ ball (0 : ℂ) 1) ∧
    ∀ ν₁ ν₂ : Measure ℂ, IsLocallyFiniteMeasure ν₁ → IsLocallyFiniteMeasure ν₂ →
      momentVec φs ν₁ = momentVec φs ν₂ →
        ν₁.restrict (ball (0 : ℂ) (3 / 4)) = ν₂.restrict (ball (0 : ℂ) (3 / 4))

/-- An almost sure property has a measurable full-measure event on which it holds pointwise. -/
theorem exists_measurable_ae_subset {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) : ∃ E : Set Ω, MeasurableSet E ∧ P E = 1 ∧ ∀ ω ∈ E, p ω := by
  have h0 : P {ω | ¬ p ω} = 0 := ae_iff.1 h
  refine ⟨(toMeasurable P {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [prob_compl_eq_one_iff (measurableSet_toMeasurable _ _), measure_toMeasurable, h0]
  · intro ω hω
    by_contra hp
    exact hω (subset_toMeasurable P _ hp)

/-- **Reduction (q1, fp-S2g).** The good-set step `ConeHalfBallGoodMeasureLawStep` follows from the source step, the
standard-Borel moment law, the countable separation, the Lusin full-image input and the field-level measurability of the
cone moments, all as hypotheses. -/
theorem coneHalfBallGood_of_source (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hsrc : SourceHalfBallPathwiseStep) (hstd : CandidateConeLogLocalCodeLawStd)
    (hsep : CandidateMomentSeparation) : ConeHalfBallGoodMeasureLawStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨Ω', _, _, P', hC', hcirc', μ', hprob, hμmeas, hGFF, hLQG, hlaw⟩ :=
    hstd γ hγ0 hγ2 Ω P hC hcirc μ hcone
  obtain ⟨φs, hφs, hsepφ⟩ := hsep
  have hφm : ∀ k, Measurable (φs k) := fun k => (hφs k).1.measurable
  -- the source good event and its moments
  obtain ⟨E, hEm, hPE, hEgood⟩ :=
    exists_measurable_ae_subset P' (hsrc γ hγ0 hγ2 Ω' P' hC' hcirc' μ' hprob hGFF hLQG)
  have hF : Measurable (fun ω' => momentVec φs (μ' ω')) := (measurable_momentVec hφm).comp hμmeas
  obtain ⟨B, hBm, hBsub, hBfull⟩ :=
    exists_measurable_subset_image_full_law hU P' (fun ω' => momentVec φs (μ' ω')) hF E hEm hPE
  -- the cone side: local finiteness and measurability of the moments
  have hPprob : IsProbabilityMeasure P := by
    have hc := hcone
    unfold IsConeField at hc
    exact hc.1
  have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := by
    have hc := hcone
    unfold IsConeField at hc
    exact hc.2.2
  have hLf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hL] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hmeask : ∀ k, Measurable (fun ω => ∫ x, φs k x ∂(μ ω)) := fun k =>
    hmeasT γ hγ0 hγ2 Ω P hC hcirc μ hcone (φs k) (hφs k).1 (hφs k).2.1
  have hae : ∀ k, (fun ω => momentVec φs (μ ω) k) =ᵐ[P] (fun ω => ∫ x, φs k x ∂(μ ω)) := by
    intro k
    filter_upwards [hLf] with ω hω
    have := hω
    exact intG_eq_integral (hφs k).1 (hφs k).2.1 (μ ω)
  have hAEM : AEMeasurable (fun ω => momentVec φs (μ ω)) P :=
    AEMeasurable.of_eval fun k => ((hmeask k).aemeasurable).congr (hae k).symm
  -- transfer of the full law to the cone
  have hcone_map : P.map (fun ω => momentVec φs (μ ω)) B = 1 := by
    rw [hlaw φs hφs]
    exact hBfull
  have : IsProbabilityMeasure (P.map (fun ω => momentVec φs (μ ω))) :=
    (Measure.isProbabilityMeasure_map_iff hAEM).mpr inferInstance
  have hA : ∀ᵐ y ∂(P.map (fun ω => momentVec φs (μ ω))), y ∈ B := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hBm).mpr hcone_map
  have hBae : ∀ᵐ ω ∂P, momentVec φs (μ ω) ∈ B :=
    (ae_map_iff (p := fun y => y ∈ B) hAEM hBm).mp hA
  refine ⟨lfMomentSet φs B, measurableSet_lfMomentSet hφm hBm, ?_, ?_⟩
  · intro ν hν
    obtain ⟨hνlf, hνB⟩ := hν
    obtain ⟨ω', hω'E, hFω'⟩ := hBsub hνB
    have hgood' := hEgood ω' hω'E
    have heq : momentVec φs (μ' ω') = momentVec φs ν := hFω'
    have hres := hsepφ (μ' ω') ν hgood'.1 hνlf heq
    exact pathwiseInputs_of_restrict_eq hres hνlf hgood'
  · filter_upwards [hLf, hBae] with ω hωlf hωB
    exact ⟨hωlf, hωB⟩

end MatedCRT
