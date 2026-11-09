import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.FirstPass.S2g.ProcessMeasurable
import MatedCRT.Proofs.Measurability.BoundaryLayer
import MatedCRT.Proofs.IDLA.UpperEventMeasurable
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfSteps

/-! # Proposition 6.1 from the corrected Lemma 2.4, canonical form (q1, fp-S2g)

The Section 6 chain takes the Draft Lemma 2.4 `ConeHarmonicBallsUpToFixedTimeStmt` (`Draft/Section2.lean:66-72`) as the
hypothesis `h24` of `MatedCRTEnv.IsValid.exists_measurable_familyProcess` (`Proofs/Measurability/BoundaryLayer.lean:369`),
of `boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable` (`BoundaryLayer.lean:415`), of the upper-event lemmas
(`Proofs/IDLA/UpperEventMeasurable.lean:115,174`) and of `iDLAUpperBound_of_steps` (`Proofs/Sec6/IDLAUpperBound/OfSteps.lean:303`).
The Draft clause `T' = T` is not part of the corrected Lemma 2.4; the chain only uses the existence of an a.s. stopped family
whose space-time process is measurable, and the corrected statement `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` supplies it.

This file restates that chain with the canonical statement in place of `h24`. Each copied proof is the shared one with
`hS.exists_measurable_familyProcess hγ hγ2 hfam h24` replaced by `hS.exists_measurable_familyProcess_canonical hγ hγ2 hcan`;
`hfam` (`ConeFamilyAEMeasurableStep`) is dropped because it only fed that call. The shared consumers are not edited.

Terminology: Lemma 2.4 (canonical stopping time `halfBallTime`, harmonic balls of the cone), Proposition 6.1 (IDLA upper bound,
`prop:IDLA-upper-bound`), Lemma 6.10 (`IterativeBoundStmt`), Proposition 5.1 (`IDLALowerBoundStmt`). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Measurable space-time process from the canonical Lemma 2.4 (q1, fp-S2g).** The conclusion of
`MatedCRTEnv.IsValid.exists_measurable_familyProcess` (`Proofs/Measurability/BoundaryLayer.lean:369`), obtained from the
canonical statement `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` through `exists_measurable_familyProcess_of_canonical`
(`FirstPass/S2g/ProcessMeasurable.lean`), with no Draft clause `T' = T`. -/
theorem MatedCRTEnv.IsValid.exists_measurable_familyProcess_canonical {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ∃ X : Ω → ℝ × ℂ → Prop, (∀ p, Measurable fun ω => X ω p) ∧ ∀ᵐ ω ∂S.P, ∃ (T : ℝ) (Λ' : ℝ → Set ℂ),
      0 < T ∧ IsConeHarmonicBallFamilyOn (S.μ ω) Λ' T ∧ IsStoppedAtHalfBall Λ' T ∧
        ∀ (t : ℝ) (x : ℂ), X ω (t, x) ↔ t ∈ Ioo 0 T ∧ x ∈ Λ' t :=
  exists_measurable_familyProcess_of_canonical hγ hγ2 hcan hS.isConeField

/-- **`BoundaryLayerMeasurableStep` of Proposition 6.1 from the canonical Lemma 2.4 (q1, fp-S2g).** The proof of
`boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable` (`Proofs/Measurability/BoundaryLayer.lean:415`) with the canonical
measurable space-time process. -/
theorem boundaryLayerMeasurableStep_of_canonical (𝒮 : SpaceFillingSLEModel)
    (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) : BoundaryLayerMeasurableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t δ₁ s ht _
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess_canonical hγ hγ2 hcan
  have hf : AEMeasurable (fun ω => S.μ ω (boundaryLayerOfTrace δ₁ {z | X ω (t, z)})) S.P :=
    aemeasurable_measure_boundaryLayerOfTrace hS.aemeasurable_lqg_mass (V := fun ω => {z | X ω (t, z)})
      (fun j => hXm (t, densePoint j)) δ₁
  have hF : NullMeasurableSet ({ω | ∃ q : ℚ, t < q ∧ X ω ((q : ℝ), 0) ∧
      ∀ j, X ω ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3} ∩
      {ω | ENNReal.ofReal s ≤ S.μ ω (boundaryLayerOfTrace δ₁ {z | X ω (t, z)})}) S.P :=
    (measurableSet_exitTest hXm t ρ).nullMeasurableSet.inter (hf.nullMeasurable measurableSet_Ici)
  refine hF.congr ?_
  filter_upwards [hΛ, hX] with ω hΛω hXω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  exact propext (boundaryLayerEvent_iff hΛω hT hΛ' hstop hXω hρ hρ1 ht).symm

section UpperEventCanonical

open Classical

/-- **The fixed-cluster upper-bound event is null measurable, from the canonical Lemma 2.4 (q1, fp-S2g).** The proof of
`MatedCRTEnv.IsValid.nullMeasurableSet_upper_cluster_event` (`Proofs/IDLA/UpperEventMeasurable.lean:115`). -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_upper_cluster_event_canonical
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {t : ℝ} (ht : 0 < t) (ε δ : ℝ) (hε : 0 ≤ ε) (A : Set ℤ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      ¬ fillCells ε (S.η ω) A ⊆ outerNbhd δ (Λ ω t)} S.P := by
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess_canonical hγ hγ2 hcan
  obtain ⟨Y, Y₀, hIG₀, B, B', B₀, B₀', W, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let V : Ω → Set ℂ := fun ω => {z | X ω (t, z)}
  let U : Ω → Set ℂ := fun ω => openSetOfTrace (V ω)
  have hV (j : ℕ) : MeasurableSet {ω | densePoint j ∈ V ω} :=
    measurableSet_setOfPred.2 (hXm (t, densePoint j))
  have hE : MeasurableSet {ω | ¬ fillCells ε (η' ω) A ⊆ outerNbhd δ (U ω)} :=
    measurableSet_fillCells_not_subset_outerNbhd ε δ hε A η' hc.measurable_curves.2.1 U
      (fun ω => isOpen_openSetOfTrace (V ω)) (fun j => measurable_openSetOfTrace_mem V hV _)
  have hF := measurableSet_exitTest hXm t ρ
  refine (hF.inter hE).nullMeasurableSet.congr ?_
  filter_upwards [hΛ, hX, hbridge] with ω hΛω hXω hηω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  obtain ⟨hcl, htT⟩ := lt_clusterExitTime_iff_of_familyProcess hΛω hT hΛ' hstop hXω hρ hρ1 ht
  have heq : EqOn Λ' (Λ ω) (Ioo 0 T) := by
    have h := (hΛω.isConeHarmonicBallFamilyOn hT).eqOn hΛ'
    rwa [min_self] at h
  have hU : t < clusterExitTime (Λ ω) ρ → U ω = Λ ω t := by
    intro hx
    have ht' := htT hx
    have htrace : V ω = Λ ω t := by
      ext z
      change X ω (t, z) ↔ z ∈ Λ ω t
      rw [hXω t z, heq ht']
      exact and_iff_right ht'
    have hreg := hΛω.2.1.isRegularOpen t ht
    change openSetOfTrace (V ω) = Λ ω t
    rw [htrace]
    apply openSetOfTrace_eq
    · rw [← hreg]; exact isOpen_interior
    · exact hreg
  apply propext
  change ((∃ q : ℚ, t < q ∧ X ω ((q : ℝ), 0) ∧
      ∀ j, X ω ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3) ∧ _) ↔ _
  rw [← hcl]
  constructor <;> rintro ⟨hx, hy⟩ <;> refine ⟨hx, ?_⟩
  · simpa [hU hx, hηω.1] using hy
  · simpa [hU hx, hηω.1] using hy

/-- **Proposition 6.1 transfers from sectionwise probabilities to the joint outer law, canonical form (q1, fp-S2g).** The proof
of `joint_iDLAUpperBound_of_sectionwise` (`Proofs/IDLA/UpperEventMeasurable.lean:174`) with the canonical Lemma 2.4. -/
theorem joint_iDLAUpperBound_of_sectionwise_canonical (𝒮 : SpaceFillingSLEModel)
    (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    (hupper : IDLAUpperBoundSectionwiseStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
      Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)})
        (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  apply (hupper γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht).congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact hS.idlaProb_eq_joint_environmentCluster ε
    (fun ω A => t < clusterExitTime (Λ ω) ρ ∧ ¬ fillCells ε (S.η ω) A ⊆ outerNbhd δ (Λ ω t))
    (fun A _ => hS.nullMeasurableSet_upper_cluster_event_canonical hγ hγ2 hcan hρ hρ1 hΛ ht ε δ hε.le A) _

end UpperEventCanonical

/-- **The sectionwise upper bound of Proposition 6.1 transferred to the joint law, canonical form (q1, fp-S2g).** The proof of
`iDLAUpperBound_of_steps` (`Proofs/Sec6/IDLAUpperBound/OfSteps.lean:303`) with the canonical Lemma 2.4. -/
theorem iDLAUpperBound_of_steps_canonical (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hm : BoundaryLayerMeasurableStep 𝒮)
    (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) : IDLAUpperBoundStmt 𝒮 :=
  joint_iDLAUpperBound_of_sectionwise_canonical 𝒮 hcan
    (IDLAUpperBound.iDLAUpperBoundSectionwise_of_steps 𝒮 h610 h51 hm)

/-- **Proposition 6.1 (prop:IDLA-upper-bound) from the corrected Lemma 2.4, canonical form (q1, fp-S2g).** Hypotheses:
Lemma 6.10 (`IterativeBoundStmt`), Proposition 5.1 (`IDLALowerBoundStmt`) and the canonical Lemma 2.4
(`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`). The Draft clause `T' = T` is not used. -/
theorem firstPass_6_1_canonical24 (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) : IDLAUpperBoundStmt 𝒮 :=
  iDLAUpperBound_of_steps_canonical 𝒮 h610 h51 (boundaryLayerMeasurableStep_of_canonical 𝒮 hcan) hcan

/-- **Proposition 6.1 from the canonical factorization (q1, fp-S2g).** `firstPass_6_1_canonical24` with the canonical
Lemma 2.4 `firstPass_2_4_canonical_of_factor` (`FirstPass/S2g/Canonical.lean:69`). The only NEW hypothesis is
`ConeCanonicalFactorStep` (OPEN, `FirstPass/S2g/Canonical.lean:32`). -/
theorem firstPass_6_1_canonical24_of_factor (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hfac : ConeCanonicalFactorStep) : IDLAUpperBoundStmt 𝒮 :=
  firstPass_6_1_canonical24 𝒮 h610 h51 (firstPass_2_4_canonical_of_factor hfac)

end MatedCRT
