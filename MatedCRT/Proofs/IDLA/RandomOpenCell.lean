import MatedCRT.Proofs.IDLA.UpperEventMeasurable

/-! # Cells meeting a random open set -/

namespace MatedCRT

open Set MeasureTheory Metric Topology Filter
open Classical

/-- Membership of a measurable random point in the open reconstruction of a trace. -/
theorem measurable_openSetOfTrace_random_mem {Ω : Type*} [MeasurableSpace Ω]
    (V : Ω → Set ℂ) (hV : ∀ j, MeasurableSet {ω | densePoint j ∈ V ω})
    (z : Ω → ℂ) (hz : Measurable z) :
    MeasurableSet {ω | z ω ∈ openSetOfTrace (V ω)} := by
  apply measurableSet_setOfPred.2
  simp only [openSetOfTrace, mem_iUnion, exists_prop]
  refine Measurable.exists fun d => Measurable.exists fun k => ?_
  apply Measurable.and
  · unfold innerBallTest
    exact Measurable.forall fun j => measurable_const.imp (measurableSet_setOfPred.1 (hV j))
  · exact measurableSet_setOfPred.1 (measurableSet_lt (hz.dist measurable_const) measurable_const)

/-- A continuous curve's cell meets a random reconstructed open set on a measurable event. -/
theorem measurableSet_cellVertices_openSetOfTrace {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (hε : 0 ≤ ε) (k : ℤ) (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (V : Ω → Set ℂ) (hV : ∀ j, MeasurableSet {ω | densePoint j ∈ V ω}) :
    MeasurableSet {ω | k ∈ cellVertices ε (η ω) (openSetOfTrace (V ω))} := by
  let I : Set ℝ := Icc (ε * (k - 1)) (ε * k)
  have hI : I.Nonempty := by
    apply nonempty_Icc.mpr
    nlinarith
  let : Nonempty I := hI.to_subtype
  let sample : ℕ → I := TopologicalSpace.denseSeq I
  have hdense : DenseRange sample := TopologicalSpace.denseRange_denseSeq I
  have heq : {ω | k ∈ cellVertices ε (η ω) (openSetOfTrace (V ω))} =
      ⋃ j : ℕ, {ω | η ω (sample j) ∈ openSetOfTrace (V ω)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨x, ⟨s, hs, rfl⟩, hx⟩
      let W : Set I := {s | η ω s ∈ openSetOfTrace (V ω)}
      have hW : IsOpen W := (isOpen_openSetOfTrace (V ω)).preimage
        ((η ω).continuous.comp continuous_subtype_val)
      obtain ⟨j, hj⟩ := hdense.exists_mem_open hW ⟨⟨s, hs⟩, hx⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨η ω (sample j), ⟨sample j, (sample j).property, rfl⟩, hj⟩
  rw [heq]
  refine MeasurableSet.iUnion fun j => measurable_openSetOfTrace_random_mem V hV _ ?_
  exact (continuous_eval_const (sample j : ℝ)).measurable.comp hη

/-- A cell meeting the harmonic ball before the exit time is a null-measurable event. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_cellVertices_coneFamily
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hfam : ConeFamilyAEMeasurableStep)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {t : ℝ} (ht : 0 < t) (ε : ℝ) (hε : 0 ≤ ε) (k : ℤ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      k ∈ cellVertices ε (S.η ω) (Λ ω t)} S.P := by
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess hγ hγ2 hfam h24
  obtain ⟨Y, Y₀, hIG₀, B, B', B₀, B₀', W, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let V : Ω → Set ℂ := fun ω => {z | X ω (t, z)}
  let U : Ω → Set ℂ := fun ω => openSetOfTrace (V ω)
  have hV (j : ℕ) : MeasurableSet {ω | densePoint j ∈ V ω} :=
    measurableSet_setOfPred.2 (hXm (t, densePoint j))
  have hE : MeasurableSet {ω | k ∈ cellVertices ε (η' ω) (U ω)} :=
    measurableSet_cellVertices_openSetOfTrace ε hε k η' hc.measurable_curves.2.1 V hV
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

end MatedCRT
