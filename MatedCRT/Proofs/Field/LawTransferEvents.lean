import MatedCRT.Steps.Sec6.AnnulusIterate

/-!
# Transfer of countable families of local events

This isolates the measure-theoretic part of the law transfer needed to apply Leonardo
Bonanno's proof of Gwynne–Miller, Lemma 3.1. The equality of the joint laws of the
local field observables is a separate hypothesis.
-/

namespace MatedCRT

open MeasureTheory Set

/-- If two families of local observables have the same joint law, then local events can
be transferred together, preserving their probabilities and the probabilities that no
event in any finite interval occurs. -/
theorem transfer_local_events_of_joint_law
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {α : ℕ → Type} [∀ k, MeasurableSpace (α k)]
    (P : Measure Ω) (P' : Measure Ω') (X : Ω → ∀ k, α k) (Y : Ω' → ∀ k, α k)
    (hX : Measurable X) (hY : Measurable Y) (hlaw : P.map X = P'.map Y)
    (E : ℕ → Set Ω)
    (hE : ∀ k, ∃ E' : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω => X ω k) inferInstance] E' ∧ E k =ᵐ[P] E') :
    ∃ F : ℕ → Set Ω',
      (∀ k, MeasurableSet[MeasurableSpace.comap (fun ω => Y ω k) inferInstance] (F k)) ∧
      (∀ k, P (E k) = P' (F k)) ∧
      ∀ K, P {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} =
        P' {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ F k} := by
  classical
  choose E' hEm hEa using hE
  have hrep : ∀ k, ∃ A : Set (α k), MeasurableSet A ∧ (fun ω => X ω k) ⁻¹' A = E' k := by
    intro k
    exact MeasurableSpace.measurableSet_comap.mp (hEm k)
  choose A hAm hAX using hrep
  let F : ℕ → Set Ω' := fun k => (fun ω => Y ω k) ⁻¹' A k
  refine ⟨F, ?_, ?_, ?_⟩
  · intro k
    exact MeasurableSpace.measurableSet_comap.mpr ⟨A k, hAm k, rfl⟩
  · intro k
    have hp := congrArg (fun μ : Measure (∀ k, α k) => μ ((fun x => x k) ⁻¹' A k)) hlaw
    rw [Measure.map_apply hX (measurable_pi_apply k (hAm k)),
      Measure.map_apply hY (measurable_pi_apply k (hAm k))] at hp
    change P ((fun ω => X ω k) ⁻¹' A k) = P' (F k) at hp
    have hp' := hp
    rw [hAX k] at hp'
    exact (measure_congr (hEa k)).trans hp'
  · intro K
    let B : Set (∀ k, α k) := {x | ∀ k ∈ Finset.Icc 1 K, x k ∉ A k}
    have hB : MeasurableSet B := by
      have heq : B = ⋂ k ∈ Finset.Icc 1 K, ((fun x : ∀ k, α k => x k) ⁻¹' A k)ᶜ := by
        ext x
        simp [B]
      rw [heq]
      exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        (measurable_pi_apply k (hAm k)).compl
    have hp := congrArg (fun μ : Measure (∀ k, α k) => μ B) hlaw
    rw [Measure.map_apply hX hB, Measure.map_apply hY hB] at hp
    have hae : ∀ᵐ ω ∂P, ∀ k, (ω ∈ E k ↔ ω ∈ E' k) := by
      exact ae_all_iff.mpr (fun k => (hEa k).mono fun _ h => propext_iff.mp h)
    have hnone : {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} =ᵐ[P] X ⁻¹' B := by
      filter_upwards [hae] with ω hω
      simp only [mem_ofPred_eq, mem_preimage, B]
      simp only [← hAX, mem_preimage] at hω
      exact propext (forall_congr' fun k => forall_congr' fun _ => not_congr (hω k))
    exact (measure_congr hnone).trans (by simpa [B, F] using hp)

end MatedCRT
