import MatedCRT.Defs.Setting

/-! # Saturation of field-and-curve events -/

namespace MatedCRT

open MeasureTheory Set _root_.HarmonicBalls

/-- An event measurable with respect to the field and curve cannot distinguish
two sample points with identical field pairings and identical curves. -/
theorem MatedCRTEnv.envSigma_mem_iff_of_field_curve_eq
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ω ω' : Ω}
    (hh : S.hC ω = S.hC ω') (hη : S.η ω = S.η ω')
    {A : Set Ω} (hA : MeasurableSet[S.envSigma] A) : ω ∈ A ↔ ω' ∈ A := by
  let F : Ω → (((ℂ → ℝ) → ℝ) × (ℝ → ℂ)) := fun x => (S.hC x, S.η x)
  let m : MeasurableSpace (((ℂ → ℝ) → ℝ) × (ℝ → ℂ)) := ⊤
  have hcomp {β : Type} [MeasurableSpace β] (f : (((ℂ → ℝ) → ℝ) × (ℝ → ℂ)) → β) :
      Measurable[m.comap F, inferInstance] (fun x => f (F x)) := by
    exact (Measurable.of_comap_le (show _ ≤ m from le_top)).comp (comap_measurable F)
  have hle : S.envSigma ≤ m.comap F := by
    change fieldSigmaAlgebra 0 S.hC univ ⊔
      (⨆ s : ℝ, MeasurableSpace.comap (fun x => S.η x s) inferInstance) ≤ _
    apply sup_le
    · change (⨆ (φ : ℂ → ℝ) (_ : IsTestFunction univ φ),
        MeasurableSpace.comap (fun x => fieldPairing 0 (S.hC x) φ) inferInstance) ≤ _
      refine iSup_le fun φ => iSup_le fun _ => ?_
      exact (hcomp (fun x => fieldPairing 0 x.1 φ)).comap_le
    · refine iSup_le fun s => ?_
      exact (hcomp (fun x => x.2 s)).comap_le
  obtain ⟨B, _, hB⟩ := MeasurableSpace.measurableSet_comap.mp (hle A hA)
  have hF : F ω = F ω' := Prod.ext hh hη
  rw [← hB]
  change F ω ∈ B ↔ F ω' ∈ B
  rw [hF]

/-- If the boundary-length paths differ at two points with identical field
and curve, the boundary-length path is not field-and-curve measurable. -/
theorem MatedCRTEnv.not_measurable_bm_of_field_curve_eq
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {ω ω' : Ω}
    (hh : S.hC ω = S.hC ω') (hη : S.η ω = S.η ω')
    (hbm : S.bm ω ≠ S.bm ω') : ¬ Measurable[S.envSigma] S.bm := by
  intro hm
  have hA : MeasurableSet[S.envSigma] {x | S.bm x = S.bm ω} :=
    (measurableSet_singleton (S.bm ω)).preimage hm
  have hw : ω' ∈ {x | S.bm x = S.bm ω} :=
    (S.envSigma_mem_iff_of_field_curve_eq hh hη hA).mp rfl
  exact hbm hw.symm

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.envSigma_mem_iff_of_field_curve_eq
#print axioms MatedCRT.MatedCRTEnv.not_measurable_bm_of_field_curve_eq
