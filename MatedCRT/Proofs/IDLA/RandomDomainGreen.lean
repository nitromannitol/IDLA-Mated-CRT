import MatedCRT.Proofs.IDLA.ClusterEvents
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.GreenMeasurable

/-! # Green functions on null-measurable random domains -/

namespace MatedCRT

open Set MeasureTheory

/-- The Green function is almost everywhere measurable for a random domain with
null-measurable vertex membership. -/
theorem MatedCRTEnv.IsValid.aemeasurable_greenFn_of_nullMeasurable_domain
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (U : Ω → Set ℤ) (hU : ∀ k, NullMeasurableSet {ω | k ∈ U ω} S.P)
    (a b : ℤ) : AEMeasurable (fun ω => greenFn (S.mult ε ω) (U ω) a b) S.P := by
  obtain ⟨V, hV, hVa⟩ := exists_measurable_random_vertexSet_ae S.P U hU
  have hVm : Measurable V := by
    apply measurable_set_iff.mpr
    intro k
    exact measurableSet_setOfPred.mp (hV k)
  apply (hS.measurable_greenFn ε V hVm a b).aemeasurable.congr
  filter_upwards [hVa] with ω hω
  rw [hω]

end MatedCRT
