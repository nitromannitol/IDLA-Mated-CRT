import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LaplacianMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.GreenMeasurable

/-! # Measurability of discrete supersolution constraints -/

namespace MatedCRT

open Set MeasureTheory

/-- For a measurable candidate, all the inequalities in the discrete
obstacle problem form a measurable event. -/
theorem MatedCRTEnv.IsValid.measurableSet_discreteSupersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ u : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (hu : ∀ b, Measurable fun ω => u ω b) :
    MeasurableSet {ω | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u ω) b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ u ω b} := by
  have hVb : ∀ b, MeasurableSet {ω | b ∈ V ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hV)
  have hWb : ∀ b, MeasurableSet {ω | b ∈ W ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hW)
  have heq : {ω | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u ω) b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ u ω b} =
      (⋂ b, (({ω | b ∈ V ω})ᶜ ∪ {ω | mLaplacian (S.mult ε ω) (u ω) b ≤ r ω b})) ∩
      (⋂ b, (({ω | b ∈ W ω})ᶜ ∪ {ω | φ ω b ≤ u ω b})) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    classical
    simp only [← imp_iff_not_or]
  rw [heq]
  exact (MeasurableSet.iInter fun b => (hVb b).compl.union
    (measurableSet_le (hS.measurable_mLaplacian ε u hu b) (hr b))).inter
    (MeasurableSet.iInter fun b => (hWb b).compl.union (measurableSet_le (hφ b) (hu b)))

end MatedCRT
