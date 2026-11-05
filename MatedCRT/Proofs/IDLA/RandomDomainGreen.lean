import MatedCRT.Proofs.IDLA.ClusterEvents
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.GreenMeasurable

/-! # Green functions on null-measurable random domains -/

namespace MatedCRT

open Set MeasureTheory
open scoped ENNReal

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

/-- The sum of Green functions over a random domain is almost everywhere measurable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_greenFn_sum_of_nullMeasurable_domain
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (U : Ω → Set ℤ) (hU : ∀ k, NullMeasurableSet {ω | k ∈ U ω} S.P)
    (a : ℤ) : AEMeasurable (fun ω => ∑' b : U ω, greenFn (S.mult ε ω) (U ω) b a) S.P := by
  classical
  obtain ⟨V, hV, hVa⟩ := exists_measurable_random_vertexSet_ae S.P U hU
  have hVm : Measurable V := by
    apply measurable_set_iff.mpr
    intro k
    exact measurableSet_setOfPred.mp (hV k)
  have hg : Measurable (fun ω => ∑' b : ℤ,
      if b ∈ V ω then greenFn (S.mult ε ω) (V ω) b a else 0) := by
    apply Measurable.tsum
    intro b
    exact Measurable.ite (hV b) (hS.measurable_greenFn ε V hVm b a) measurable_const
  apply hg.aemeasurable.congr
  filter_upwards [hVa] with ω hω
  rw [hω, tsum_subtype (U ω) (fun b => greenFn (S.mult ε ω) (U ω) b a)]
  congr 1

/-- The vertices satisfying the two Green-function inequalities in the IDLA
lower bound have null-measurable membership. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_greenGoodVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε K q : ℝ) (s : Ω → ℝ) (hs : AEMeasurable s S.P)
    (U : Ω → Set ℤ) (hU : ∀ k, NullMeasurableSet {ω | k ∈ U ω} S.P) (a : ℤ) :
    NullMeasurableSet {ω | a ∈ U ω ∧
      (1 + s ω) * ∑' b : U ω, greenFn (S.mult ε ω) (U ω) b a ≤
        K * greenFn (S.mult ε ω) (U ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : U ω, greenFn (S.mult ε ω) (U ω) b a) /
        greenFn (S.mult ε ω) (U ω) a a} S.P := by
  have hsum := hS.aemeasurable_greenFn_sum_of_nullMeasurable_domain ε U hU a
  have h0 := hS.aemeasurable_greenFn_of_nullMeasurable_domain ε U hU 0 a
  have haa := hS.aemeasurable_greenFn_of_nullMeasurable_domain ε U hU a a
  exact (hU a).inter ((nullMeasurableSet_le ((aemeasurable_const.add hs).mul hsum)
    (aemeasurable_const.mul h0)).inter
      (nullMeasurableSet_le aemeasurable_const (hsum.div haa)))

end MatedCRT
