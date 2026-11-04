import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DegreeMeasurable

/-! # Measurability of the simple random walk transition law -/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The edge measure depends measurably on the environment. -/
theorem MatedCRTEnv.IsValid.measurable_edgeMeasure
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (j : ℤ) : Measurable (fun ω => edgeMeasure (S.mult ε ω) j) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [edgeMeasure, Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  apply Measurable.tsum
  intro k
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
    (hS.measurable_mult ε j k)).mul measurable_const

/-- The simple random walk one-step law depends measurably on the environment. -/
theorem MatedCRTEnv.IsValid.measurable_srwStep
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (j : ℤ) : Measurable (fun ω => srwStep (S.mult ε ω) j) := by
  let μ : Ω → Measure ℤ := fun ω => edgeMeasure (S.mult ε ω) j
  have hμ : Measurable μ := hS.measurable_edgeMeasure ε j
  have hm : Measurable (fun ω => μ ω univ) := (Measure.measurable_coe MeasurableSet.univ).comp hμ
  have hgood : MeasurableSet {ω | μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤} :=
    ((hm (measurableSet_singleton 0)).compl).inter ((hm (measurableSet_singleton ⊤)).compl)
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hvalue : Measurable (fun ω => μ ω A) := (Measure.measurable_coe hA).comp hμ
  change Measurable (fun ω => (if μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤ then (μ ω)[|univ]
    else Measure.dirac j) A)
  have heq : (fun ω => (if μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤ then (μ ω)[|univ]
      else Measure.dirac j) A) =
      (fun ω => if μ ω univ ≠ 0 ∧ μ ω univ ≠ ⊤ then (μ ω univ)⁻¹ * μ ω A
      else (Measure.dirac j) A) := by
    funext ω
    split_ifs <;> simp [cond_apply MeasurableSet.univ]
  rw [heq]
  exact Measurable.ite hgood (hm.inv.mul hvalue) measurable_const

end MatedCRT
