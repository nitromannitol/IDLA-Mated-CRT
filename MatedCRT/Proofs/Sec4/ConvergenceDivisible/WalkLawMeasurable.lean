import MatedCRT.Proofs.Sec4.ConvergenceDivisible.WalkStepMeasurable
import MatedCRT.Proofs.WalkPotential.Markov

/-! # Measurability of the random walk law -/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal

/-- Every finite path cylinder probability is measurable in the environment. -/
theorem MatedCRTEnv.IsValid.measurable_srwLaw_cylinder
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (a : ℤ) (n : ℕ) (x : ℕ → ℤ) :
    Measurable (fun ω => srwLaw (S.mult ε ω) a {y | ∀ i ≤ n, y i = x i}) := by
  simp_rw [srwLaw_cylinder]
  refine measurable_const.mul (Finset.measurable_prod _ ?_)
  intro i hi
  exact (Measure.measurable_coe (measurableSet_singleton _)).comp
    (hS.measurable_srwStep ε (x i))

/-- Every finite-dimensional marginal of the walk law is measurable in the
environment. -/
theorem MatedCRTEnv.IsValid.measurable_srwLaw_marginal
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (a : ℤ) (n : ℕ) :
    Measurable (fun ω => (srwLaw (S.mult ε ω) a).map
      (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ))) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hres : Measurable (Preorder.frestrictLe n :
      (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) := Preorder.measurable_frestrictLe n
  simp_rw [Measure.map_apply hres hA]
  have heq : (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' A =
      ⋃ x : A, (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1} := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    constructor
    · intro hy
      exact ⟨⟨Preorder.frestrictLe n y, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      simp [hx]
  have hdisj : Pairwise (Disjoint on fun x : A =>
      (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1}) := by
    intro x y hxy
    apply Disjoint.preimage
    exact disjoint_singleton.mpr (fun h => hxy (Subtype.ext h))
  have hsets : ∀ x : A, MeasurableSet ((Preorder.frestrictLe n :
      (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1}) := fun x =>
    (measurableSet_singleton _).preimage (Preorder.measurable_frestrictLe n)
  simp_rw [heq, measure_iUnion hdisj hsets]
  apply Measurable.tsum
  intro x
  let z : ℕ → ℤ := fun i => if hi : i ≤ n then x.1 ⟨i, Finset.mem_Iic.mpr hi⟩ else 0
  have hc : (Preorder.frestrictLe n : (ℕ → ℤ) → ((i : Finset.Iic n) → ℤ)) ⁻¹' {x.1} =
      {y | ∀ i ≤ n, y i = z i} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · intro hy i hi
      have hv := congrFun hy ⟨i, Finset.mem_Iic.mpr hi⟩
      simpa [Preorder.frestrictLe, z, hi] using hv
    · intro hy
      funext i
      have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.property
      simpa [Preorder.frestrictLe, z, hi] using hy i hi
  rw [hc]
  exact hS.measurable_srwLaw_cylinder ε a n z

/-- The full law of simple random walk is measurable in the environment. -/
theorem MatedCRTEnv.IsValid.measurable_srwLaw
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (a : ℤ) : Measurable (fun ω => srwLaw (S.mult ε ω) a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => Measurable (fun ω => srwLaw (S.mult ε ω) a t))
    (s := measurableCylinders (fun _ : ℕ => ℤ)) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht => ?_) (fun t mt ht => ?_)
    (fun f disf mf hf => ?_)
  · obtain ⟨N, A, hA, rfl⟩ : ∃ N A, MeasurableSet A ∧ t = cylinder (Finset.Iic N) A := by
      simpa [measurableCylinders_nat] using ht
    have hm := (Measure.measurable_coe hA).comp (hS.measurable_srwLaw_marginal ε a N)
    have hres : Measurable (Preorder.frestrictLe N :
        (ℕ → ℤ) → ((i : Finset.Iic N) → ℤ)) := Preorder.measurable_frestrictLe N
    change Measurable (fun ω => ((srwLaw (S.mult ε ω) a).map
      (Preorder.frestrictLe N : (ℕ → ℤ) → ((i : Finset.Iic N) → ℤ))) A) at hm
    simp_rw [Measure.map_apply hres hA] at hm
    simpa [cylinder, Preorder.frestrictLe] using hm
  · simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

end MatedCRT
