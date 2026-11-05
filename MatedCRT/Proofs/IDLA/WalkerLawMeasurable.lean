import MatedCRT.Proofs.Sec4.ConvergenceDivisible.WalkLawMeasurable
import MatedCRT.Proofs.IDLA.Walkers
import MatedCRT.Proofs.IDLA.Counts

/-! # Measurability of the independent walker sequence

The environment uses Leonardo Bonanno's mating-of-trees bundle, ported in
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`.
-/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal

/-- Finite products of measurable families of probability measures depend measurably on the parameter. -/
theorem measurable_finite_pi_probability {Ω I X : Type*} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace X] (μ : Ω → I → Measure X)
    (hμ : ∀ i, Measurable fun ω => μ ω i)
    (hprob : ∀ ω i, IsProbabilityMeasure (μ ω i)) :
    Measurable (fun ω => Measure.pi (μ ω)) := by
  let : ∀ ω i, IsProbabilityMeasure (μ ω i) := hprob
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => Measurable (fun ω => Measure.pi (μ ω) t))
    (s := Set.pi univ '' Set.pi univ (fun _ : I => {s : Set X | MeasurableSet s}))
    generateFrom_pi.symm isPiSystem_pi (by simp) (fun t ht => ?_) (fun t mt ht => ?_)
    (fun f disf mf hf => ?_)
  · obtain ⟨s, hs, rfl⟩ := ht
    have hs' : ∀ i, MeasurableSet (s i) := fun i => hs i (mem_univ i)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (hs' i)).comp (hμ i))
  · simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

/-- The law of all independent walkers is measurable when the one-walk law is measurable. -/
theorem MatedCRTEnv.IsValid.measurable_walkerSequenceLaw
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (a : ℤ) : Measurable (fun ω => walkerSequenceLaw (S.mult ε ω) a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => Measurable (fun ω => walkerSequenceLaw (S.mult ε ω) a t))
    (s := measurableCylinders (fun _ : ℕ => ℕ → ℤ)) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht => ?_) (fun t mt ht => ?_)
    (fun f disf mf hf => ?_)
  · obtain ⟨N, A, hA, rfl⟩ : ∃ N A, MeasurableSet A ∧ t = cylinder (Finset.Iic N) A := by
      simpa [measurableCylinders_nat] using ht
    have hp : Measurable (fun ω => Measure.pi (fun _ : Finset.Iic N => srwLaw (S.mult ε ω) a)) :=
      measurable_finite_pi_probability _ (fun _ => hS.measurable_srwLaw ε a) (fun _ _ => inferInstance)
    have hm := (Measure.measurable_coe hA).comp hp
    have heq (ω : Ω) : walkerSequenceLaw (S.mult ε ω) a (cylinder (Finset.Iic N) A) =
        Measure.pi (fun _ : Finset.Iic N => srwLaw (S.mult ε ω) a) A :=
      Measure.infinitePi_cylinder (fun _ : ℕ => srwLaw (S.mult ε ω) a) hA
    simpa only [heq, Function.comp_def] using hm
  · simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.tsum hf

/-- The joint law of the environment and the sequence of independent IDLA walkers. -/
noncomputable def MatedCRTEnv.IsValid.idlaJointLaw
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) :
    Measure (Ω × (ℕ → ℕ → ℤ)) :=
  S.P ⊗ₘ (⟨fun ω => walkerSequenceLaw (S.mult ε ω) 0,
    hS.measurable_walkerSequenceLaw ε 0⟩ : Kernel Ω (ℕ → ℕ → ℤ))

/-- On measurable events the joint law integrates the quenched probabilities. -/
theorem MatedCRTEnv.IsValid.idlaJointLaw_apply
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    {E : Set (Ω × (ℕ → ℕ → ℤ))} (hE : MeasurableSet E) :
    hS.idlaJointLaw ε E = ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' E) ∂S.P := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let κ : Kernel Ω (ℕ → ℕ → ℤ) := ⟨fun ω => walkerSequenceLaw (S.mult ε ω) 0,
    hS.measurable_walkerSequenceLaw ε 0⟩
  let : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_walkerSequenceLaw _ _⟩
  exact Measure.compProd_apply hE

end MatedCRT
