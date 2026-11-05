import MatedCRT.Proofs.IDLA.ClusterEvents
import MatedCRT.Proofs.IDLA.Monotone

/-! # Environment-dependent events of finite IDLA runs -/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory

/-- An environment-dependent predicate of the final state is jointly measurable
when it is measurable in the environment for every fixed state. -/
theorem measurableSet_foldl_idlaStep_environment {Ω : Type} [MeasurableSpace Ω]
    (U : Set ℤ) (P : Ω → Set ℤ × List ℤ → Prop)
    (hP : ∀ s, MeasurableSet {ω | P ω s}) :
    ∀ (n : ℕ) (s : Set ℤ × List ℤ),
      MeasurableSet {p : Ω × (Fin n → ℕ → ℤ) |
        P p.1 ((List.ofFn p.2).foldl (idlaStep U) s)}
  | 0, s => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, List.foldl_nil]
    exact (hP s).preimage measurable_fst
  | n + 1, s => by
    have h : {p : Ω × (Fin (n + 1) → ℕ → ℤ) |
        P p.1 ((List.ofFn p.2).foldl (idlaStep U) s)} =
        ⋃ o : Option ℤ,
          (fun p : Ω × (Fin (n + 1) → ℕ → ℤ) => p.2 0) ⁻¹'
            {x | firstExitSite s.1 x = o} ∩
          (fun p : Ω × (Fin (n + 1) → ℕ → ℤ) =>
            (p.1, fun i : Fin n => p.2 i.succ)) ⁻¹'
            {p | P p.1 ((List.ofFn p.2).foldl (idlaStep U) (AbelianIDLA.stepOpt U s o))} := by
      ext ⟨ω, xs⟩
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage,
        List.ofFn_succ, List.foldl_cons, AbelianIDLA.idlaStep_eq_stepOpt]
      constructor
      · intro hx
        exact ⟨_, rfl, hx⟩
      · rintro ⟨o, ho, hx⟩
        rw [ho]
        exact hx
    rw [h]
    refine MeasurableSet.iUnion fun o => ?_
    exact ((Absorption.measurableSet_firstExitSite_eq s.1 o).preimage
      ((measurable_pi_apply 0).comp measurable_snd)).inter
      ((measurableSet_foldl_idlaStep_environment U P hP n (AbelianIDLA.stepOpt U s o)).preimage
        (measurable_fst.prodMk (Measurable.of_eval fun i => (measurable_pi_apply i.succ).comp measurable_snd)))

/-- An environment-dependent predicate of an IDLA cluster is jointly measurable
when its fixed-cluster sections are measurable. -/
theorem measurableSet_idlaCluster_environment {Ω : Type} [MeasurableSpace Ω]
    (P : Ω → Set ℤ → Prop) (hP : ∀ A, MeasurableSet {ω | P ω A}) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | P p.1 (idlaCluster p.2 n)} := by
  exact (measurableSet_foldl_idlaStep_environment univ (fun ω s => P ω s.1)
    (fun s => hP s.1) n (∅, [])).preimage
      (measurable_fst.prodMk ((measurable_restrictFin n).comp measurable_snd))

/-- For an IDLA cluster it suffices to check the environmental predicate on
finite vertex sets. -/
theorem measurableSet_idlaCluster_environment_of_finite {Ω : Type} [MeasurableSpace Ω]
    (P : Ω → Set ℤ → Prop) (hP : ∀ A, A.Finite → MeasurableSet {ω | P ω A}) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | P p.1 (idlaCluster p.2 n)} := by
  classical
  let Q : Ω → Set ℤ → Prop := fun ω A => A.Finite ∧ P ω A
  have hQ : ∀ A, MeasurableSet {ω | Q ω A} := by
    intro A
    by_cases hA : A.Finite
    · simpa [Q, hA] using hP A hA
    · simp [Q, hA]
  have hm := measurableSet_idlaCluster_environment Q hQ n
  convert hm using 1
  ext ⟨ω, xs⟩
  have hf : (idlaCluster xs n).Finite :=
    (foldl_idlaStep_card univ (List.ofFn fun i : Fin n => xs i) (∅, []) finite_empty).1
  simp [Q, hf]

/-- Null-measurable environmental tests on finite clusters admit a single
jointly measurable modification, simultaneously for all walker sequences. -/
theorem exists_measurable_idlaCluster_environment_ae {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Ω → Set ℤ → Prop)
    (hP : ∀ A, A.Finite → NullMeasurableSet {ω | P ω A} μ) (n : ℕ) :
    ∃ E : Set (Ω × (ℕ → ℕ → ℤ)), MeasurableSet E ∧
      ∀ᵐ ω ∂μ, ∀ xs, (ω, xs) ∈ E ↔ P ω (idlaCluster xs n) := by
  classical
  choose E hsub hEm hEae using fun A : Finset ℤ =>
    (hP A A.finite_toSet).exists_measurable_subset_ae_eq
  let Q : Ω → Set ℤ → Prop := fun ω A => if hA : A.Finite then ω ∈ E hA.toFinset else False
  have hQ : ∀ A, A.Finite → MeasurableSet {ω | Q ω A} := by
    intro A hA
    simpa [Q, hA] using hEm hA.toFinset
  refine ⟨{p | Q p.1 (idlaCluster p.2 n)},
    measurableSet_idlaCluster_environment_of_finite Q hQ n, ?_⟩
  have hae : ∀ᵐ ω ∂μ, ∀ A : Finset ℤ, ω ∈ E A ↔ P ω A := by
    rw [ae_all_iff]
    intro A
    filter_upwards [hEae A] with ω hω
    exact iff_of_eq hω
  filter_upwards [hae] with ω hω
  intro xs
  have hf : (idlaCluster xs n).Finite :=
    (foldl_idlaStep_card univ (List.ofFn fun i : Fin n => xs i) (∅, []) finite_empty).1
  simpa [Q, hf] using hω hf.toFinset

/-- Sectionwise and joint outer probabilities agree for environmental cluster
predicates with null-measurable sections at every finite cluster. -/
theorem MatedCRTEnv.IsValid.idlaProb_eq_joint_environmentCluster
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    (P : Ω → Set ℤ → Prop) (hP : ∀ A, A.Finite → NullMeasurableSet {ω | P ω A} S.P)
    (n : ℕ) :
    S.idlaSectionProb ε {p | P p.1 (idlaCluster p.2 n)} =
      S.idlaJointMeasure ε {p | P p.1 (idlaCluster p.2 n)} := by
  obtain ⟨E', hE', hEq⟩ := exists_measurable_idlaCluster_environment_ae S.P P hP n
  let E : Set (Ω × (ℕ → ℕ → ℤ)) := {p | P p.1 (idlaCluster p.2 n)}
  let B : Set Ω := {ω | ¬ ∀ xs, (ω, xs) ∈ E' ↔ P ω (idlaCluster xs n)}
  have hB : S.P B = 0 := by
    apply ae_iff.1
    filter_upwards [hEq] with ω hω
    simp [hω]
  have h1 : S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε E' := by
    have h := hS.idlaJointMeasure_le_add_env ε E E' B (by
      intro ω hω xs hx
      exact (not_not.mp hω xs).mpr hx)
    simpa [hB] using h
  have h2 : S.idlaSectionProb ε E' ≤ S.idlaSectionProb ε E := by
    have h := Sec8.annealedOuterProb_le_of_forall_not_mem S.P
      (fun ω => walkerSequenceLaw (S.mult ε ω) 0) (fun ω => walkerSequenceLaw (S.mult ε ω) 0)
      (fun _ => prob_le_one) E' E B (by
        intro ω hω
        have heq : Prod.mk ω ⁻¹' E' = Prod.mk ω ⁻¹' E := by
          ext xs
          exact not_not.mp hω xs
        rw [heq])
    simpa [MatedCRTEnv.idlaSectionProb, hB] using h
  apply le_antisymm (hS.idlaProb_le_jointMeasure ε E)
  calc
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε E' := h1
    _ = S.idlaSectionProb ε E' := by rw [hS.idlaJointMeasure_eq ε, hS.idlaProb_eq_jointLaw_of_measurable ε hE']
    _ ≤ S.idlaSectionProb ε E := h2

end MatedCRT
