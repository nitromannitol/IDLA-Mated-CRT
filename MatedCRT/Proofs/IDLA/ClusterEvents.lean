import MatedCRT.Proofs.IDLA.WalkerLawMeasurable
import MatedCRT.Proofs.Sec6.AbelianIDLA.Exchange

/-! # Joint measurability of IDLA cluster events

The vertex sets may depend measurably on the environment.
-/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory

/-- A random vertex set with null-measurable coordinates has a jointly measurable modification. -/
theorem exists_measurable_random_vertexSet_ae {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Ω → Set ℤ) (hU : ∀ k, NullMeasurableSet {ω | k ∈ U ω} P) :
    ∃ V : Ω → Set ℤ, (∀ k, MeasurableSet {ω | k ∈ V ω}) ∧ ∀ᵐ ω ∂P, V ω = U ω := by
  classical
  choose A hsub hA hAe using fun k => (hU k).exists_measurable_subset_ae_eq
  refine ⟨fun ω => {k | ω ∈ A k}, fun k => hA k, ?_⟩
  have h : ∀ᵐ ω ∂P, ∀ k, ω ∈ A k ↔ k ∈ U ω := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hAe k] with ω hω
    exact iff_of_eq hω
  filter_upwards [h] with ω hω
  ext k
  exact hω k

/-- Finite stopped IDLA runs are jointly measurable when membership in the stopping domain is
measurable. The proof conditions successively on each walker's first exit and whether the exit
site belongs to the stopping domain. -/
theorem measurableSet_foldl_random_idlaStep {Ω : Type} [MeasurableSpace Ω]
    (U : Ω → Set ℤ) (hU : ∀ k, MeasurableSet {ω | k ∈ U ω}) :
    ∀ (n : ℕ) (s : Set ℤ × List ℤ) (P : Set ℤ × List ℤ → Prop),
      MeasurableSet {p : Ω × (Fin n → ℕ → ℤ) |
        P ((List.ofFn p.2).foldl (idlaStep (U p.1)) s)}
  | 0, s, P => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, List.foldl_nil]
    exact MeasurableSet.const _
  | n + 1, s, P => by
    classical
    let test : Option ℤ → Bool → Set Ω := fun o v =>
      match o with
      | none => univ
      | some z => if v then {ω | z ∈ U ω} else {ω | z ∉ U ω}
    let fixed : Bool → Set ℤ := fun v => if v then univ else ∅
    have htest (o : Option ℤ) (v : Bool) : MeasurableSet (test o v) := by
      cases o with
      | none => exact MeasurableSet.univ
      | some z =>
        cases v with
        | false => exact (hU z).compl
        | true => exact hU z
    have hstep (ω : Ω) (o : Option ℤ) (v : Bool) (hv : ω ∈ test o v) :
        AbelianIDLA.stepOpt (U ω) s o = AbelianIDLA.stepOpt (fixed v) s o := by
      cases o with
      | none => rfl
      | some z => cases v <;> simp_all [test, fixed, AbelianIDLA.stepOpt]
    have hexists (ω : Ω) (o : Option ℤ) : ∃ v, ω ∈ test o v := by
      cases o with
      | none => exact ⟨false, trivial⟩
      | some z => by_cases hz : z ∈ U ω <;> simp [test, hz]
    have heq : {p : Ω × (Fin (n + 1) → ℕ → ℤ) |
        P ((List.ofFn p.2).foldl (idlaStep (U p.1)) s)} =
        ⋃ o : Option ℤ, ⋃ v : Bool,
          (test o v ×ˢ {xs | firstExitSite s.1 (xs 0) = o}) ∩
          (fun p : Ω × (Fin (n + 1) → ℕ → ℤ) =>
            (p.1, fun i : Fin n => p.2 i.succ)) ⁻¹'
            {p | P ((List.ofFn p.2).foldl (idlaStep (U p.1))
              (AbelianIDLA.stepOpt (fixed v) s o))} := by
      ext ⟨ω, xs⟩
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_prod, mem_preimage,
        List.ofFn_succ, List.foldl_cons, AbelianIDLA.idlaStep_eq_stepOpt]
      constructor
      · intro hp
        obtain ⟨v, hv⟩ := hexists ω (firstExitSite s.1 (xs 0))
        exact ⟨_, v, ⟨hv, rfl⟩, by rw [← hstep ω _ v hv]; exact hp⟩
      · rintro ⟨o, v, ⟨hv, ho⟩, hp⟩
        rw [ho, hstep ω o v hv]
        exact hp
    rw [heq]
    refine MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun v => ?_
    refine ((htest o v).prod ((Absorption.measurableSet_firstExitSite_eq s.1 o).preimage
      (measurable_pi_apply 0))).inter ?_
    exact (measurableSet_foldl_random_idlaStep U hU n (AbelianIDLA.stepOpt (fixed v) s o) P).preimage
      (measurable_fst.prodMk (Measurable.of_eval fun i => (measurable_pi_apply i.succ).comp measurable_snd))

/-- A random stopping domain with measurable vertex membership gives measurable cluster events. -/
theorem measurableSet_random_stoppedIDLACluster_mem {Ω : Type} [MeasurableSpace Ω]
    (U : Ω → Set ℤ) (hU : ∀ k, MeasurableSet {ω | k ∈ U ω}) (n : ℕ) (k : ℤ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | k ∈ stoppedIDLACluster (U p.1) p.2 n} := by
  exact (measurableSet_foldl_random_idlaStep U hU n (∅, []) (fun s => k ∈ s.1)).preimage
    (measurable_fst.prodMk ((measurable_restrictFin n).comp measurable_snd))

/-- Failure of containment in a stopped cluster is jointly measurable for measurable vertex sets. -/
theorem measurableSet_not_subset_random_stoppedIDLACluster {Ω : Type} [MeasurableSpace Ω]
    (O U : Ω → Set ℤ) (hO : ∀ k, MeasurableSet {ω | k ∈ O ω})
    (hU : ∀ k, MeasurableSet {ω | k ∈ U ω}) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n} := by
  have h : {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n} =
      ⋃ k : ℤ, ({p | k ∈ O p.1} ∩ {p | k ∉ stoppedIDLACluster (U p.1) p.2 n}) := by
    ext ⟨ω, xs⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, not_subset]
  rw [h]
  exact MeasurableSet.iUnion fun k => ((hO k).preimage measurable_fst).inter
    (measurableSet_random_stoppedIDLACluster_mem U hU n k).compl

/-- For measurable random domains, the sectionwise and joint probabilities of the stopped
cluster containment event agree. -/
theorem MatedCRTEnv.IsValid.idlaProb_eq_joint_stopped_containment
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) (O U : Ω → Set ℤ)
    (hO : ∀ k, MeasurableSet {ω | k ∈ O ω})
    (hU : ∀ k, MeasurableSet {ω | k ∈ U ω}) (n : ℕ) :
    S.idlaProb ε {p | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n} =
      S.idlaJointMeasure ε {p | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n} := by
  rw [hS.idlaJointMeasure_eq ε]
  exact hS.idlaProb_eq_jointLaw_of_measurable ε
    (measurableSet_not_subset_random_stoppedIDLACluster O U hO hU n)

/-- The same equality holds for coordinatewise null-measurable random vertex sets. -/
theorem MatedCRTEnv.IsValid.idlaProb_eq_joint_stopped_containment_of_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) (O U : Ω → Set ℤ)
    (hO : ∀ k, NullMeasurableSet {ω | k ∈ O ω} S.P)
    (hU : ∀ k, NullMeasurableSet {ω | k ∈ U ω} S.P) (n : ℕ) :
    S.idlaProb ε {p | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n} =
      S.idlaJointMeasure ε {p | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n} := by
  obtain ⟨O', hO', hOeq⟩ := exists_measurable_random_vertexSet_ae S.P O hO
  obtain ⟨U', hU', hUeq⟩ := exists_measurable_random_vertexSet_ae S.P U hU
  let B : Set Ω := {ω | O' ω ≠ O ω ∨ U' ω ≠ U ω}
  have hB : S.P B = 0 := by
    have h : ∀ᵐ ω ∂S.P, ω ∉ B := by
      filter_upwards [hOeq, hUeq] with ω ho hu
      simp [B, ho, hu]
    simpa using ae_iff.1 h
  let E : Set (Ω × (ℕ → ℕ → ℤ)) :=
    {p | ¬ O p.1 ⊆ stoppedIDLACluster (U p.1) p.2 n}
  let E' : Set (Ω × (ℕ → ℕ → ℤ)) :=
    {p | ¬ O' p.1 ⊆ stoppedIDLACluster (U' p.1) p.2 n}
  have hoff (ω : Ω) (hω : ω ∉ B) : O' ω = O ω ∧ U' ω = U ω := by
    simpa [B] using hω
  have h1 : S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε E' := by
    have h := hS.idlaJointMeasure_le_add_env ε E E' B (by
      intro ω hω xs hx
      simpa [E, E', (hoff ω hω).1, (hoff ω hω).2] using hx)
    simpa [hB] using h
  have h2 : S.idlaProb ε E' ≤ S.idlaProb ε E := by
    have h := Sec8.annealedOuterProb_le_of_forall_not_mem S.P
      (fun ω => walkerSequenceLaw (S.mult ε ω) 0) (fun ω => walkerSequenceLaw (S.mult ε ω) 0)
      (fun _ => prob_le_one) E' E B (by
        intro ω hω
        have hs : Prod.mk ω ⁻¹' E' = Prod.mk ω ⁻¹' E := by
          simp [E, E', (hoff ω hω).1, (hoff ω hω).2]
        rw [hs])
    simpa [MatedCRTEnv.idlaProb, hB] using h
  apply le_antisymm (hS.idlaProb_le_jointMeasure ε E)
  calc
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε E' := h1
    _ = S.idlaProb ε E' := (hS.idlaProb_eq_joint_stopped_containment ε O' U' hO' hU' n).symm
    _ ≤ S.idlaProb ε E := h2

/-- The sectionwise and joint probabilities also agree for the unstopped cluster. -/
theorem MatedCRTEnv.IsValid.idlaProb_eq_joint_containment_of_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) (O : Ω → Set ℤ)
    (hO : ∀ k, NullMeasurableSet {ω | k ∈ O ω} S.P) (n : ℕ) :
    S.idlaProb ε {p | ¬ O p.1 ⊆ idlaCluster p.2 n} =
      S.idlaJointMeasure ε {p | ¬ O p.1 ⊆ idlaCluster p.2 n} := by
  exact hS.idlaProb_eq_joint_stopped_containment_of_nullMeasurable ε O (fun _ => univ) hO
    (fun _ => MeasurableSet.univ.nullMeasurableSet) n

/-- A membership event for a stopped aggregate of finitely many walkers is measurable. -/
theorem measurableSet_stoppedIDLACluster_mem (U : Set ℤ) (n : ℕ) (k : ℤ) :
    MeasurableSet {xs : ℕ → ℕ → ℤ | k ∈ stoppedIDLACluster U xs n} := by
  have h := AbelianIDLA.measurableSet_foldl_idlaStep U n (∅, []) (fun s => k ∈ s.1)
  exact h.preimage (measurable_restrictFin n)

/-- Failure of a measurable random set to be contained in a stopped cluster is a joint event. -/
theorem measurableSet_not_subset_stoppedIDLACluster {Ω : Type} [MeasurableSpace Ω]
    (O : Ω → Set ℤ) (hO : ∀ k, MeasurableSet {ω | k ∈ O ω}) (U : Set ℤ) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ stoppedIDLACluster U p.2 n} := by
  have h : {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ stoppedIDLACluster U p.2 n} =
      ⋃ k : ℤ, ({ω | k ∈ O ω} ×ˢ {xs | k ∉ stoppedIDLACluster U xs n}) := by
    ext ⟨ω, xs⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, not_subset]
  rw [h]
  exact MeasurableSet.iUnion fun k => (hO k).prod (measurableSet_stoppedIDLACluster_mem U n k).compl

/-- The corresponding event for the unstopped IDLA cluster is measurable. -/
theorem measurableSet_not_subset_idlaCluster {Ω : Type} [MeasurableSpace Ω]
    (O : Ω → Set ℤ) (hO : ∀ k, MeasurableSet {ω | k ∈ O ω}) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ idlaCluster p.2 n} := by
  exact measurableSet_not_subset_stoppedIDLACluster O hO univ n

end MatedCRT
