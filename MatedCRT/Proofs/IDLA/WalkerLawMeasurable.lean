import MatedCRT.Proofs.Sec4.ConvergenceDivisible.WalkLawMeasurable
import MatedCRT.Proofs.IDLA.Walkers
import MatedCRT.Proofs.IDLA.Counts
import MatedCRT.Proofs.Sec8.Annealed

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

/-- The totalized joint measure uses the conditional walker law in any valid environment. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) :
    S.idlaJointMeasure ε = hS.idlaJointLaw ε := by
  classical
  simp only [MatedCRTEnv.idlaJointMeasure, hS.measurable_walkerSequenceLaw ε 0, ↓reduceDIte,
    MatedCRTEnv.IsValid.idlaJointLaw]

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

/-- The joint measure of a measurable event is the integral of its quenched probabilities. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_apply
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    {E : Set (Ω × (ℕ → ℕ → ℤ))} (hE : MeasurableSet E) :
    S.idlaJointMeasure ε E =
      ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' E) ∂S.P := by
  rw [hS.idlaJointMeasure_eq ε]
  exact hS.idlaJointLaw_apply ε hE

/-- On measurable events the sectionwise convention agrees with the joint law. -/
theorem MatedCRTEnv.IsValid.idlaProb_eq_jointLaw_of_measurable
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    {E : Set (Ω × (ℕ → ℕ → ℤ))} (hE : MeasurableSet E) :
    S.idlaProb ε E = hS.idlaJointLaw ε E := by
  rw [hS.idlaJointLaw_apply ε hE]
  let κ : Kernel Ω (ℕ → ℕ → ℤ) := ⟨fun ω => walkerSequenceLaw (S.mult ε ω) 0,
    hS.measurable_walkerSequenceLaw ε 0⟩
  let : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_walkerSequenceLaw _ _⟩
  have hm : Measurable (fun ω => walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' E)) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ) hE
  unfold MatedCRTEnv.idlaProb annealedOuterProb outerLIntegral
  apply le_antisymm
  · exact iInf_le_of_le _ (iInf_le_of_le hm (iInf_le_of_le (le_refl _) le_rfl))
  · refine le_iInf fun g => le_iInf fun _ => le_iInf fun hg => ?_
    exact lintegral_mono hg

/-- The sectionwise outer integral is bounded by the joint outer measure, including for nonmeasurable events. -/
theorem MatedCRTEnv.IsValid.idlaProb_le_jointMeasure
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    (E : Set (Ω × (ℕ → ℕ → ℤ))) : S.idlaProb ε E ≤ S.idlaJointMeasure ε E := by
  let F := toMeasurable (hS.idlaJointLaw ε) E
  calc
    S.idlaProb ε E ≤ S.idlaProb ε F :=
      Sec8.annealedOuterProb_mono _ _ (subset_toMeasurable _ _)
    _ = hS.idlaJointLaw ε F :=
      hS.idlaProb_eq_jointLaw_of_measurable ε (measurableSet_toMeasurable _ _)
    _ = hS.idlaJointLaw ε E := measure_toMeasurable _
    _ = S.idlaJointMeasure ε E := by rw [hS.idlaJointMeasure_eq ε]

/-- Under the joint law, the event that the environment belongs to `B` has probability `P B`, also for
nonmeasurable `B` in the sense of an upper bound for outer measure. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_env_le
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) (B : Set Ω) :
    S.idlaJointMeasure ε (B ×ˢ (univ : Set (ℕ → ℕ → ℤ))) ≤ S.P B := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let κ : Kernel Ω (ℕ → ℕ → ℤ) := ⟨fun ω => walkerSequenceLaw (S.mult ε ω) 0,
    hS.measurable_walkerSequenceLaw ε 0⟩
  let : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_walkerSequenceLaw _ _⟩
  calc
    S.idlaJointMeasure ε (B ×ˢ (univ : Set (ℕ → ℕ → ℤ))) ≤
        S.idlaJointMeasure ε (toMeasurable S.P B ×ˢ univ) :=
      measure_mono (prod_mono (subset_toMeasurable _ _) Subset.rfl)
    _ = S.P B := by
      rw [hS.idlaJointMeasure_eq ε]
      change (S.P ⊗ₘ κ) (toMeasurable S.P B ×ˢ univ) = S.P B
      rw [Measure.compProd_apply_prod (measurableSet_toMeasurable _ _) MeasurableSet.univ]
      simp [κ]

/-- Transfer a joint event by containment outside a bad set of environments. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_le_add_env
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    (E F : Set (Ω × (ℕ → ℕ → ℤ))) (B : Set Ω)
    (h : ∀ ω, ω ∉ B → ∀ xs, (ω, xs) ∈ E → (ω, xs) ∈ F) :
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε F + S.P B := by
  calc
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε (F ∪ B ×ˢ univ) := by
      apply measure_mono
      intro ⟨ω, xs⟩ hx
      by_cases hω : ω ∈ B
      · exact Or.inr ⟨hω, mem_univ xs⟩
      · exact Or.inl (h ω hω xs hx)
    _ ≤ S.idlaJointMeasure ε F + S.idlaJointMeasure ε (B ×ˢ univ) := measure_union_le _ _
    _ ≤ S.idlaJointMeasure ε F + S.P B := add_le_add le_rfl (hS.idlaJointMeasure_env_le ε B)

/-- Compare joint outer probabilities when the graph and the events agree away from a bad
set of environments.  A measurable envelope of the bad set makes the comparison valid even
when the original events and the bad set are not measurable. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_le_of_graph_eq_off_sharp
    {Ω : Type} [MeasurableSpace Ω] {S S' : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮 γ)
    (ε ε' : ℝ) (E F : Set (Ω × (ℕ → ℕ → ℤ))) (B : Set Ω) (hP : S.P = S'.P)
    (hgraph : ∀ ω, ω ∉ B → S.mult ε ω = S'.mult ε' ω)
    (h : ∀ ω, ω ∉ B → ∀ xs, (ω, xs) ∈ E → (ω, xs) ∈ F) :
    S.idlaJointMeasure ε E ≤ S'.idlaJointMeasure ε' F + S.P B := by
  let B' := toMeasurable S.P B
  let F' := toMeasurable (S'.idlaJointMeasure ε') F
  let G := F' \ (B' ×ˢ (univ : Set (ℕ → ℕ → ℤ)))
  have hG : MeasurableSet G := (measurableSet_toMeasurable _ _).diff
    ((measurableSet_toMeasurable _ _).prod MeasurableSet.univ)
  have hfirst : S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε G + S.P B' :=
    hS.idlaJointMeasure_le_add_env ε E G B' (by
      intro ω hω xs hx
      have hωB : ω ∉ B := fun hb => hω (subset_toMeasurable _ _ hb)
      exact ⟨subset_toMeasurable _ _ (h ω hωB xs hx), by simpa using hω⟩)
  have heq : S.idlaJointMeasure ε G = S'.idlaJointMeasure ε' G := by
    rw [hS.idlaJointMeasure_apply ε hG, hS'.idlaJointMeasure_apply ε' hG, ← hP]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ B'
    · have hempty : Prod.mk ω ⁻¹' G = ∅ := by
        ext xs
        simp [G, hω]
      rw [hempty, measure_empty, measure_empty]
    · rw [hgraph ω (fun hb => hω (subset_toMeasurable _ _ hb))]
  calc
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε G + S.P B' := hfirst
    _ = S'.idlaJointMeasure ε' G + S.P B := by rw [heq, show S.P B' = S.P B from measure_toMeasurable B]
    _ ≤ S'.idlaJointMeasure ε' F + S.P B := by
      apply add_le_add ?_ le_rfl
      calc
        S'.idlaJointMeasure ε' G ≤ S'.idlaJointMeasure ε' F' := measure_mono sdiff_subset
        _ = S'.idlaJointMeasure ε' F := measure_toMeasurable F

/-- Transfer joint outer probabilities between environments with identical graph laws off a bad set. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_le_of_graph_eq_off
    {Ω : Type} [MeasurableSpace Ω] {S S' : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮 γ)
    (ε ε' : ℝ) (E F : Set (Ω × (ℕ → ℕ → ℤ))) (B : Set Ω) (hP : S.P = S'.P)
    (hgraph : ∀ ω, ω ∉ B → S.mult ε ω = S'.mult ε' ω)
    (h : ∀ ω, ω ∉ B → ∀ xs, (ω, xs) ∈ E → (ω, xs) ∈ F) :
    S.idlaJointMeasure ε E ≤ S'.idlaJointMeasure ε' F + S.P B + S.P B := by
  let F' := toMeasurable (S'.idlaJointMeasure ε') F
  have hF' : MeasurableSet F' := measurableSet_toMeasurable _ _
  have hfirst : S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε F' + S.P B :=
    hS.idlaJointMeasure_le_add_env ε E F' B (fun ω hω xs hx =>
      subset_toMeasurable _ _ (h ω hω xs hx))
  have hsecond : S.idlaProb ε F' ≤ S'.idlaProb ε' F' + S.P B := by
    unfold MatedCRTEnv.idlaProb
    rw [← hP]
    refine Sec8.annealedOuterProb_le_of_forall_not_mem S.P _ _ (fun ω => prob_le_one) F' F' B ?_
    intro ω hω
    rw [hgraph ω hω]
  rw [hS.idlaProb_eq_jointLaw_of_measurable ε hF',
    hS'.idlaProb_eq_jointLaw_of_measurable ε' hF', ← hS.idlaJointMeasure_eq ε,
    ← hS'.idlaJointMeasure_eq ε'] at hsecond
  calc
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε F' + S.P B := hfirst
    _ ≤ (S'.idlaJointMeasure ε' F' + S.P B) + S.P B := add_le_add hsecond le_rfl
    _ = S'.idlaJointMeasure ε' F + S.P B + S.P B := by rw [show S'.idlaJointMeasure ε' F' =
      S'.idlaJointMeasure ε' F from measure_toMeasurable F]

/-- Bound a joint outer event using a measurable cover with controlled quenched probabilities. -/
theorem MatedCRTEnv.IsValid.idlaJointMeasure_le_of_measurable_cover
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    (E A : Set (Ω × (ℕ → ℕ → ℤ))) (B : Set Ω) (g : Ω → ℝ≥0∞)
    (hEA : E ⊆ A) (hA : MeasurableSet A) (hg : Measurable g)
    (h : ∀ ω, ω ∉ B → walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' A) ≤ g ω) :
    S.idlaJointMeasure ε E ≤ (∫⁻ ω, g ω ∂S.P) + S.P B := by
  let bad : Ω → ℝ≥0∞ := (toMeasurable S.P B).indicator 1
  have hi : ∫⁻ ω, bad ω ∂S.P = S.P B := by
    rw [show bad = (toMeasurable S.P B).indicator 1 from rfl,
      lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
  have hbound (ω : Ω) : walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' A) ≤ g ω + bad ω := by
    by_cases hω : ω ∈ B
    · have hbad : bad ω = 1 := by simp [bad, subset_toMeasurable S.P B hω]
      calc
        walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' A) ≤ 1 := prob_le_one
        _ ≤ g ω + bad ω := by rw [hbad]; exact le_add_self
    · exact (h ω hω).trans le_self_add
  calc
    S.idlaJointMeasure ε E ≤ S.idlaJointMeasure ε A := measure_mono hEA
    _ = ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' A) ∂S.P :=
      hS.idlaJointMeasure_apply ε hA
    _ ≤ ∫⁻ ω, g ω + bad ω ∂S.P := lintegral_mono hbound
    _ = (∫⁻ ω, g ω ∂S.P) + S.P B := by rw [lintegral_add_left hg, hi]

end MatedCRT
