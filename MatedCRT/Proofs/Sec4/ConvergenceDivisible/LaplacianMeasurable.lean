import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DegreeMeasurable

/-! # Measurability of the discrete Laplacian -/

namespace MatedCRT

open Set MeasureTheory

/-- A countable finitely supported sum of measurable real functions is
measurable, including the default value for infinite support. -/
theorem measurable_finsum_real {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (f : Ω → ι → ℝ) (hf : ∀ i, Measurable fun ω => f ω i) :
    Measurable (fun ω => ∑ᶠ i, f ω i) := by
  classical
  let A : Finset ι → Set Ω := fun s => {ω | ∀ i, i ∉ s → f ω i = 0}
  have hA : ∀ s, MeasurableSet (A s) := by
    intro s
    convert MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun (_ : i ∉ s) =>
      (hf i) (measurableSet_singleton 0))) using 1
    ext ω
    simp [A]
  have hsum : ∀ s ω, ω ∈ A s → (∑ᶠ i, f ω i) = ∑ i ∈ s, f ω i := by
    intro s ω h
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    exact hi (h i his)
  have hfinite : ∀ ω, (∃ s, ω ∈ A s) ↔ (f ω).HasFiniteSupport := by
    intro ω
    constructor
    · rintro ⟨s, hs⟩
      apply s.finite_toSet.subset
      intro i hi
      by_contra his
      exact hi (hs i his)
    · intro h
      refine ⟨h.toFinset, ?_⟩
      intro i hi
      by_contra hne
      exact hi (h.mem_toFinset.mpr hne)
  intro T hT
  let B : Set Ω := ⋃ s, A s
  have hB : MeasurableSet B := MeasurableSet.iUnion hA
  have heq : (fun ω => ∑ᶠ i, f ω i) ⁻¹' T =
      (⋃ s, A s ∩ (fun ω => ∑ i ∈ s, f ω i) ⁻¹' T) ∪
        (if (0 : ℝ) ∈ T then Bᶜ else ∅) := by
    ext ω
    simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff]
    by_cases h : ω ∈ B
    · obtain ⟨s, hs⟩ : ∃ s, ω ∈ A s := mem_iUnion.mp h
      have hb : ω ∉ (if (0 : ℝ) ∈ T then Bᶜ else ∅) := by
        split_ifs <;> simp [h]
      simp only [hb, or_false]
      constructor
      · intro hn
        exact ⟨s, hs, (hsum s ω hs) ▸ hn⟩
      · rintro ⟨s, hs, hn⟩
        exact (hsum s ω hs).symm ▸ hn
    · have hinf : ¬ (f ω).HasFiniteSupport := by
        intro hfω
        exact h (mem_iUnion.mpr ((hfinite ω).mpr hfω))
      have hz : (∑ᶠ i, f ω i) = 0 := finsum_of_not_hasFiniteSupport hinf
      have hb : ω ∈ (if (0 : ℝ) ∈ T then Bᶜ else ∅) ↔ (0 : ℝ) ∈ T := by
        split_ifs with hn <;> simp [hn, h]
      rw [hz]
      constructor
      · intro hn
        exact Or.inr (hb.mpr hn)
      · rintro (⟨s, hs, _⟩ | hn)
        · exact False.elim (h (mem_iUnion.mpr ⟨s, hs⟩))
        · exact hb.mp hn
  rw [heq]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion fun s => (hA s).inter
      ((Finset.measurable_sum s fun i _ => hf i) hT)
  · split_ifs
    · exact hB.compl
    · exact MeasurableSet.empty

/-- The normalized Laplacian of a measurable vertex function is measurable. -/
theorem MatedCRTEnv.IsValid.measurable_mLaplacian
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (u : Ω → ℤ → ℝ) (hu : ∀ k, Measurable fun ω => u ω k)
    (j : ℤ) : Measurable (fun ω => mLaplacian (S.mult ε ω) (u ω) j) := by
  unfold mLaplacian
  have hd : Measurable (fun ω => (mdeg (S.mult ε ω) j : ℝ)) := by
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hS.measurable_mdeg ε j)
  refine hd.inv.mul (measurable_finsum_real _ ?_)
  intro k
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (hS.measurable_mult ε j k)).mul ((hu k).sub (hu j))

end MatedCRT
