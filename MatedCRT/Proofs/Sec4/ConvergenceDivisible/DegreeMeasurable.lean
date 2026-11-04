import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EdgeMeasurable

/-! # Measurability of graph degrees -/

namespace MatedCRT

open Set MeasureTheory

/-- A countable, finitely supported sum of measurable natural-valued
functions is measurable, including the default value for infinite support. -/
theorem measurable_finsum_nat {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (f : Ω → ι → ℕ) (hf : ∀ i, Measurable fun ω => f ω i) :
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
  apply measurable_to_countable'
  intro n
  let B : Set Ω := ⋃ s, A s
  have hB : MeasurableSet B := MeasurableSet.iUnion hA
  have heq : (fun ω => ∑ᶠ i, f ω i) ⁻¹' {n} =
      (⋃ s, A s ∩ {ω | (∑ i ∈ s, f ω i) = n}) ∪
        (if n = 0 then Bᶜ else ∅) := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_iUnion, mem_inter_iff]
    by_cases h : ω ∈ B
    · obtain ⟨s, hs⟩ : ∃ s, ω ∈ A s := mem_iUnion.mp h
      have hb : ω ∉ (if n = 0 then Bᶜ else ∅) := by
        split_ifs <;> simp [h]
      simp only [hb, or_false]
      constructor
      · intro hn
        exact ⟨s, hs, (hsum s ω hs).symm.trans hn⟩
      · rintro ⟨s, hs, hn⟩
        exact (hsum s ω hs).trans hn
    · have hinf : ¬ (f ω).HasFiniteSupport := by
        intro hfω
        exact h (mem_iUnion.mpr ((hfinite ω).mpr hfω))
      have hz : (∑ᶠ i, f ω i) = 0 := finsum_of_not_hasFiniteSupport hinf
      have hb : ω ∈ (if n = 0 then Bᶜ else ∅) ↔ n = 0 := by
        split_ifs with hn <;> simp [hn, h]
      rw [hz]
      constructor
      · intro hn
        exact Or.inr (hb.mpr hn.symm)
      · rintro (⟨s, hs, _⟩ | hn)
        · exact False.elim (h (mem_iUnion.mpr ⟨s, hs⟩))
        · exact (hb.mp hn).symm
  rw [heq]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion fun s => (hA s).inter
      ((Finset.measurable_sum s fun i _ => hf i) (measurableSet_singleton n))
  · split_ifs
    · exact hB.compl
    · exact MeasurableSet.empty

/-- The degree of each vertex in a valid mated-CRT environment is measurable. -/
theorem MatedCRTEnv.IsValid.measurable_mdeg
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (j : ℤ) : Measurable (fun ω => mdeg (S.mult ε ω) j) := by
  exact measurable_finsum_nat (fun ω k => S.mult ε ω j k) (fun k => hS.measurable_mult ε j k)

end MatedCRT
