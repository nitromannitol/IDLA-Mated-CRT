import MatedCRT.Defs.Notation

/-! Union bounds for the good events used in the shell iteration. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Filter Topology

/-- Two events which hold on `F` with high probability hold jointly on `F`
with high probability. No measurability assumption on the events is needed. -/
theorem tendsToOneOn_inter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Set Ω) (E G : ℝ → Set Ω) (hE : TendsToOneOn P F E)
    (hG : TendsToOneOn P F G) : TendsToOneOn P F (fun ε => E ε ∩ G ε) := by
  unfold TendsToOneOn at hE hG ⊢
  have hlim := hE.add hG
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  calc
    P (F ∩ (E ε ∩ G ε)ᶜ) ≤ P ((F ∩ (E ε)ᶜ) ∪ (F ∩ (G ε)ᶜ)) := by
      apply measure_mono
      intro x hx
      by_cases h : x ∈ E ε
      · exact Or.inr ⟨hx.1, fun hg => hx.2 ⟨h, hg⟩⟩
      · exact Or.inl ⟨hx.1, h⟩
    _ ≤ _ := measure_union_le _ _

/-- A fixed finite family of events which hold with high probability on `F`
also holds simultaneously with high probability on `F`. -/
theorem tendsToOneOn_finset_iInter {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set Ω) (s : Finset ι) (E : ι → ℝ → Set Ω)
    (hE : ∀ i ∈ s, TendsToOneOn P F (E i)) :
    TendsToOneOn P F (fun ε => ⋂ i ∈ s, E i ε) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [TendsToOneOn]
  | @insert a s ha ih =>
    have ha' := hE a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, TendsToOneOn P F (E i) :=
      fun i hi => hE i (Finset.mem_insert_of_mem hi)
    have h := tendsToOneOn_inter P F (E a) (fun ε => ⋂ i ∈ s, E i ε) ha' (ih hs)
    simpa only [Finset.set_biInter_insert] using h

end MatedCRT.Sec7
