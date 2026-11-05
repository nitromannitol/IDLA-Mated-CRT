import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialLocalization

/-! Conditional estimates on measurable covers of an arbitrary event. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- An almost-everywhere measurable cover can localize a conditional estimate
without requiring the conditioning event itself to be null measurable. -/
theorem tendsToOneOn_of_ae_measurable_cover
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Set Ω) (G : ℕ → Set Ω) (E : ℝ → Set Ω)
    (hmono : Monotone G) (hmeas : ∀ n, NullMeasurableSet (G n) P)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ n, ω ∈ G n)
    (hE : ∀ n, TendsToOneOn P (F ∩ G n) E) : TendsToOneOn P F E := by
  have hE' : ∀ n, TendsToOneOn P (G n) (fun ε => Fᶜ ∪ E ε) := by
    intro n
    have hn := hE n
    unfold TendsToOneOn at hn ⊢
    convert hn using 1
    ext ε
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, mem_union]
    tauto
  have hlim := tendsToOneOn_iUnion_of_monotone P G (fun ε => Fᶜ ∪ E ε) hmono hmeas hE'
  unfold TendsToOneOn at hlim ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono_ae
  filter_upwards [hcover] with ω hω hbad
  exact ⟨mem_iUnion.mpr (hω hbad.1), fun h => h.elim (fun hn => hn hbad.1) hbad.2⟩

end MatedCRT.Sec7
