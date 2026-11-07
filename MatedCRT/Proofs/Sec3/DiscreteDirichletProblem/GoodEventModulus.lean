import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.LocalizedModulus

/-! # Transfer of oscillation estimates on good events -/

namespace MatedCRT

open Set MeasureTheory
open scoped ENNReal

/-- If two functions agree on a good event, the oscillation event of one is
contained in that of the other, up to the complement of the good event. -/
theorem measure_oscillation_le_of_eqOn_good_event
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) (E : Set Ω) (K : Set α) (F G : Ω → α → ℝ)
    (hEq : ∀ᵐ ω ∂P, ω ∈ E → EqOn (F ω) (G ω) K) (δ t : ℝ) :
    P {ω | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧ t < |F ω x - F ω y|} ≤
      P {ω | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧ t < |G ω x - G ω y|} + P Eᶜ := by
  let A : Set Ω := {ω | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧ t < |F ω x - F ω y|}
  let B : Set Ω := {ω | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧ t < |G ω x - G ω y|}
  have hsub : A ≤ᵐ[P] B ∪ Eᶜ := by
    filter_upwards [hEq] with ω hω hA
    by_cases he : ω ∈ E
    · left
      obtain ⟨x, hx, y, hy, hdist, hval⟩ := hA
      exact ⟨x, hx, y, hy, hdist, by simpa only [hω he hx, hω he hy] using hval⟩
    · exact Or.inr he
  calc
    P A ≤ P (B ∪ Eᶜ) := measure_mono_ae hsub
    _ ≤ P B + P Eᶜ := measure_union_le _ _

/-- Agreement on cells meeting the domain implies agreement of the rescaled
functions on the good event. -/
theorem MatedCRTEnv.IsValid.ae_rescale_eqOn_of_cellVertices_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (E : Set Ω) (D K : Set ℂ) (hKD : K ⊆ D)
    (F G : Ω → ℤ → ℝ)
    (hEq : ∀ᵐ ω ∂S.P, ω ∈ E → ∀ a ∈ cellVertices ε (S.η ω) D, F ω a = G ω a) :
    ∀ᵐ ω ∂S.P, ω ∈ E → EqOn (rescale (S.mε ε) ε (S.η ω) (F ω))
      (rescale (S.mε ε) ε (S.η ω) (G ω)) K := by
  filter_upwards [hEq, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω heq harea hp he
  intro x hx
  have hcell := Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
  have ha : vertexOf ε (S.η ω) x ∈ cellVertices ε (S.η ω) D :=
    ⟨x, hcell, hKD hx⟩
  simp only [rescale, heq he _ ha]

end MatedCRT
