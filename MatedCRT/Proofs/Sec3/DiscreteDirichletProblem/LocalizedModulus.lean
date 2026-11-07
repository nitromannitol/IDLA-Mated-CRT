import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ModulusFromRandomBounds

/-! Localizing the discrete modulus to cells meeting the domain. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Agreement on the cells meeting a region gives agreement of the rescaled
    functions on each subset of that region, almost surely. -/
theorem MatedCRTEnv.IsValid.ae_rescale_eqOn_of_cellVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (D K : Set ℂ) (hKD : K ⊆ D)
    (F G : Ω → ℤ → ℝ)
    (hEq : ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) D, F ω a = G ω a) :
    ∀ᵐ ω ∂S.P, EqOn (rescale (S.mε ε) ε (S.η ω) (F ω))
      (rescale (S.mε ε) ε (S.η ω) (G ω)) K := by
  filter_upwards [hEq, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω heq harea hp
  intro x hx
  have hcell := Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
  have ha : vertexOf ε (S.η ω) x ∈ cellVertices ε (S.η ω) D :=
    ⟨x, hcell, hKD hx⟩
  simp only [rescale, heq _ ha]

/-- A modulus in probability transfers between fields whose rescaled versions
    agree almost surely on the compact set at each positive mesh. -/
theorem modulus_of_ae_eqOn
    {Ω α : Type*} [MeasurableSpace Ω] (P : Measure Ω) [PseudoMetricSpace α]
    (K : Set α) (F G : ℝ → Ω → α → ℝ)
    (hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, EqOn (F ε ω) (G ε ω) K)
    (t : ℝ) {e : ℝ≥0∞}
    (hG : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |G ε ω x - G ε ω y|} ≤ e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e := by
  obtain ⟨δ, hδ, hmod⟩ := hG
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmod, self_mem_nhdsWithin] with ε hε hεpos
  have heq : P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} =
      P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |G ε ω x - G ε ω y|} := by
    apply measure_congr
    filter_upwards [hEq ε hεpos] with ω hω
    apply propext
    constructor <;> rintro ⟨x, hx, y, hy, hxy, hval⟩
    · exact ⟨x, hx, y, hy, hxy, by simpa only [hω hx, hω hy] using hval⟩
    · exact ⟨x, hx, y, hy, hxy, by simpa only [hω hx, hω hy] using hval⟩
  rw [heq]
  exact hε

/-- The modulus transfers when the two discrete fields agree on the cells
    meeting a domain containing the compact set. -/
theorem MatedCRTEnv.IsValid.rescale_modulus_of_ae_eqOn_cellVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (D K : Set ℂ) (hKD : K ⊆ D) (F G : ℝ → Ω → ℤ → ℝ)
    (hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      ∀ a ∈ cellVertices ε (S.η ω) D, F ε ω a = G ε ω a)
    (t : ℝ) {e : ℝ≥0∞}
    (hG : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (G ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (G ε ω) y|} ≤ e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  apply modulus_of_ae_eqOn S.P K _ _ ?_ t hG
  intro ε hε
  exact hS.ae_rescale_eqOn_of_cellVertices ε hε D K hKD (F ε) (G ε) (hEq ε hε)

end MatedCRT
