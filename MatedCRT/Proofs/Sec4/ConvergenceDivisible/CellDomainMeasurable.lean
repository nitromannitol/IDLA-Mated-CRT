import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable

/-! # Measurability of the cells meeting a domain -/

namespace MatedCRT

open Set MeasureTheory Topology

/-- Meeting a closed set is a closed condition on a continuous curve's cell. -/
theorem isClosed_curve_cell_meets (ε : ℝ) (k : ℤ) (F : Set ℂ) (hF : IsClosed F) :
    IsClosed {p : C(ℝ, ℂ) | k ∈ cellVertices ε p F} := by
  let I : Set ℝ := Icc (ε * (k - 1)) (ε * k)
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let B : Set (C(ℝ, ℂ) × I) := {p | p.1 p.2 ∈ F}
  have heval : Continuous (fun p : C(ℝ, ℂ) × I => p.1 p.2) :=
    ContinuousEval.continuous_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed (Prod.fst '' B) :=
    isClosedMap_fst_of_compactSpace _ (hF.preimage heval : IsClosed B)
  have heq : Prod.fst '' B = {p : C(ℝ, ℂ) | k ∈ cellVertices ε p F} := by
    ext p
    constructor
    · rintro ⟨⟨q, u⟩, hu, rfl⟩
      exact ⟨q u, ⟨u, u.property, rfl⟩, hu⟩
    · rintro ⟨z, ⟨u, hu, rfl⟩, hz⟩
      exact ⟨(p, ⟨u, hu⟩), hz, rfl⟩
  rwa [heq] at hclosed

/-- Meeting an open set is an open condition on a continuous curve's cell. -/
theorem isOpen_curve_cell_meets (ε : ℝ) (k : ℤ) (U : Set ℂ) (hU : IsOpen U) :
    IsOpen {p : C(ℝ, ℂ) | k ∈ cellVertices ε p U} := by
  let I : Set ℝ := Icc (ε * (k - 1)) (ε * k)
  have heq : {p : C(ℝ, ℂ) | k ∈ cellVertices ε p U} =
      ⋃ u : I, (fun p : C(ℝ, ℂ) => p u) ⁻¹' U := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨z, ⟨u, hu, rfl⟩, hz⟩
      exact ⟨⟨u, hu⟩, hz⟩
    · rintro ⟨u, hu⟩
      exact ⟨p u, ⟨u, u.property, rfl⟩, hu⟩
  rw [heq]
  exact isOpen_iUnion fun u => hU.preimage (continuous_eval_const (u : ℝ))

/-- Cell intersection with a fixed open or closed set has a measurable
version for each vertex of a valid environment. -/
theorem MatedCRTEnv.IsValid.exists_measurable_cellVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (k : ℤ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ A : Set Ω, MeasurableSet A ∧
      ∀ᵐ ω ∂S.P, (ω ∈ A ↔ k ∈ cellVertices ε (S.η ω) D) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let A : Set Ω := {ω | k ∈ cellVertices ε (η' ω) D}
  have hA : MeasurableSet A := by
    rcases hD with hD | hD
    · exact (isOpen_curve_cell_meets ε k D hD).measurableSet.preimage hc.measurable_curves.2.1
    · exact (isClosed_curve_cell_meets ε k D hD).measurableSet.preimage hc.measurable_curves.2.1
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbridge] with ω hω
  change k ∈ cellVertices ε (η' ω) D ↔ k ∈ cellVertices ε (S.η ω) D
  rw [hω.1]

/-- The entire set of vertices whose cells meet a fixed open or closed
set has a measurable version. -/
theorem MatedCRTEnv.IsValid.exists_measurable_cellVertices_set
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ V : Ω → Set ℤ, Measurable V ∧
      ∀ᵐ ω ∂S.P, V ω = cellVertices ε (S.η ω) D := by
  classical
  choose A hA hAe using fun k => hS.exists_measurable_cellVertices ε k D hD
  let V : Ω → Set ℤ := fun ω => {k | ω ∈ A k}
  refine ⟨V, ?_, ?_⟩
  · apply measurable_set_iff.mpr
    intro k
    exact measurableSet_setOfPred.mp (hA k)
  · filter_upwards [ae_all_iff.mpr hAe] with ω hω
    ext k
    exact hω k

/-- The interior vertex set used in the discrete obstacle problem has a
measurable version. -/
theorem MatedCRTEnv.IsValid.exists_measurable_interiorCellVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ V : Ω → Set ℤ, Measurable V ∧
      ∀ᵐ ω ∂S.P, V ω = interiorCellVertices ε (S.η ω) D := by
  obtain ⟨V, hV, hVa⟩ := hS.exists_measurable_cellVertices_set ε D hD
  obtain ⟨W, hW, hWa⟩ := hS.exists_measurable_cellVertices_set ε (frontier D)
    (Or.inr isClosed_frontier)
  refine ⟨fun ω => V ω \ W ω, ?_, ?_⟩
  · apply measurable_set_iff.mpr
    intro k
    exact ((measurable_set_mem k).comp hV).and (((measurable_set_mem k).comp hW).not)
  · filter_upwards [hVa, hWa] with ω hv hw
    simp only [interiorCellVertices, hv, hw]

end MatedCRT
