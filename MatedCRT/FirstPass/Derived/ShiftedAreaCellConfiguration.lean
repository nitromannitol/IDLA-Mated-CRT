import MatedCRT.FirstPass.Derived.ShiftedAreaCellGeometry

/-! # Configuration of time-shifted area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- A matching embedding and compatible multiplicities give a shifted cell configuration. -/
theorem shiftedAreaCellConfig_isCellConfiguration
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ)))
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hcompat : ∀ a b, 0 < m a b → G.adj.Adj a b) :
    (shiftedAreaCellConfig h hε θ m).IsCellConfiguration := by
  classical
  let C := shiftedAreaCellConfig h hε θ m
  have houtL : ∀ K K', K ∉ C.cells → C.c K K' = 0 := by
    intro K K' hK
    simp only [C, shiftedAreaCellConfig] at hK ⊢
    simp [hK]
  have houtR : ∀ K K', K' ∉ C.cells → C.c K K' = 0 := by
    intro K K' hK'
    simp only [C, shiftedAreaCellConfig] at hK' ⊢
    split <;> simp_all
  have hmem : ∀ K K', C.Adj K K' → K ∈ C.cells ∧ K' ∈ C.cells := by
    intro K K' hpos
    constructor
    · by_contra hn
      have hz := houtL K K' hn
      change 0 < C.c K K' at hpos
      rw [hz] at hpos
      exact (lt_irrefl 0) hpos
    · by_contra hn
      have hz := houtR K K' hn
      change 0 < C.c K K' at hpos
      rw [hz] at hpos
      exact (lt_irrefl 0) hpos
  refine ⟨shiftedAreaCellConfig_locallyFinite h hε θ m H hH,
    shiftedAreaCellConfig_isConnected h hε θ m H hH,
    shiftedAreaCellConfig_interior_nonempty h hε θ m H hH,
    shiftedAreaCellConfig_iUnion_eq_univ h hε θ m H hH,
    shiftedAreaCellConfig_volume_inter h hε θ m H hH, ?_, ?_, hmem, ?_, ?_⟩
  · intro K K'
    by_cases hK : K ∈ C.cells
    · by_cases hK' : K' ∈ C.cells
      · obtain ⟨a, rfl⟩ := hK
        obtain ⟨b, rfl⟩ := hK'
        change 0 ≤ C.c (shiftedEuclideanCellEquiv h hε θ a)
          (shiftedEuclideanCellEquiv h hε θ b)
        rw [shiftedAreaCellConfig_conductance]
        exact Nat.cast_nonneg _
      · rw [houtR K K' hK']
    · rw [houtL K K' hK]
  · intro K K'
    by_cases hK : K ∈ C.cells
    · by_cases hK' : K' ∈ C.cells
      · obtain ⟨a, rfl⟩ := hK
        obtain ⟨b, rfl⟩ := hK'
        change C.c (shiftedEuclideanCellEquiv h hε θ a)
          (shiftedEuclideanCellEquiv h hε θ b) =
          C.c (shiftedEuclideanCellEquiv h hε θ b)
          (shiftedEuclideanCellEquiv h hε θ a)
        rw [shiftedAreaCellConfig_conductance, shiftedAreaCellConfig_conductance, hsymm]
      · rw [houtR K K' hK', houtL K' K hK']
    · rw [houtL K K' hK, houtR K' K hK]
  · intro K K' hpos heq
    subst K'
    obtain ⟨a, rfl⟩ := (hmem K K hpos).1
    change 0 < C.c (shiftedEuclideanCellEquiv h hε θ a)
      (shiftedEuclideanCellEquiv h hε θ a) at hpos
    rw [shiftedAreaCellConfig_conductance, hloop, Nat.cast_zero] at hpos
    exact (lt_irrefl 0) hpos
  · intro K K' hpos
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hmem K K' hpos
    have hp : 0 < m a b := by
      change 0 < C.c (shiftedEuclideanCellEquiv h hε θ a)
        (shiftedEuclideanCellEquiv h hε θ b) at hpos
      rw [shiftedAreaCellConfig_conductance, Nat.cast_pos] at hpos
      exact hpos
    obtain ⟨z, hz, hz'⟩ := H.inter_of_adj a b (hcompat a b hp)
    refine ⟨Complex.orthonormalBasisOneI.repr z, ?_, ?_⟩
    · rw [coe_euclideanCell, ← hH]
      exact ⟨z, hz, rfl⟩
    · rw [coe_euclideanCell, ← hH]
      exact ⟨z, hz', rfl⟩

end MatedCRT
