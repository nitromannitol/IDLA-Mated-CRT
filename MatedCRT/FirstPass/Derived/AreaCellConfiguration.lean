import MatedCRT.FirstPass.Derived.AreaCellConfigurationNull
import MatedCRT.FirstPass.Derived.AreaCellFiniteNeighbors

/-! # Configuration of area-parametrized curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- The conductance vanishes when the first argument is not a curve cell. -/
theorem areaCellConfig_conductance_eq_zero_of_not_mem_left
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (K K' : Cell)
    (hK : K ∉ (areaCellConfig h hε m).cells) :
    (areaCellConfig h hε m).c K K' = 0 := by
  classical
  simp only [areaCellConfig] at hK ⊢
  simp [hK]

/-- The conductance vanishes when the second argument is not a curve cell. -/
theorem areaCellConfig_conductance_eq_zero_of_not_mem_right
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (K K' : Cell)
    (hK' : K' ∉ (areaCellConfig h hε m).cells) :
    (areaCellConfig h hε m).c K K' = 0 := by
  classical
  simp only [areaCellConfig] at hK' ⊢
  split <;> simp_all

/-- Matching embedding geometry and compatible multiplicities define a cell configuration. -/
theorem areaCellConfig_isCellConfiguration
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0)
    (hcompat : ∀ a b, 0 < m a b → G.adj.Adj a b) :
    (areaCellConfig h hε m).IsCellConfiguration := by
  classical
  let C := areaCellConfig h hε m
  have houtL : ∀ K K', K ∉ C.cells → C.c K K' = 0 :=
    areaCellConfig_conductance_eq_zero_of_not_mem_left h hε m
  have houtR : ∀ K K', K' ∉ C.cells → C.c K K' = 0 :=
    areaCellConfig_conductance_eq_zero_of_not_mem_right h hε m
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
  refine ⟨areaCellConfig_locallyFinite h hε m H hH,
    areaCellConfig_isConnected h hε m H hH,
    areaCellConfig_interior_nonempty h hε m H hH,
    areaCellConfig_iUnion_eq_univ h hε m H hH,
    areaCellConfig_volume_inter h hε m H hH, ?_, ?_, hmem, ?_, ?_⟩
  · intro K K'
    by_cases hK : K ∈ C.cells
    · by_cases hK' : K' ∈ C.cells
      · exact areaCellConfig_conductance_nonneg h hε m ⟨K, hK⟩ ⟨K', hK'⟩
      · rw [houtR K K' hK']
    · rw [houtL K K' hK]
  · intro K K'
    by_cases hK : K ∈ C.cells
    · by_cases hK' : K' ∈ C.cells
      · exact areaCellConfig_conductance_symm h hε m hsymm ⟨K, hK⟩ ⟨K', hK'⟩
      · rw [houtR K K' hK', houtL K' K hK']
    · rw [houtL K K' hK, houtR K' K hK]
  · intro K K' hpos heq
    subst K'
    have hK := (hmem K K hpos).1
    have hz := areaCellConfig_conductance_self h hε m hloop ⟨K, hK⟩
    change 0 < C.c K K at hpos
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  · intro K K' hpos
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hmem K K' hpos
    have hp : 0 < m a b := by
      change 0 < C.c (euclideanCellEquiv h hε a) (euclideanCellEquiv h hε b) at hpos
      rw [areaCellConfig_conductance, Nat.cast_pos] at hpos
      exact hpos
    obtain ⟨z, hz, hz'⟩ := H.inter_of_adj a b (hcompat a b hp)
    refine ⟨Complex.orthonormalBasisOneI.repr z, ?_, ?_⟩
    · rw [coe_euclideanCell, ← hH]
      exact ⟨z, hz, rfl⟩
    · rw [coe_euclideanCell, ← hH]
      exact ⟨z, hz', rfl⟩

end MatedCRT
