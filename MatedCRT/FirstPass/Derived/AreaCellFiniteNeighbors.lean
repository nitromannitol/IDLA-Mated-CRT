import MatedCRT.FirstPass.Derived.AreaCellConfig
import MatedCRT.Proofs.Infra.DiscretePotential

/-! # Finite conductance neighborhoods of curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- Symmetry of multiplicities gives symmetry of area-cell conductances. -/
theorem areaCellConfig_conductance_symm {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hsymm : ∀ a b, m a b = m b a)
    (A B : (areaCellConfig h hε m).cells) :
    (areaCellConfig h hε m).c A B = (areaCellConfig h hε m).c B A := by
  obtain ⟨a, rfl⟩ := (euclideanCellEquiv h hε).surjective A
  obtain ⟨b, rfl⟩ := (euclideanCellEquiv h hε).surjective B
  rw [areaCellConfig_conductance, areaCellConfig_conductance, hsymm]

/-- Area-cell conductances are nonnegative. -/
theorem areaCellConfig_conductance_nonneg {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (A B : (areaCellConfig h hε m).cells) :
    0 ≤ (areaCellConfig h hε m).c A B := by
  obtain ⟨a, rfl⟩ := (euclideanCellEquiv h hε).surjective A
  obtain ⟨b, rfl⟩ := (euclideanCellEquiv h hε).surjective B
  rw [areaCellConfig_conductance]
  exact Nat.cast_nonneg _

/-- Loop-free multiplicities give zero diagonal conductances. -/
theorem areaCellConfig_conductance_self {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hloop : ∀ a, m a a = 0) (A : (areaCellConfig h hε m).cells) :
    (areaCellConfig h hε m).c A A = 0 := by
  obtain ⟨a, rfl⟩ := (euclideanCellEquiv h hε).surjective A
  rw [areaCellConfig_conductance, hloop, Nat.cast_zero]

/-- A locally finite multigraph gives each area cell finitely many nonzero neighbors. -/
theorem areaCellConfig_conductance_neighbors_finite {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (A : (areaCellConfig h hε m).cells) :
    {B : (areaCellConfig h hε m).cells | (areaCellConfig h hε m).c A B ≠ 0}.Finite := by
  obtain ⟨a, rfl⟩ := (euclideanCellEquiv h hε).surjective A
  apply ((hlf a).image (euclideanCellEquiv h hε)).subset
  intro B hB
  obtain ⟨b, rfl⟩ := (euclideanCellEquiv h hε).surjective B
  refine ⟨b, ?_, rfl⟩
  change (areaCellConfig h hε m).c (euclideanCellEquiv h hε a)
    (euclideanCellEquiv h hε b) ≠ 0 at hB
  rw [areaCellConfig_conductance, Nat.cast_ne_zero] at hB
  exact hB

/-- Every finite set of cells is contained in a finite region retaining all its neighbors. -/
theorem areaCellConfig_exists_finite_conductance_region {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (A : Set (areaCellConfig h hε m).cells)
    (hA : A.Finite) :
    ∃ R : Set (areaCellConfig h hε m).cells, R.Finite ∧ A ⊆ R ∧
      ∀ v ∈ A, ∀ w, w ∉ R → (areaCellConfig h hε m).c v w = 0 := by
  let N : (areaCellConfig h hε m).cells → Set (areaCellConfig h hε m).cells :=
    fun v => {w | (areaCellConfig h hε m).c v w ≠ 0}
  let R := A ∪ ⋃ v ∈ A, N v
  have hN : (⋃ v ∈ A, N v).Finite :=
    Set.Finite.biUnion hA (fun v _ => areaCellConfig_conductance_neighbors_finite h hε m hlf v)
  refine ⟨R, hA.union hN, Set.subset_union_left, ?_⟩
  intro v hv w hw
  by_contra hne
  apply hw
  exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, hne⟩⟩)

end MatedCRT
