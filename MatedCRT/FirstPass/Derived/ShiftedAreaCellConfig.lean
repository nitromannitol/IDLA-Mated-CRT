import MatedCRT.FirstPass.Derived.AreaCellConfig
import MatedCRT.FirstPass.Derived.ShiftedPaperCell
import MatedCRT.FirstPass.Derived.HarnackRingGeometry
import MatedCRT.FirstPass.Derived.SrwCellLaw
import LatticeProb.Topology.ShiftedAreaCellInjective

/-! # Shifted area cells and their random walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- The time-shifted Euclidean cells retain their distinct integer labels. -/
theorem shiftedEuclideanCell_injective {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    Function.Injective (euclideanCell ε (fun t => η (t + ε * θ))
      (h.1.comp (continuous_id.add continuous_const)) hε) := by
  let f : C(ℝ, ℂ) := ⟨η, h.1⟩
  have hf := LatticeProb.shiftedCompactCell_injective_of_areaParametrized f hε θ h.2.2.2
  intro j k hjk
  apply hf
  apply SetLike.coe_injective
  rw [shiftedCompactCell_eq_cell_timeShift f hε.le θ j,
    shiftedCompactCell_eq_cell_timeShift f hε.le θ k]
  apply Set.image_injective.mpr Complex.orthonormalBasisOneI.repr.injective
  exact congrArg (fun K : Cell => (K : Set ReflectedGMS.Plane)) hjk

/-- Integer labels of the time-shifted area cells. -/
def shiftedEuclideanCellEquiv {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    ℤ ≃ Set.range (euclideanCell ε (fun t => η (t + ε * θ))
      (h.1.comp (continuous_id.add continuous_const)) hε) :=
  Equiv.ofInjective _ (shiftedEuclideanCell_injective h hε θ)

/-- The time-shifted cells with conductances given by their integer labels. -/
def shiftedAreaCellConfig {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) : CellConfig := by
  classical
  refine ⟨Set.range (euclideanCell ε (fun t => η (t + ε * θ))
    (h.1.comp (continuous_id.add continuous_const)) hε), ?_⟩
  intro A B
  exact if ha : A ∈ Set.range (euclideanCell ε (fun t => η (t + ε * θ))
      (h.1.comp (continuous_id.add continuous_const)) hε) then
    if hb : B ∈ Set.range (euclideanCell ε (fun t => η (t + ε * θ))
        (h.1.comp (continuous_id.add continuous_const)) hε) then
      (m ((shiftedEuclideanCellEquiv h hε θ).symm ⟨A, ha⟩)
        ((shiftedEuclideanCellEquiv h hε θ).symm ⟨B, hb⟩) : ℝ)
    else 0
    else 0

/-- The shifted cell conductances preserve the multiplicity of every edge. -/
theorem shiftedAreaCellConfig_conductance {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) (a b : ℤ) :
    (shiftedAreaCellConfig h hε θ m).c (shiftedEuclideanCellEquiv h hε θ a)
      (shiftedEuclideanCellEquiv h hε θ b) = (m a b : ℝ) := by
  classical
  simp [shiftedAreaCellConfig, shiftedEuclideanCellEquiv]

/-- The embedded vertex is contained in its shifted cell. -/
theorem shiftedAreaCellConfig_vertex_mem {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (k : ℤ) :
    Complex.orthonormalBasisOneI.repr (vertexPoint ε (fun t => η (t + ε * θ)) k) ∈
      ((shiftedEuclideanCellEquiv h hε θ k).1 : Set ReflectedGMS.Plane) := by
  change _ ∈ (euclideanCell ε (fun t => η (t + ε * θ))
    (h.1.comp (continuous_id.add continuous_const)) hε k : Set ReflectedGMS.Plane)
  rw [coe_euclideanCell]
  exact ⟨_, vertexPoint_mem_cell hε.le _ k, rfl⟩

/-- Relabelling a locally finite positive-degree walk gives the shifted cell walk. -/
theorem shiftedAreaCellConfig_isSRWLaw {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m) (hpos : ∀ a, 0 < mdeg m a)
    (a : ℤ) :
    (shiftedAreaCellConfig h hε θ m).IsSRWLaw (shiftedEuclideanCellEquiv h hε θ a)
      ((srwLaw m a).map (fun p n => shiftedEuclideanCellEquiv h hε θ (p n))) :=
  isSRWLaw_map_srwLaw m hlf hpos (shiftedAreaCellConfig h hε θ m)
    (shiftedEuclideanCellEquiv h hε θ) (shiftedAreaCellConfig_conductance h hε θ m) a

end MatedCRT
end
