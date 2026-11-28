import MatedCRT.FirstPass.Derived.ZeroConePolygonalData

/-!
# The polygonal configuration of a unit-mesh datum

The polygonal cells `C_j` of a valid unit-mesh datum `w = (η, m)` form a cell configuration of
Gwynne–Miller–Sheffield (arXiv:1807.07515, Definition 1.15) carrying the walk of `w` (the construction of the
polygonal configuration in the proof of Lemma 3.5 of Gwynne–Miller–Sheffield, arXiv:1705.11161). This file
packages it as a map from data to the GMS space, with a default point `H₀` off the valid data.

* `polygonalConfig H₀ w`: the GMS configuration of the polygonal cells of `w` if `UnitMeshValid w`, and `H₀`
  otherwise.
* `polygonalConfig_of_valid`, `polygonalConfig_of_not_valid`: the two branches.
* `lineConnected_polygonalConfig`: for valid data the configuration is connected along lines.
* `carriesUnitMeshWalk_body_polygonalConfig`: for valid data the cells carry the walk of `w` (the body of
  `CarriesUnitMeshWalk w (polygonalConfig H₀ w)`).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

open Classical in
/-- **The polygonal configuration of a unit-mesh datum**: the GMS configuration of the polygonal cells of `w`
when `w` is a valid datum, and the default point `H₀` otherwise. -/
def polygonalConfig (H₀ : GMSSpace) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : GMSSpace :=
  if h : UnitMeshValid w then (polygonalInputOf w).toGMS (isValid_polygonalInputOf h) else H₀

variable {H₀ : GMSSpace} {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}

theorem polygonalConfig_of_valid (h : UnitMeshValid w) :
    polygonalConfig H₀ w = (polygonalInputOf w).toGMS (isValid_polygonalInputOf h) := by
  rw [polygonalConfig, dite_eq_left h]

theorem polygonalConfig_of_not_valid (h : ¬ UnitMeshValid w) : polygonalConfig H₀ w = H₀ := by
  rw [polygonalConfig, dite_eq_right h]

/-- **The polygonal configuration of a valid datum is connected along lines.** -/
theorem lineConnected_polygonalConfig (h : UnitMeshValid w) : (polygonalConfig H₀ w).1.LineConnected := by
  rw [polygonalConfig_of_valid h]
  exact (polygonalInputOf w).lineConnected (isValid_polygonalInputOf h)

/-- **The polygonal configuration of a valid datum carries its walk**: the body of
`CarriesUnitMeshWalk w (polygonalConfig H₀ w)`. The labels `ℤ` are in bijection with the cells, the
conductance between the cells of `a` and `b` is the edge count `m a b`, the vertex `η(j)` lies in the `j`-th
cell, and every point `z` of `η([j - 1, j])` lies in a cell within its diameter of a point of the `j`-th cell. -/
theorem carriesUnitMeshWalk_body_polygonalConfig (h : UnitMeshValid w) :
    ∃ e : ℤ ≃ (polygonalConfig H₀ w).1.cells,
      (∀ a b : ℤ, (polygonalConfig H₀ w).1.c (e a) (e b) = (w.2 a b : ℝ)) ∧
      (∀ j : ℤ, Complex.orthonormalBasisOneI.repr (MatedCRT.vertexPoint 1 w.1 j) ∈
        ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) ∧
      ∀ j : ℤ, ∀ z ∈ MatedCRT.cell 1 w.1 j,
        ∃ K : (polygonalConfig H₀ w).1.cells,
          Complex.orthonormalBasisOneI.repr z ∈
            ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ∧
          ∃ y ∈ ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane),
            dist (Complex.orthonormalBasisOneI.repr z) y ≤
              Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
  rw [polygonalConfig_of_valid h]
  exact carriesUnitMeshWalk_polygonalInputOf h

end MatedCRT.ZeroConePolygonal
