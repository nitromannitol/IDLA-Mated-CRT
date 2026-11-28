import MatedCRT.FirstPass.Derived.ZeroConePolygonalDataCfg
import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepair
import MatedCRT.FirstPass.Derived.ZeroConeConnectedAlongLines
import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig

/-!
# The shifted zero-cone data are valid unit-mesh data almost surely

For the mating-of-trees coupling `D`, `γ ∈ (0, 2)` and a measurable version `G` of the
boundary-length pair of the zero-cone curve (`IsZeroConeBoundaryPair`), almost surely under
`P ⊗ Unif[0, 1]` the unit-mesh datum `phaseShiftedData η₀ G 1 p` (the curve `t ↦ η₀(t + θ)` and
the contour edge counts of `t ↦ G(t + θ)`) is `UnitMeshValid`.

* `ae_unitMeshValid_phaseShifted`: the statement. The cells `η₀([j - 1 + θ, j + θ])` with the
  contour edges of `G` form almost surely a line-connected cell configuration
  (`exists_zeroCone_clocked_shiftedCellCode_lineConnected`, Lattice-Probability
  `exists_coupled_clocked_cellularEmbedding`); the transported pair of that construction is a.s.
  equal to the given `G` (as in `ae_mem_regularData_phaseShifted`), and
  `UnitMeshValid.of_cellConfig` reads the point connectivity of the labels off connectedness
  along lines.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open MatedCRT MatedCRT.GMS310Transfer MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
  MatedCRTHarmonic.GMS4b

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The shifted zero-cone data are valid unit-mesh data almost surely.** -/
theorem ae_unitMeshValid_phaseShifted
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {G : Ω → Path2} (hG : IsZeroConeBoundaryPair D hγ G) :
    ∀ᵐ p ∂P.prod zeroConePhase, UnitMeshValid (phaseShiftedData η₀ G 1 p) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hf := MatedCRTHarmonic.GMSCase.aemeasurable_coneField D hγ
  have hQ : zeroConePhase ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hphase : ∀ᵐ θ ∂zeroConePhase, θ ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  obtain ⟨G₂, -, hclock, H, hH, -⟩ :=
    exists_zeroCone_clocked_shiftedCellCode_lineConnected D hγ hf one_pos zeroConePhase hQ hphase
  have hGG : ∀ᵐ ω ∂P, G₂ ω = G ω := by
    filter_upwards [hclock, hG.2] with ω hω hGω
    obtain ⟨ψ, -, -, hGψ, hψ, -⟩ := hω
    ext1 t
    rw [hGψ t, hGω t, hψ t]
  filter_upwards [hH, Measure.quasiMeasurePreserving_fst.ae hGG] with p hp hGp
  obtain ⟨h, hEq, hcfg, hL⟩ := hp
  rw [hEq, hGp] at hcfg hL
  refine UnitMeshValid.of_cellConfig _ hcfg hL (shiftedEuclideanCellEquiv h one_pos p.2) ?_ ?_
  · intro a
    rfl
  · intro a b
    exact shiftedAreaCellConfig_conductance h one_pos p.2 _ a b

end MatedCRT.ZeroConePolygonal
