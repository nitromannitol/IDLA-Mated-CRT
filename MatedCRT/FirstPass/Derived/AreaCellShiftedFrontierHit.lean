import MatedCRT.FirstPass.Derived.IntegerWalkShiftedFrontierHit
import MatedCRT.FirstPass.Derived.AreaCellHitTime

/-! # Shifted frontier hitting for area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- On one full-measure event, every shifted area-cell walk starting in a cell
meeting a bounded open set hits a cell meeting its frontier. -/
theorem ae_hitTime_frontier_ne_top_all_bounded_open_all_shifts_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ V : Set ReflectedGMS.Plane, Bornology.IsBounded V → IsOpen V → ∀ K : ℕ,
        (((ξ K).1 : Set ReflectedGMS.Plane) ∩ V).Nonempty →
        hitTime {C : (areaCellConfig h hε m).cells | ((C.1 : Set ReflectedGMS.Plane) ∩ frontier V).Nonempty}
          (fun n => ξ (K + n)) ≠ ⊤ := by
  let : Countable (areaCellConfig h hε m).cells :=
    Countable.of_equiv ℤ (euclideanCellEquiv h hε)
  let e : ℤ ≃ᵐ (areaCellConfig h hε m).cells :=
    { toEquiv := euclideanCellEquiv h hε
      measurable_toFun := measurable_of_countable _
      measurable_invFun := measurable_of_countable _ }
  let E : (ℕ → ℤ) ≃ᵐ (ℕ → (areaCellConfig h hε m).cells) :=
    MeasurableEquiv.piCongrRight (fun _ => e)
  change ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map E, _
  apply E.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [ae_hitTime_frontier_ne_top_all_bounded_open_all_shifts
    h hε m hlf H hH hconn x] with ξ hξ
  intro V hVb hVo K hstart
  let f := Complex.orthonormalBasisOneI.repr.toHomeomorph
  let D : Set ℂ := f ⁻¹' V
  have hDb : Bornology.IsBounded D :=
    Complex.orthonormalBasisOneI.repr.isometry.antilipschitzWith.isBounded_preimage hVb
  have hDo : IsOpen D := hVo.preimage f.continuous
  have hVD : f '' D = V := Set.image_preimage_eq V f.surjective
  have hstart' : (H.cell (ξ K) ∩ D).Nonempty := by
    have ht : ξ K ∈ cellVertices ε η D := by
      change ξ K ∈ cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' V)
      rw [← euclideanCellEquiv_preimage_meeting h hε m V]
      exact hstart
    simpa only [cellVertices, verticesMeeting, mem_ofPred_eq, hH] using ht
  have hh := hξ D hDb hDo K hstart'
  have heq := areaCell_hitTime_frontier_eq h hε m D (fun n => ξ (K + n))
  rw [show Complex.orthonormalBasisOneI.repr '' D = V from hVD] at heq
  change hitTime {C : (areaCellConfig h hε m).cells |
    ((C.1 : Set ReflectedGMS.Plane) ∩ frontier V).Nonempty}
    (fun n => euclideanCellEquiv h hε (ξ (K + n))) ≠ ⊤
  rw [heq, ← hitTime_eq_vHitTime]
  simpa only [cellVertices, verticesMeeting, hH] using hh

end MatedCRT
end
