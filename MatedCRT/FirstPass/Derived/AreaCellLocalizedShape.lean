import MatedCRT.FirstPass.Derived.AreaCellValidFiniteExpectation
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.CurveSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Localized segment bounds for rooted area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open MatedCRTHarmonic.GMS4b
open scoped ENNReal

/-- The rooted area ratio is bounded by the extended nonnegative ratio of the
corresponding path segment. This includes cells of zero Euclidean area. -/
theorem originAreaRatio_euclideanCell_le_segRatio
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    originAreaRatio (euclideanCell ε η h.1 hε k) ≤
      segRatio η (ε * (k - 1)) (ε * k) := by
  let K := euclideanCell ε η h.1 hε k
  have hd : Metric.diam (K : Set ReflectedGMS.Plane) = Metric.diam (cell ε η k) := by
    change Metric.diam (Complex.orthonormalBasisOneI.repr '' cell ε η k) = _
    exact Complex.orthonormalBasisOneI.repr.isometry.diam_image _
  have hv : volume (K : Set ReflectedGMS.Plane) = volume (cell ε η k) := by
    change volume (Complex.orthonormalBasisOneI.repr.toLinearEquiv.toEquiv '' cell ε η k) = _
    rw [Equiv.image_eq_preimage_symm]
    change volume (Complex.orthonormalBasisOneI.repr.symm ⁻¹' cell ε η k) = _
    exact Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
      ((isCompact_Icc.image h.1).isClosed.measurableSet.nullMeasurableSet)
  have hfin : volume (cell ε η k) ≠ ∞ :=
    (isCompact_Icc.image h.1).measure_ne_top
  have hquot : ENNReal.ofReal (Metric.diam (cell ε η k) ^ 2 /
      (volume (cell ε η k)).toReal) ≤
      ENNReal.ofReal (Metric.diam (cell ε η k) ^ 2) / volume (cell ε η k) := by
    by_cases hz : volume (cell ε η k) = 0
    · simp [hz]
    · rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hz hfin), ENNReal.ofReal_toReal hfin]
  unfold originAreaRatio
  by_cases hz : (0 : ReflectedGMS.Plane) ∈ (K : Set ReflectedGMS.Plane)
  · rw [Set.indicator_of_mem (show K ∈ {K : Cell | (0 : ReflectedGMS.Plane) ∈
        (K : Set ReflectedGMS.Plane)} from hz)]
    change ENNReal.ofReal (Metric.diam (K : Set ReflectedGMS.Plane) ^ 2 /
      (volume (K : Set ReflectedGMS.Plane)).toReal) ≤ _
    rw [hd, hv]
    exact hquot
  · rw [Set.indicator_of_notMem (show K ∉ {K : Cell | (0 : ReflectedGMS.Plane) ∈
        (K : Set ReflectedGMS.Plane)} from hz)]
    exact bot_le

/-- The two cells adjacent to time zero are bounded by the localized
segment-ratio supremum. -/
theorem originAreaRatio_two_cells_le_locDA
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) :
    originAreaRatio (euclideanCell ε η h.1 hε 0) ≤ locDA ε η 0 ∧
    originAreaRatio (euclideanCell ε η h.1 hε 1) ≤ locDA ε η 0 := by
  constructor
  · apply (originAreaRatio_euclideanCell_le_segRatio h hε 0).trans
    simpa using (segRatio_le_locDA (ε := ε) (c := η) (t₀ := 0) (s := 0)
      (by linarith) (by rfl))
  · apply (originAreaRatio_euclideanCell_le_segRatio h hε 1).trans
    simpa using (segRatio_le_locDA (ε := ε) (c := η) (t₀ := 0) (s := ε)
      (by linarith) (by linarith))

/-- A localized segment-ratio second moment supplies the root-shape bound
for the finite expectation of a valid area-cell configuration. -/
theorem MatedCRTEnv.IsValid.areaCellConfig_finiteExpectation_map_of_locDA
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε)
    (F : Ω → GMSSpace) (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω))
    (ηc : Ω → C(ℝ, ℂ)) (hηc : AEMeasurable ηc S.P)
    (hηc_eq : ∀ᵐ ω ∂S.P, (ηc ω : ℝ → ℂ) = S.η ω)
    (hmom : ∫⁻ ω, locDA ε (ηc ω) 0 ^ (2 : ℝ) ∂S.P < ∞) :
    FiniteExpectation (S.P.map F) := by
  apply hS.areaCellConfig_finiteExpectation_map_of_root_shape hε F hF hF_eq
    (fun ω => locDA ε (ηc ω) 0) ((measurable_locDA ε 0).comp_aemeasurable hηc) hmom
  filter_upwards [hF_eq, hηc_eq] with ω ⟨h, hFω⟩ heq
  refine ⟨h, ?_, ?_⟩
  · rw [heq]
    exact (originAreaRatio_two_cells_le_locDA h hε).1
  · rw [heq]
    exact (originAreaRatio_two_cells_le_locDA h hε).2

end MatedCRT
