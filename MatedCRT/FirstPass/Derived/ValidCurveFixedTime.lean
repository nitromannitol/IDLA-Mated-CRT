import MatedCRT.FirstPass.Derived.MatingRelation
import MatedCRT.FirstPass.Derived.BlockRunningMinTail
import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Prob.CorrelatedBMContourFiber

/-! # Fixed-time fibres of a valid space-filling curve -/

open MeasureTheory Set

namespace MatedCRT

/-- At each fixed deterministic time, the curve of a valid environment has
almost surely a singleton fibre. -/
theorem MatedCRTEnv.IsValid.ae_fixedTime_singleton_fibre
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (a : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ t, S.η ω t = S.η ω a → t = a := by
  apply LatticeProb.CorrelatedBM.ae_singleton_fiber_of_contour_relation
    hS.isCorrelatedBM2_map_bm.2.aemeasurable hS.isCorrelatedBM2_map_bm.1 a
  filter_upwards [hS.ae_matingRel_eq_fibre] with ω hω t ht
  exact (congrFun (congrFun hω a) t).mpr ht.symm

/-- At each fixed deterministic time, the curve point lies almost surely in
the interior of every segment image whose time interval contains that time. -/
theorem MatedCRTEnv.IsValid.ae_fixedTime_mem_interior_image
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (a : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ l r, l < a → a < r → S.η ω a ∈ interior (S.η ω '' Icc l r) := by
  obtain ⟨η, _, hae⟩ := hS.exists_curveVersion
  filter_upwards [hS.ae_fixedTime_singleton_fibre a, hae,
    FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hae] with ω hf he hp
  intro l r hl hr
  have hf' : ∀ t, η ω t = η ω a → t = a := by
    intro t ht
    apply hf t
    simpa only [he] using ht
  have hi := LatticeProb.mem_interior_image_Icc_of_singleton_fiber (η ω) hp.1 hp.2.1 hl hr hf'
  simpa only [he] using hi

end MatedCRT
