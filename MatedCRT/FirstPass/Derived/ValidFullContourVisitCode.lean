import MatedCRT.FirstPass.Derived.ValidCurveContourJointLaw
import LatticeProb.Topology.CurveComponentVisitCodeHomeomorph
import LatticeProb.Topology.ProperFiberComponentTransfer
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent

/-! # Component visit codes from the full contour -/

set_option autoImplicit false

open MeasureTheory Set
open LatticeProb MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- The rational component visit code of a valid curve has a measurable version
as a function of its entire boundary-length path. -/
theorem MatedCRTEnv.IsValid.exists_full_contour_component_visit_code
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (a u b : ℝ) :
    ∃ η : Ω → C(ℝ, ℂ), Measurable η ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω) ∧
      ∃ d : Path2 → ℚ → Bool, Measurable d ∧ ∀ᵐ ω ∂S.P,
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) = d (S.bm ω) := by
  classical
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨η, hη, hgood⟩ := FirstPass.Derived.MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  have hbm := hS.isCorrelatedBM2_map_bm
  let V : Ω → C(ℝ, ℂ) × Path2 := fun ω => (η ω, S.bm ω)
  have hV : Measurable V := hη.prodMk hbm.2
  let ν := S.P.map V
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 inferInstance
  let A : Set (C(ℝ, ℂ) × Path2) := {p |
    IsProperMap p.1 ∧ Function.Surjective p.1 ∧
      matingRel p.2 = fun s t => p.1 s = p.1 t}
  have hA : NullMeasurableSet A ν := by
    convert (ContinuousMap.measurableSet_isProperMap_and_surjective_curve.preimage
      measurable_fst).nullMeasurableSet.inter
      (FirstPass.Derived.nullMeasurableSet_matingRel_eq_fibre ν) using 1
    ext p
    simp only [A, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    tauto
  have hAV : ∀ᵐ ω ∂S.P, V ω ∈ A := by
    filter_upwards [hgood, hS.ae_matingRel_eq_fibre] with ω hv hf
    exact ⟨hv.2.1, hv.2.2.1, by simpa only [V, hv.1] using hf⟩
  obtain ⟨G, hGA, hG, hGeq⟩ := hA.exists_measurable_subset_ae_eq
  have hGV : ∀ᵐ ω ∂S.P, V ω ∈ G := by
    have hνA : ∀ᵐ p ∂ν, p ∈ A := by
      rw [ae_iff]
      change (S.P.map V) Aᶜ = 0
      rw [Measure.map_apply₀ hV.aemeasurable hA.compl]
      exact ae_iff.mp hAV
    have hνG : ∀ᵐ p ∂ν, p ∈ G := by
      filter_upwards [hGeq, hνA] with p hp ha
      exact hp.mpr ha
    exact ae_of_ae_map hV.aemeasurable hνG
  let Y : C(ℝ, ℂ) × Path2 → ℚ → Bool := fun p =>
    curveComponentVisitCode (Icc a b) p.1 (p.1 u)
  have hY : Measurable Y := by
    obtain ⟨B, hBsub, hBcount, hBbasis⟩ :=
      (TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected (α := ℂ)).exists_countable
    have : Countable B := hBcount.to_subtype
    exact measurable_curveComponentVisitCode (fun i : B => i.val) Prod.fst
      (fun p => p.1 u) isCompact_Icc measurable_fst
      ((ContinuousMap.measurable_eval u).comp measurable_fst)
      (fun i => (hBsub i.property).1) (fun i => (hBsub i.property).2)
      (fun U hU z hz => by
        obtain ⟨T, hT, hzT, hTU⟩ := hBbasis.isOpen_iff.mp hU z hz
        exact ⟨⟨T, hT⟩, hzT, hTU⟩)
  have hconst : ∀ p ∈ G, ∀ q ∈ G, p.2 = q.2 → Y p = Y q := by
    intro p hp q hq heq
    have hp' := hGA hp
    have hq' := hGA hq
    have hfib : ∀ s t, p.1 s = p.1 t ↔ q.1 s = q.1 t := by
      intro s t
      rw [← congrFun (congrFun hp'.2.2 s) t,
        ← congrFun (congrFun hq'.2.2 s) t, heq]
    obtain ⟨e, he, _⟩ := exists_homeomorph_of_proper_maps_same_fibers_components
      p.1 q.1 hp'.1 hq'.1 hp'.2.1 hq'.2.1 hfib
    have hefun : (⟨e, e.continuous⟩ : C(ℂ, ℂ)).comp p.1 = q.1 := by
      ext t
      exact he t
    have hc := curveComponentVisitCode_comp_homeomorph e p.1 (p.1 u) (Icc a b)
    rw [hefun, he u] at hc
    exact hc.symm
  have hsep (i : ℚ) : ∃ T : Set Path2, MeasurableSet T ∧
      ∀ᵐ ω ∂S.P, (Y (V ω) i = true ↔ S.bm ω ∈ T) := by
    let B : Set (C(ℝ, ℂ) × Path2) := {p | Y p i = true}
    have hB : MeasurableSet B :=
      measurableSet_eq_fun ((measurable_pi_apply i).comp hY) measurable_const
    obtain ⟨T, hT, hEq⟩ := LQGMetric.LocalEvent.ae_preimage_eq_of_saturated
      (P := S.P) (Y := V) (R := Prod.snd) measurable_snd hG (hG.inter hB) hGV (by
        intro p hp q hq he hpB
        change Y q i = true
        rw [← hconst p hp q hq he]
        exact hpB)
    refine ⟨T, hT, ?_⟩
    filter_upwards [hEq] with ω hω
    exact iff_of_eq hω
  choose T hT hEq using hsep
  let d : Path2 → ℚ → Bool := fun p i => if p ∈ T i then true else false
  refine ⟨η, hη, ?_, d, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    exact hω.1
  · apply measurable_pi_iff.mpr
    intro i
    exact Measurable.ite (hT i) measurable_const measurable_const
  · filter_upwards [ae_all_iff.2 hEq] with ω hω
    funext i
    have hi := hω i
    cases h : Y (V ω) i <;> simp [d, Y, V, h] at hi ⊢
    · exact hi
    · exact hi

end MatedCRT
