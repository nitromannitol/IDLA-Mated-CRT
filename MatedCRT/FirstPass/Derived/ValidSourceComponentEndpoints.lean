import MatedCRT.FirstPass.Derived.ValidComponentIntervalTransfer
import MatedCRT.FirstPass.Derived.ValidExistentialComponentEndpoints
import LatticeProb.Topology.ComponentVisitCodeMarginalTransfer

/-! # Component endpoints from a source law -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LatticeProb LatticeProb.CorrelatedBM MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- A source law with observable visit codes and component intervals supplies
segment-observable component endpoints in a valid environment. -/
theorem MatedCRTEnv.IsValid.exists_segment_component_endpoints_of_source
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) (η : Ω → C(ℝ, ℂ))
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω)
    (ν : Measure (Path2 × C(ℝ, ℂ))) [IsFiniteMeasure ν]
    (hlaw : IsCorrelatedBM2 γ (ν.map Prod.fst))
    (dPast dFuture : Path2 → {q : ℚ // (q : ℝ) ∈ Icc a b} → Bool)
    (hdPast : Measurable[incrementSigma lrCoord (Iic b) b] dPast)
    (hdFuture : Measurable[incrementSigma lrCoord (Ici a) a] dFuture)
    {G : Set (Path2 × C(ℝ, ℂ))} (hG : NullMeasurableSet G ν)
    (hfull : ∀ᵐ p ∂ν, p ∈ G)
    (hsource : ∀ p ∈ G, IsProperMap p.2 ∧ Function.Surjective p.2 ∧
      (∀ v w, p.2 v = p.2 w ↔ matingRel p.1 v w) ∧
      p.2 u ∈ interior (p.2 '' Icc a b) ∧
      (∃ A B : ℝ, a ≤ A ∧ A ≤ B ∧ B ≤ b ∧
        p.2 '' Icc A B = closure (connectedComponentIn (interior (p.2 '' Icc a b)) (p.2 u))) ∧
      (∀ q, curveComponentVisitCode (Icc a b) p.2 (p.2 u) q.1 = dPast p.1 q) ∧
      (∀ q, curveComponentVisitCode (Icc a b) p.2 (p.2 u) q.1 = dFuture p.1 q)) :
    ∃ A B : Path2 → ℝ,
      Measurable[incrementSigma lrCoord (Icc a b) a] A ∧
      Measurable[incrementSigma lrCoord (Icc a b) a] B ∧
      ∀ᵐ ω ∂S.P, a ≤ A (S.bm ω) ∧ B (S.bm ω) ≤ b ∧
        (η ω) '' Icc (A (S.bm ω)) (B (S.bm ω)) =
          closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u)) := by
  have hmarg : S.P.map S.bm = ν.map Prod.fst :=
    MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ _ _ hS.isCorrelatedBM2_map_bm.1 hlaw
  have htarget : ∀ᵐ ω ∂S.P, IsProperMap (η ω) ∧ Function.Surjective (η ω) ∧
      ∀ v w, η ω v = η ω w ↔ matingRel (S.bm ω) v w := by
    filter_upwards [FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hη,
      hS.ae_matingRel_eq_fibre, hη] with ω hp hf he
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro v w
    rw [hf, ← he]
  have hdecode (d : Path2 → {q : ℚ // (q : ℝ) ∈ Icc a b} → Bool)
      (hd : ∀ p ∈ G, ∀ q,
        curveComponentVisitCode (Icc a b) p.2 (p.2 u) q.1 = d p.1 q) :
      ∀ᵐ ω ∂S.P, ∀ q,
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1 = d (S.bm ω) q := by
    have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
    filter_upwards [ae_exists_witness_of_marginal_law ν S.P S.bm
      hS.isCorrelatedBM2_map_bm.2 hmarg hG hfull, htarget] with ω hw ht
    obtain ⟨f, hf⟩ := hw
    have hs := hsource (S.bm ω, f) hf
    have hfib : ∀ v w, f v = f w ↔ (η ω) v = (η ω) w := by
      intro v w
      exact (hs.2.2.1 v w).trans (ht.2.2 v w).symm
    obtain ⟨e, he, _⟩ := exists_homeomorph_of_proper_maps_same_fibers_components
      f (η ω) hs.1 ht.1 hs.2.1 ht.2.1 hfib
    have hefun : (⟨e, e.continuous⟩ : C(ℂ, ℂ)).comp f = η ω := by
      ext v
      exact he v
    have hc := curveComponentVisitCode_comp_homeomorph e f (f u) (Icc a b)
    rw [hefun, he u] at hc
    intro q
    exact (congrFun hc q.1).trans (hd (S.bm ω, f) hf q)
  have hpast : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Iic b) b).comap S.bm) S.P := by
    apply AELeSigma.comap_of_ae_eq
      (hdPast.comp (measurable_iff_comap_le.mpr le_rfl))
    filter_upwards [hdecode dPast (fun p hp => (hsource p hp).2.2.2.2.2.1)] with ω hω
    funext q
    exact hω q
  have hfuture : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Ici a) a).comap S.bm) S.P := by
    apply AELeSigma.comap_of_ae_eq
      (hdFuture.comp (measurable_iff_comap_le.mpr le_rfl))
    filter_upwards [hdecode dFuture (fun p hp => (hsource p hp).2.2.2.2.2.2)] with ω hω
    funext q
    exact hω q
  apply hS.exists_segment_observable_component_interval hau hub η hη hpast hfuture
  filter_upwards [hS.ae_component_interval_of_source η hη ν hlaw hG hfull
    (fun p hp => ⟨(hsource p hp).1, (hsource p hp).2.1, (hsource p hp).2.2.1,
      (hsource p hp).2.2.2.1, (hsource p hp).2.2.2.2.1⟩)] with ω hω
  obtain ⟨A, B, ha, _, hb, hi⟩ := hω
  exact ⟨A, B, ha, hb, hi⟩

end MatedCRT
