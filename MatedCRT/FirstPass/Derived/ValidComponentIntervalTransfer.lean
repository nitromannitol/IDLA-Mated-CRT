import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import MatedCRT.FirstPass.Derived.BlockRunningMinTail
import MatedCRT.FirstPass.Derived.MatingRelation
import LatticeProb.Topology.ComponentIntervalMarginalTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique

/-! # Component intervals transferred to a valid environment -/

set_option autoImplicit false

open MeasureTheory Set
open LatticeProb MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- A source law with the same correlated Brownian contour and a full family
of component interval witnesses supplies such witnesses for a valid curve. -/
theorem MatedCRTEnv.IsValid.ae_component_interval_of_source
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (η : Ω → C(ℝ, ℂ)) (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω)
    (ν : Measure (Path2 × C(ℝ, ℂ))) [IsFiniteMeasure ν]
    (hlaw : IsCorrelatedBM2 γ (ν.map Prod.fst))
    {G : Set (Path2 × C(ℝ, ℂ))} (hG : NullMeasurableSet G ν)
    (hfull : ∀ᵐ p ∂ν, p ∈ G)
    (hsource : ∀ p ∈ G, IsProperMap p.2 ∧ Function.Surjective p.2 ∧
      (∀ v w, p.2 v = p.2 w ↔ matingRel p.1 v w) ∧
      p.2 u ∈ interior (p.2 '' Icc a b) ∧
      ∃ A B : ℝ, a ≤ A ∧ A ≤ B ∧ B ≤ b ∧
        p.2 '' Icc A B = closure (connectedComponentIn (interior (p.2 '' Icc a b)) (p.2 u))) :
    ∀ᵐ ω ∂S.P, ∃ A B : ℝ, a ≤ A ∧ A ≤ B ∧ B ≤ b ∧
      (η ω) '' Icc A B = closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u)) := by
  have hmarg : S.P.map S.bm = ν.map Prod.fst :=
    MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ _ _ hS.isCorrelatedBM2_map_bm.1 hlaw
  have htarget : ∀ᵐ ω ∂S.P, IsProperMap (η ω) ∧ Function.Surjective (η ω) ∧
      ∀ v w, η ω v = η ω w ↔ matingRel (S.bm ω) v w := by
    filter_upwards [FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hη,
      hS.ae_matingRel_eq_fibre, hη] with ω hp hf he
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro v w
    rw [hf, ← he]
  exact ae_exists_component_interval_of_marginal_fibers ν S.P S.bm η
    hS.isCorrelatedBM2_map_bm.2 hmarg matingRel a u b hG hfull hsource htarget

end MatedCRT
