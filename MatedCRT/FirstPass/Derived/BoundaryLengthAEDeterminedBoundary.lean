import MatedCRT.FirstPass.Derived.BoundaryLengthRecenteredBoundary
import LatticeProb.Prob.AEDetermined

/-!
# Boundary from almost surely determined endpoints

A past-measurable version of the inner boundary exists when the pair of
interval endpoints is almost surely determined by the past.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- Localized endpoint pairs yield a past-measurable version of the inner boundary. -/
theorem exists_increment_measurable_innerBoundary_of_ae_determined_endpoints
    {Ω : Type} [MeasurableSpace Ω] (mPast : MeasurableSpace Ω)
    {P : Measure Ω} {B : Ω → C(ℝ, ℝ × ℝ)} {γ : ℝ}
    (hB : AEMeasurable B P)
    (hBM : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ (P.map B))
    (s ε : ℝ) (hε : 0 < ε) (N : ℤ) (hN : ε * N ≤ s)
    (hPast : ∀ t ≤ s, @Measurable Ω (ℝ × ℝ) mPast _ (fun ω => B ω t - B ω s))
    (α β : Ω → ℝ)
    (hEndpoints : LatticeProb.AEDeterminedSigma
      (MeasurableSpace.comap (fun ω => (α ω, β ω)) inferInstance) mPast P)
    (hβN : ∀ᵐ ω ∂P, β ω < ε * ((N : ℝ) + 1)) :
    ∃ S : Ω → Set ℤ, @Measurable Ω (Set ℤ) mPast _ S ∧
      ∀ᵐ ω ∂P, S ω = LatticeProb.Graph.innerBoundary
        (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2)))
        {j : ℤ | α ω ≤ ε * j ∧ ε * j ≤ β ω} := by
  obtain ⟨Y, hY, hEq⟩ :=
    LatticeProb.exists_ae_eq_measurable_of_aeDeterminedSigma hEndpoints
  let α' : Ω → ℝ := fun ω => (Y ω).1
  let β' : Ω → ℝ := fun ω => (Y ω).2
  have hα' : @Measurable Ω ℝ mPast _ α' := hY.fst
  have hβ' : @Measurable Ω ℝ mPast _ β' := hY.snd
  have hβN' : ∀ᵐ ω ∂P, β' ω < ε * ((N : ℝ) + 1) := by
    filter_upwards [hβN, hEq] with ω hbound heq
    have heq' : β ω = β' ω := congrArg Prod.snd heq
    rw [← heq']
    exact hbound
  obtain ⟨S, hS, hSEq⟩ := exists_increment_measurable_innerBoundary_set_version
    mPast hB hBM s ε hε N hN hPast α' β' hα' hβ' hβN'
  refine ⟨S, hS, ?_⟩
  filter_upwards [hSEq, hEq] with ω hSω heq
  have hαeq : α ω = α' ω := congrArg Prod.fst heq
  have hβeq : β ω = β' ω := congrArg Prod.snd heq
  simpa only [hαeq, hβeq] using hSω

end MatedCRT
