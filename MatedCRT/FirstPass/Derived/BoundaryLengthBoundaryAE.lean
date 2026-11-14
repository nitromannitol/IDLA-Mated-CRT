import MatedCRT.FirstPass.Derived.BoundaryLengthBoundaryCriterion
import MatedCRT.FirstPass.Derived.ValidPeanosphere
import MatedCRT.FirstPass.Derived.BlockRunningMinTail

/-!
# Almost sure boundary criterion for Brownian coordinates

The past-edge criterion holds on a single probability-one event for all
positive meshes, interval endpoints and admissible cutoff indices.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- A correlated Brownian boundary pair satisfies the outside-edge criterion
simultaneously for all positive meshes and all admissible interval endpoints. -/
theorem ae_outside_bmEdge_iff_past_or_protected {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Ω → C(ℝ, ℝ × ℝ)} {γ : ℝ}
    (hB : AEMeasurable B P)
    (hBM : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ (P.map B)) :
    ∀ᵐ ω ∂P, ∀ (ε α β : ℝ) (j N : ℤ), 0 < ε → j ≤ N →
      β < ε * ((N : ℝ) + 1) →
      ((∃ k : ℤ, ¬ (α ≤ ε * k ∧ ε * k ≤ β) ∧
        bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0) ↔
      (∃ k : ℤ, k ≤ N ∧ ¬ (α ≤ ε * k ∧ ε * k ≤ β) ∧
        bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0) ∨
      (∀ u ∈ Icc (ε * j) (ε * N),
        sInf ((fun t => (B ω t).1) '' Icc (ε * j - ε) (ε * j)) ≤ (B ω u).1) ∨
      (∀ u ∈ Icc (ε * j) (ε * N),
        sInf ((fun t => (B ω t).2) '' Icc (ε * j - ε) (ε * j)) ≤ (B ω u).2)) := by
  have hL := ae_of_ae_map hB (ae_exists_lrCoord_lt_of_isCorrelatedBM2 hBM 0)
  have hR := ae_of_ae_map hB (ae_exists_lrCoord_lt_of_isCorrelatedBM2 hBM 1)
  filter_upwards [hL, hR] with ω hL hR
  intro ε α β j N hε hjN hβ
  apply exists_outside_bmEdge_iff_past_or_protected (L := fun t => (B ω t).1)
    (R := fun t => (B ω t).2) hε
    (continuous_fst.comp (B ω).continuous) (continuous_snd.comp (B ω).continuous) hjN hβ
  · simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using
      (hL (sInf ((fun t => (B ω t).1) '' Icc (ε * j - ε) (ε * j))) (ε * j)).1
  · simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using
      (hR (sInf ((fun t => (B ω t).2) '' Icc (ε * j - ε) (ε * j))) (ε * j)).1

/-- The simultaneous outside-edge criterion applies to every valid environment. -/
theorem MatedCRTEnv.IsValid.ae_outside_bmEdge_iff_past_or_protected
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε α β : ℝ) (j N : ℤ), 0 < ε → j ≤ N →
      β < ε * ((N : ℝ) + 1) →
      ((∃ k : ℤ, ¬ (α ≤ ε * k ∧ ε * k ≤ β) ∧
        bmEdgeCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2) j k ≠ 0) ↔
      (∃ k : ℤ, k ≤ N ∧ ¬ (α ≤ ε * k ∧ ε * k ≤ β) ∧
        bmEdgeCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2) j k ≠ 0) ∨
      (∀ u ∈ Icc (ε * j) (ε * N),
        sInf ((fun t => (S.bm ω t).1) '' Icc (ε * j - ε) (ε * j)) ≤ (S.bm ω u).1) ∨
      (∀ u ∈ Icc (ε * j) (ε * N),
        sInf ((fun t => (S.bm ω t).2) '' Icc (ε * j - ε) (ε * j)) ≤ (S.bm ω u).2)) :=
  MatedCRT.ae_outside_bmEdge_iff_past_or_protected hS.isCorrelatedBM2_map_bm.2.aemeasurable
    hS.isCorrelatedBM2_map_bm.1

end MatedCRT
