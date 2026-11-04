import MatedCRT.Proofs.MatingOfTrees.CellContacts
import MatedCRT.Proofs.MatingOfTrees.BrownianLocalMin

/-!
# Adjacent mated-CRT cells meet

The boundary-length coordinates have distinct local-minimum values on one almost-sure
event, and the mating-of-trees merge rule then applies to all positive mesh sizes.
-/

namespace MatedCRT

open MeasureTheory Set

/-- Adjacent vertices of the boundary-length map have intersecting SLE cells, simultaneously
for all positive mesh sizes. -/
theorem adjacentCellsMeetAeStep (𝒮 : SpaceFillingSLEModel) : AdjacentCellsMeetAeStep 𝒮 := by
  intro γ _ _ Ω _ S hS
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have hdist := ae_of_ae_map hC.measurable_curves.2.2.2.aemeasurable
    (MatedCRTHarmonic.MatedCRT.ae_locMinDistinct hC.boundaryLawBM)
  filter_upwards [hdist, hC.merge, htie] with ω hdist hmerge htie
  intro ε hε j k hedge
  have hLd : ∀ x y, x ≠ y → IsLocalMin (fun t => (S.bm ω t).1) x →
      IsLocalMin (fun t => (S.bm ω t).1) y → (S.bm ω x).1 ≠ (S.bm ω y).1 := by
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hdist 0
  have hRd : ∀ x y, x ≠ y → IsLocalMin (fun t => (S.bm ω t).2) x →
      IsLocalMin (fun t => (S.bm ω t).2) y → (S.bm ω x).2 ≠ (S.bm ω y).2 := by
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hdist 1
  have hLm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => (S.bm ω u).1) s t →
      S.η ω s = S.η ω t := by
    intro s t h
    rw [← htie.1]
    exact hmerge s t (Or.inl h)
  have hRm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => (S.bm ω u).2) s t →
      S.η ω s = S.η ω t := by
    intro s t h
    rw [← htie.1]
    exact hmerge s t (Or.inr h)
  exact cells_meet_of_bmEdgeCount hε.le (S.bm ω).continuous.fst (S.bm ω).continuous.snd
    hLd hRd hLm hRm hedge

end MatedCRT
