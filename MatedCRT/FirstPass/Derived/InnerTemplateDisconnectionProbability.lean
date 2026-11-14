import MatedCRT.FirstPass.Derived.ValidInnerTemplateDisconnection

/-! # Probability of inner-frontier disconnection -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set
open MatedCRT.TemplateDisconnectionWalk

/-- A template event bounds the probability of disconnection before the inner frontier,
for any measure on walks that follow graph edges almost everywhere. -/
theorem MatedCRTEnv.IsValid.ae_templateProbability_le_innerDisconnection
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf)
        (0 : ℤ)), H.cell = cell ε (S.η ω) → ∀ (δ : ℝ), 0 < δ →
      (∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
        diam (cell ε (S.η ω) k) ≤ (templateRadius (templateScaleCount δ) : ℝ) / 2000) →
      ∀ (R : ℝ), R ≤ 1 →
        1 / 2 + 3 * ((templateRadius (templateScaleCount δ) : ℝ) / 2000) < R →
      ∀ (m : ℝ) (hm : 0 < m) (Q : Measure (ℕ → ℤ)),
        (∀ᵐ ξ ∂Q, ∀ n,
          (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Adj (ξ n) (ξ (n + 1))) →
        Q {ξ | interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ ∈ templateDisconnectionEvent δ} ≤
          Q {ξ | walkSetDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (closedBall 0 δ))
            (cellVertices ε (S.η ω) (frontier (ball 0 R))) ξ} := by
  filter_upwards [hS.ae_walkSetDisconnectsBeforeHit_frontier_of_mem_templateDisconnectionEvent S hε] with ω hω
  intro hlf H hH δ hδ hdiam R hR hgap m hm Q hQ
  apply measure_mono_ae
  filter_upwards [hQ] with ξ hξ hmem
  exact hω hlf H hH δ hδ hdiam R hR hgap ξ hξ m hm hmem

end MatedCRT
