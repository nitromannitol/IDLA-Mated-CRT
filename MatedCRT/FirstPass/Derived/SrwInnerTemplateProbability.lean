import MatedCRT.FirstPass.Derived.InnerTemplateDisconnectionProbability
import MatedCRT.FirstPass.Derived.SrwStrictAdjacency

/-! # Simple random walk and inner-frontier disconnection -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set
open MatedCRT.TemplateDisconnectionWalk

/-- A template event bounds the probability that simple random walk disconnects
inner cells from the frontier before hitting the frontier. -/
theorem MatedCRTEnv.IsValid.ae_srw_templateProbability_le_innerDisconnection
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf)
        (0 : ℤ)), H.cell = cell ε (S.η ω) → ∀ (δ : ℝ), 0 < δ →
      (∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
        diam (cell ε (S.η ω) k) ≤ (templateRadius (templateScaleCount δ) : ℝ) / 2000) →
      ∀ (R : ℝ), R ≤ 1 →
        1 / 2 + 3 * ((templateRadius (templateScaleCount δ) : ℝ) / 2000) < R →
      ∀ (m : ℝ) (hm : 0 < m) (a : ℤ),
        srwLaw (S.mult ε ω) a
          {ξ | interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ ∈ templateDisconnectionEvent δ} ≤
        srwLaw (S.mult ε ω) a
          {ξ | walkSetDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (closedBall 0 δ))
            (cellVertices ε (S.η ω) (frontier (ball 0 R))) ξ} := by
  filter_upwards [hS.ae_templateProbability_le_innerDisconnection S hε] with ω hω
  intro hlf H hH δ hδ hdiam R hR hgap m hm a
  exact hω hlf H hH δ hδ hdiam R hR hgap m hm _
    (S.srwLaw_ae_graph_adj hε.le ω hlf a)

end MatedCRT
