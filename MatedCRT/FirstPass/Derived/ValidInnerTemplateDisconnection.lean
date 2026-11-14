import MatedCRT.FirstPass.Derived.ValidTemplateDisconnection

/-! # Disconnection before an inner ball frontier -/

namespace MatedCRT

open MeasureTheory Metric Set
open MatedCRT.TemplateDisconnectionWalk

/-- In a valid environment, a template walk disconnects the inner cells before hitting the
frontier of any sufficiently large inner ball. The exceptional set is independent of the ball,
walk, and cellular embedding. -/
theorem MatedCRTEnv.IsValid.ae_walkSetDisconnectsBeforeHit_frontier_of_mem_templateDisconnectionEvent
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf)
        (0 : ℤ)), H.cell = cell ε (S.η ω) → ∀ (δ : ℝ), 0 < δ →
      (∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
        diam (cell ε (S.η ω) k) ≤ (templateRadius (templateScaleCount δ) : ℝ) / 2000) →
      ∀ (R : ℝ), R ≤ 1 →
        1 / 2 + 3 * ((templateRadius (templateScaleCount δ) : ℝ) / 2000) < R →
      ∀ (ξ : ℕ → ℤ),
        (∀ n, (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Adj (ξ n) (ξ (n + 1))) →
        ∀ (m : ℝ) (hm : 0 < m),
          interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ ∈ templateDisconnectionEvent δ →
          walkSetDisconnectsBeforeHit (S.mult ε ω) (cellVertices ε (S.η ω) (closedBall 0 δ))
            (cellVertices ε (S.η ω) (frontier (ball 0 R))) ξ := by
  filter_upwards [MatedCRTEnv.IsValid.ae_templateSeparation S hS hε] with ω hTS
  intro hlf H hHc δ hδ hdiam R hR1 hρ ξ hadj m hm hf
  set d : ℝ := (templateRadius (templateScaleCount δ) : ℝ) / 2000 with hd_def
  have hd : 0 ≤ d := by
    have := templateRadius_pos (templateScaleCount δ)
    positivity
  have hv : ∀ k, vertexPoint ε (S.η ω) k ∈ H.cell k := fun k => by
    rw [hHc]
    exact ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hdiam' : ∀ k, (H.cell k ∩ ball 0 1).Nonempty → diam (H.cell k) ≤ d := by
    rw [hHc]
    exact hdiam
  have hTS' : ∀ k ∈ Finset.Icc 1 (templateScaleCount δ),
      H.TemplateSeparation 0 (templateRadius k) := by
    intro k hk
    obtain ⟨hk4, hKk⟩ := templateRadius_le_quarter_and_ge hk
    have hr : (0 : ℝ) < templateRadius k := by exact_mod_cast templateRadius_pos k
    refine hTS hlf H hHc 0 (templateRadius k) hr fun x hx => ?_
    obtain ⟨q, hqc, hqb⟩ := hx
    have hq1 : q ∈ ball (0 : ℂ) 1 := by
      rw [mem_closedBall] at hqb
      rw [mem_ball]
      linarith
    calc diam (H.cell x) ≤ d := hdiam' x ⟨q, hqc, hq1⟩
      _ ≤ (templateRadius k : ℝ) / 1000 := by
        rw [hd_def]
        linarith
  have key := graphSeparates_traceBefore_sphere_of_mem_templateDisconnectionEvent hv hadj
    (fun n => H.inter_of_adj _ _ (hadj n)) hm hδ hd hR1 (by simpa [hd_def] using hρ)
    le_rfl hdiam' hTS' hf
  rw [hHc, verticesMeeting_cell_eq_cellVertices, setOf_exists_mem_cell_dist_le_eq_cellVertices] at key
  have hR : 0 < R := by linarith
  rw [frontier_ball (0 : ℂ) hR.ne']
  exact (MatedCRTEnv.walkSetDisconnectsBeforeHit_mult_iff S hε.le ω hlf _ _ ξ).2 key


end MatedCRT
