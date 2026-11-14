import MatedCRT.FirstPass.Derived.TemplateDisconnectionWalk
import MatedCRT.FirstPass.Derived.ValidTemplateSeparation
import MatedCRT.FirstPass.Derived.WalkSetDisconnectsBridge

/-!
# Disconnection by a walk whose interpolation follows a template, in a valid environment

For a valid environment `S` and a cell size `ε > 0`, almost surely the following holds simultaneously
for every proof of local finiteness of the mated-CRT map of `S.bm ω`, every cellular embedding `H` of
it whose cells are the cells `H^ε_{εx} = η([ε(x - 1), εx])` of Definition 1.2, every `δ > 0`, every
walk `ξ` along the edges of the map and every speed `m > 0`: if the cells meeting the open unit disc
have diameter at most `4^{-K(δ)} / 2000` and the linear interpolation of the embedded walk
`k ↦ η(ε ξ_k)` at speed `m` lies in the robust disconnection event `E_δ`
(`templateDisconnectionEvent δ`), then the walk disconnects the vertices whose cells meet
`closedBall 0 δ` from those whose cells meet the unit circle before hitting the latter
(`walkSetDisconnectsBeforeHit (S.mult ε ω)`). This is the discrete form of the Brownian
disconnection estimate used for [GMS21, Lemma 3.12] in the proof of the uniform-start invariance
principle.

The almost sure ingredient is the template separation property of the cells
(`MatedCRTEnv.IsValid.ae_templateSeparation`); the rest is deterministic
(`graphSeparates_traceBefore_of_mem_templateDisconnectionEvent`) together with the identification
of the separation by the trace with `walkSetDisconnectsBeforeHit`
(`MatedCRTEnv.walkSetDisconnectsBeforeHit_mult_iff`).
-/

namespace MatedCRT

open MeasureTheory Metric Set
open MatedCRT.TemplateDisconnectionWalk

/-- The scales `4^{-k}`, `1 ≤ k ≤ K`, are at most `1 / 4` and at least `4^{-K}`. -/
theorem templateRadius_le_quarter_and_ge {k K : ℕ} (hk : k ∈ Finset.Icc 1 K) :
    (templateRadius k : ℝ) ≤ 1 / 4 ∧ (templateRadius K : ℝ) ≤ templateRadius k := by
  obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.1 hk
  refine ⟨?_, ?_⟩
  · rw [coe_templateRadius]
    calc (1 / 4 : ℝ) ^ k ≤ (1 / 4) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk1
      _ = 1 / 4 := pow_one _
  · rw [coe_templateRadius, coe_templateRadius]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hkK

/-- **Discrete disconnection from the template event, almost surely.** For a valid environment and
`ε > 0`, almost surely: for every proof of local finiteness, every cellular embedding `H` of the
mated-CRT map with `H.cell = cell ε (S.η ω)`, every `δ > 0` such that the cells meeting the unit
disc have diameter at most `4^{-K(δ)} / 2000`, every walk `ξ` along the edges of the map and every
speed `m > 0` with `interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ ∈ templateDisconnectionEvent δ`, the
walk disconnects `cellVertices ε (S.η ω) (closedBall 0 δ)` from `cellVertices ε (S.η ω) (sphere 0 1)`
before hitting the latter. -/
theorem MatedCRTEnv.IsValid.ae_walkSetDisconnectsBeforeHit_of_mem_templateDisconnectionEvent
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : MatedCRTHarmonic.CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf)
        (0 : ℤ)), H.cell = cell ε (S.η ω) → ∀ (δ : ℝ), 0 < δ →
      (∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
        diam (cell ε (S.η ω) k) ≤ (templateRadius (templateScaleCount δ) : ℝ) / 2000) →
      ∀ (ξ : ℕ → ℤ),
        (∀ n, (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Adj (ξ n) (ξ (n + 1))) →
        ∀ (m : ℝ) (hm : 0 < m),
          interpPathCM (vertexPoint ε (S.η ω)) hm.le ξ ∈ templateDisconnectionEvent δ →
          walkSetDisconnectsBeforeHit (S.mult ε ω) (cellVertices ε (S.η ω) (closedBall 0 δ))
            (cellVertices ε (S.η ω) (sphere 0 1)) ξ := by
  filter_upwards [MatedCRTEnv.IsValid.ae_templateSeparation S hS hε] with ω hTS
  intro hlf H hHc δ hδ hdiam ξ hadj m hm hf
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
  have key := graphSeparates_traceBefore_of_mem_templateDisconnectionEvent hv hadj
    (fun n => H.inter_of_adj _ _ (hadj n)) hm hδ hd le_rfl hdiam' hTS' hf
  rw [hHc, verticesMeeting_cell_eq_cellVertices, setOf_exists_mem_cell_dist_le_eq_cellVertices] at key
  exact (MatedCRTEnv.walkSetDisconnectsBeforeHit_mult_iff S hε.le ω hlf _ _ ξ).2 key

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.templateRadius_le_quarter_and_ge
#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_walkSetDisconnectsBeforeHit_of_mem_templateDisconnectionEvent
