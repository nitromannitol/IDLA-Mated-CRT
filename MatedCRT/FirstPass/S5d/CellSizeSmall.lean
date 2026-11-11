import MatedCRT.FirstPass.S5d.CoverEvent

/-!
# The cell-size event on `{t < T}`

Reuses `cellSizeEvent` (S5d/CoverEvent.lean:31) and the polynomial tail of `CellSizeEstimateStmt` (Lemma 2.8, Draft/Section2.lean:131),
as in the proof of `tendsToOneOn_cover_vertexThresholdSet` (S5d/CoverEvent.lean:78). The exponent is `ζ = 1/(2+γ)²`, so the upper
exponent of the size event `2/(2+γ)² - ζ` equals `ζ > 0`.

* `tendsto_cellSizeEvent_compl`: the size event fails with probability tending to zero.
* `tendsTo_small_cells_on_lt_clusterExitTime`: on `{t < T}` (`T = clusterExitTime`), with probability tending to one, every cell
  meeting `B⁻_{δ/2}(Λ_t)` has diameter `< δ/4` (the referee's "once the maximum cell diameter is less than δ/4", lines 153-175).

For `t < T` the set `Λ_t` lies in `B_ρ` (`subset_ball_of_lt_clusterExitTime_cover`, S5d/CoverEvent.lean:63), using the monotonicity of
`Λ` on `(0, ∞)`, which holds almost surely by the harmonic-ball property (`IsConeHarmonicBallFamily`, Defs/Setting.lean:266).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

/-- The upper exponent `2/(2+γ)² - 1/(2+γ)²` of the cell-size event tends to zero as `ε → 0⁺` (it is positive). -/
theorem tendsto_cellExponent_rpow {γ : ℝ} (hγ0 : 0 < γ) :
    Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have hb : 0 < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    rw [show (2 : ℝ) / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 by ring]
    positivity
  have hc : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)) (𝓝 0)
      (𝓝 ((0 : ℝ) ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2))) :=
    (Real.continuous_rpow_const hb.le).tendsto 0
  rw [Real.zero_rpow hb.ne'] at hc
  exact hc.mono_left nhdsWithin_le_nhds

/-- The cell-size event of Lemma 2.8 fails with probability tending to zero (polynomial tail of `CellSizeEstimateStmt`). -/
theorem tendsto_cellSizeEvent_compl {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (h28 : CellSizeEstimateStmt 𝒮) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    Tendsto (fun ε : ℝ => S.P (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
  have h2γ : (1 : ℝ) < (2 + γ) ^ 2 := by nlinarith
  have hζ0 : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    exact h2γ
  obtain ⟨p, hp, C, r₀, hr₀, hPoly⟩ := h28 γ hγ0 hγ2 (1 / (2 + γ) ^ 2) ρ hζ0 hζ1 hρ hρ1 Ω S hS
  have hPolyT : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => C * r ^ p) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ p)) :=
      (continuous_const.mul (Real.continuous_rpow_const hp.le)).tendsto 0
    rw [Real.zero_rpow hp.ne', mul_zero] at hc
    have hc' : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] 0) (𝓝 0) := hc.mono_left nhdsWithin_le_nhds
    have h := ENNReal.tendsto_ofReal hc'
    rwa [ENNReal.ofReal_zero] at h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < r₀ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr₀)] with ε h1 h2
    exact ⟨h1, h2⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hPolyT
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev] with ε hε
  exact hPoly ε hε.1 hε.2

/-- **Every cell meeting `B⁻_{δ/2}(Λ_t)` has diameter below `δ/4`, with probability tending to one on `{t < T}`**
(the hypothesis of the floor argument, referee lines 153-175). Uses the a.s. monotonicity of `Λ` (`IsConeHarmonicBallFamily`). -/
theorem tendsTo_small_cells_on_lt_clusterExitTime {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (h28 : CellSizeEstimateStmt 𝒮) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω | ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty → diam (cell ε (S.η ω) k) < δ / 4} := by
  have hsm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) < δ / 4 :=
    (tendsto_cellExponent_rpow hγ0).eventually (gt_mem_nhds (by positivity))
  have hN : S.P {ω | ¬ MonotoneOn (Λ ω) (Ioi 0)} = 0 :=
    ae_iff.1 (hΛ.mono fun ω h => h.2.1.monotoneOn)
  have hZ := tendsto_cellSizeEvent_compl hγ0 hγ2 hρ hρ1 h28 S hS
  have incl : ∀ ε : ℝ, ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) < δ / 4 →
      ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ∀ k : ℤ,
        (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty → diam (cell ε (S.η ω) k) < δ / 4}ᶜ) ⊆
      (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ ∪ {ω | ¬ MonotoneOn (Λ ω) (Ioi 0)} := by
    intro ε hεs ω hω
    obtain ⟨hF, hE⟩ := hω
    by_cases hC : ω ∈ cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε
    · by_cases hM : MonotoneOn (Λ ω) (Ioi 0)
      · exfalso
        have hE' : ¬ ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
            diam (cell ε (S.η ω) k) < δ / 4 := hE
        obtain ⟨k, hk⟩ := not_forall.1 hE'
        rw [not_imp] at hk
        obtain ⟨⟨y, hyc, hyI⟩, hkd⟩ := hk
        have hball : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime_cover hρ hM ht hF
        have hne : (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty := ⟨y, hyc, hball hyI.1⟩
        have hC' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
            ε ^ (2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) ≤ diam (cell ε (S.η ω) k) ∧
              diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) := hC
        exact hkd (lt_of_le_of_lt (hC' k hne).2 hεs)
      · exact Or.inr hM
    · exact Or.inl hC
  unfold TendsToOneOn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hZ
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hsm] with ε hε
  calc S.P _ ≤ S.P ((cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ ∪ {ω | ¬ MonotoneOn (Λ ω) (Ioi 0)}) :=
        measure_mono (incl ε hε)
    _ ≤ S.P (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ + S.P {ω | ¬ MonotoneOn (Λ ω) (Ioi 0)} :=
        measure_union_le _ _
    _ = S.P (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ := by rw [hN, add_zero]

end MatedCRT
