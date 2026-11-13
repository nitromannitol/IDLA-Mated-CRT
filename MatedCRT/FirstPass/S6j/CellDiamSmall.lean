import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd

/-!
# Small cells near the origin with probability tending to one

For a valid environment with `0 < γ < 2`, a radius `0 < R < 1` and a threshold `c > 0`, the probability that some
cell `H^ε_k = η([ε(k-1), εk])` meeting `B_R(0)` has diameter larger than `c` tends to `0` as `ε → 0+`. This is
the cell-size estimate (Lemma 2.8, BG20 Lemma 2.4): with polynomially high probability every cell meeting `B_R`
has diameter at most `ε^{2/(2+γ)² - ζ}`, which is below `c` for small `ε`.

This is the cell-size hypothesis of the deterministic transfer step in the proof of BG20 Lemma 6.9
(`MatedCRT.WalkDisplacementBlocks`), in the form `∃ ε₀, ∀ ε < ε₀, P[bad] ≤ θ`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT.CellDiamSmall

/-- **Large cells meeting `B_R(0)` are unlikely.** For every valid environment with `0 < γ < 2`, every radius
`0 < R < 1` and every `c > 0`, the probability that some cell meeting `B_R(0)` has diameter larger than `c` tends
to `0` as `ε → 0+`. -/
theorem tendsto_prob_not_cellDiam_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {R c : ℝ} (hR0 : 0 < R)
    (hR1 : R < 1) (hc : 0 < c) :
    Tendsto (fun ε : ℝ => S.P {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 R).Nonempty →
      diam (cell ε (S.η ω) k) ≤ c}ᶜ) (𝓝[>] 0) (𝓝 0) := by
  set a : ℝ := 2 / (2 + γ) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set ζ : ℝ := min (1 / 2) (a / 2) with hζ
  have hζ0 : 0 < ζ := lt_min (by norm_num) (by positivity)
  have hζ1 : ζ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have he : 0 < a - ζ := by
    have := min_le_right (1 / 2 : ℝ) (a / 2)
    linarith
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ :=
    FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮 γ hγ0 hγ2 ζ R hζ0 hζ1 hR0 hR1 Ω S hS
  have hpow : Tendsto (fun ε : ℝ => ε ^ (a - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (a - ζ) (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ (a - ζ) < c := hpow.eventually (gt_mem_nhds hc)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < r₀ := nhdsWithin_le_nhds (Iio_mem_nhds hr₀)
  have hupper : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.const_mul C
      rw [Real.zero_rpow hp.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hsmall, hpos, hlt] with ε hε hε0 hεr
  refine (measure_mono ?_).trans (hbound ε hε0 hεr)
  refine compl_subset_compl.mpr fun ω hω k hk => ?_
  exact (hω k hk).2.trans hε.le

/-- **Small cells near the origin, quantitative form.** For every valid environment with `0 < γ < 2`, every
radius `0 < R < 1`, every `c > 0` and every `θ > 0` there is `ε₀ > 0` such that for `ε ∈ (0, ε₀)`, with
probability at least `1 - θ`, every cell meeting `B_R(0)` has diameter at most `c`. -/
theorem exists_eps_prob_not_cellDiam_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {R c : ℝ} (hR0 : 0 < R)
    (hR1 : R < 1) (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 R).Nonempty →
        diam (cell ε (S.η ω) k) ≤ c}ᶜ ≤ ENNReal.ofReal θ := by
  have hev := (tendsto_prob_not_cellDiam_le hγ0 hγ2 S hS hR0 hR1 hc).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  exact ⟨ε₀, hε₀, fun ε hε hεε₀ => (hsub ⟨hε, hεε₀⟩).le⟩

end MatedCRT.CellDiamSmall
