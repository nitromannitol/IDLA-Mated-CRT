import MatedCRT.Draft.Section2

/-!
# Large cells meeting a ball have vanishing probability

For a valid environment, the probability that some cell `H^ε_a` which meets `B_{5/8}` has diameter
at least `1/8` tends to `0` as `ε → 0+`. This is the cell-size input of the comparison of the
embedded walk with the walk on the interior vertex set in the upper bound on the median exit time
(eq:meps, line 731). It follows from the cell-size estimate of Lemma 2.8 (BG20 Lemma 2.4): with
polynomially high probability every such cell has diameter at most `ε^{2/(2+γ)² - ζ}`, which is
below `1/8` for small `ε` once `ζ < 2/(2+γ)²`.

## Main results

* `MatedCRT.cellDiam_bad_tendsto_zero_of_cellSizeEstimate`
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

/-- **Large cells meeting `B_{5/8}` are unlikely.** Given the cell-size estimate (Lemma 2.8), for every
valid environment with `0 < γ < 2` the probability that some cell meeting `B_{5/8}` has diameter at least
`1/8` tends to `0` as `ε → 0+`. -/
theorem cellDiam_bad_tendsto_zero_of_cellSizeEstimate {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    Tendsto (fun ε : ℝ => S.P {ω | ∃ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
      1 / 8 ≤ diam (cell ε (S.η ω) k)}) (𝓝[>] 0) (𝓝 0) := by
  set a : ℝ := 2 / (2 + γ) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set ζ : ℝ := min (1 / 2) (a / 2) with hζ
  have hζ0 : 0 < ζ := lt_min (by norm_num) (by positivity)
  have hζ1 : ζ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have he : 0 < a - ζ := by
    have := min_le_right (1 / 2 : ℝ) (a / 2)
    linarith
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ :=
    h28 γ hγ0 hγ2 ζ (5 / 8) hζ0 hζ1 (by norm_num) (by norm_num) Ω S hS
  have hpow : Tendsto (fun ε : ℝ => ε ^ (a - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (a - ζ) (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ (a - ζ) < 1 / 8 :=
    hpow.eventually (gt_mem_nhds (by norm_num))
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < r₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hr₀)
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
  intro ω hω hgood
  obtain ⟨k, hk, hd⟩ := hω
  exact absurd (hd.trans (hgood k hk).2) (not_le.2 hε)

end MatedCRT
