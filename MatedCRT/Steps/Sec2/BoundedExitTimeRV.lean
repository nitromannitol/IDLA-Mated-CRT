import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Infra.LogKernel

/-!
# Lemma 2.17 from Lemma 2.7

Lemma 2.17 (lemma:bounded-exit-time, line 888) follows from the upper volume bound of Lemma 2.7 (lemma:volume-growth,
BG20 Lemma A.1) by the partition of the integral into dyadic annuli which the proof of Lemma 2.17 refers to (line 911,
"as in the proof of BG20 Lemma A.3"). Fix `β ∈ (0, (2-γ)²/2)` (here `β = (2-γ)²/4`) and `q = β/2`.
* Union bound over the dyadic scales `2δ 2^{-k}`: with polynomially high probability as `δ → 0`,
  `μ_h(B_{2δ 2^{-k}}(z)) ≤ (2δ 2^{-k})^β` for all `k` and all `z ∈ B_{1-2δ}` (`measure_compl_iInter_le`).
* On this event, `𝓜(B_δ(y)) ≤ (log (1/δ) + 1) (2δ)^β (1 - 2^{-β})⁻¹ ≤ δ^{β/2}` for `y ∈ B_ρ` and small `δ`
  (`largestExitTimeRV_ball_le_of_dyadic`, `exists_pos_log_rpow_le`): the second statement.
* On the same event, `sup_{D ⊆ B_ρ} 𝓜(D) ≤ 𝓜(B_ρ) < ∞` (`largestExitTimeRV_ball_zero_lt_top_of_dyadic`); its
  probability tends to `1` as `δ → 0`, which gives the first statement (instead of the Borel-Cantelli argument with
  BG20 Lemma A.3 of line 908).
The cited input is Lemma 2.7 (`VolumeGrowthStmt`) only; BG20 Lemma A.3 and BG20 (5.3) are not needed.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Lemma 2.17** from **Lemma 2.7** (`VolumeGrowthStmt`, BG20 Lemma A.1), with `q = (2-γ)²/8`. -/
theorem boundedExitTimeRV_of_steps (h27 : VolumeGrowthStmt) : BoundedExitTimeRVStmt := by
  intro γ hγ0 hγ2
  have hsq : 0 < (2 - γ) ^ 2 := pow_pos (by linarith) 2
  obtain ⟨β, hβ0, hβ1⟩ : ∃ β : ℝ, 0 < β ∧ β < (2 - γ) ^ 2 / 2 :=
    ⟨(2 - γ) ^ 2 / 4, by linarith, by linarith⟩
  refine ⟨β / 2, half_pos hβ0, fun ρ hρ0 hρ1 Ω _ P hC hcirc μ hcone => ?_⟩
  obtain ⟨p, hp, K, r₀, hr₀, hV⟩ :=
    h27 γ hγ0 hγ2 β ((2 + γ) ^ 2 / 2 + 1) hβ0 hβ1 (by linarith) Ω P hC hcirc μ hcone
  -- the dyadic volume bound at the top radius `2δ` on `B_{1-2δ}`
  have hdy : ∀ δ : ℝ, 0 < δ → 2 * δ < r₀ →
      P {ω | DyadicVolumeBound (μ ω) (1 - 2 * δ) (2 * δ) β}ᶜ ≤
        ENNReal.ofReal (max K 0 * (1 - (1 / 2) ^ p)⁻¹ * (2 * δ) ^ p) := by
    intro δ hδ hδr
    refine measure_compl_iInter_le hp hV (mul_pos two_pos hδ) hδr ?_
    intro ω hω z hz k
    rw [mem_iInter] at hω
    have hrad : 1 - 2 * δ ≤ 1 - 2 * δ * (1 / 2) ^ k := by
      have := mul_le_of_le_one_right (by linarith : (0 : ℝ) ≤ 2 * δ)
        (pow_le_one₀ (by norm_num) (by norm_num) : ((1 : ℝ) / 2) ^ k ≤ 1)
      linarith
    exact (hω k z (ball_subset_ball hrad hz)).2
  -- first statement: `sup_{D ⊆ B_ρ} 𝓜(D) < ∞` a.s.
  have hae : ∀ᵐ ω ∂P, (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ), largestExitTimeRV (μ ω) D) < ⊤ := by
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto (tendsto_ofReal_mul_rpow (max K 0 * (1 - (1 / 2) ^ p)⁻¹) 2 p hp) ?_)
      zero_le
    filter_upwards [Ioo_mem_nhdsGT (lt_min (half_pos hr₀) (by linarith : (0 : ℝ) < (1 - ρ) / 2))] with δ hδ
    obtain ⟨hδ0, hδlt⟩ := hδ
    have hδr : 2 * δ < r₀ := by linarith [hδlt.trans_le (min_le_left _ _)]
    have hδρ : δ < (1 - ρ) / 2 := hδlt.trans_le (min_le_right _ _)
    refine (measure_mono ?_).trans (hdy δ hδ0 hδr)
    intro ω hω hgood
    apply hω
    calc (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ), largestExitTimeRV (μ ω) D)
        ≤ largestExitTimeRV (μ ω) (ball 0 ρ) := iSup₂_le fun D hD => largestExitTimeRV_mono _ hD
      _ < ⊤ := largestExitTimeRV_ball_zero_lt_top_of_dyadic (mul_pos two_pos hδ0) (by linarith) hβ0
          (by linarith) hgood
  -- second statement: `sup_{y ∈ B_ρ} 𝓜(B_δ(y)) ≤ δ^{β/2}` with polynomially high probability
  refine ⟨hae, ?_⟩
  obtain ⟨δ₁, hδ₁, hasymp⟩ := exists_pos_log_rpow_le hβ0
  refine ⟨p, hp, max K 0 * (1 - (1 / 2) ^ p)⁻¹ * 2 ^ p, min (r₀ / 2) (min ((1 - ρ) / 3) δ₁),
    lt_min (half_pos hr₀) (lt_min (by linarith) hδ₁), fun δ hδ0 hδlt => ?_⟩
  have hδr : 2 * δ < r₀ := by linarith [hδlt.trans_le (min_le_left _ _)]
  have hδρ : δ < (1 - ρ) / 3 := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδδ₁ : δ < δ₁ := hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine (measure_mono (Set.compl_subset_compl.mpr ?_)).trans ((hdy δ hδ0 hδr).trans (le_of_eq ?_))
  · intro ω hgood y hy
    have hsub : ball y δ ⊆ ball 0 (1 - 2 * δ) :=
      ball_subset_ball' (by rw [mem_ball] at hy; linarith)
    exact (largestExitTimeRV_ball_le_of_dyadic hδ0 (by linarith) hβ0 hsub hgood).trans
      (ENNReal.ofReal_le_ofReal (hasymp δ hδ0 hδδ₁))
  · congr 1
    rw [Real.mul_rpow zero_le_two hδ0.le]
    ring

end MatedCRT
