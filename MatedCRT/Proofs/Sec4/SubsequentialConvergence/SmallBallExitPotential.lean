import MatedCRT.Proofs.Infra.LogKernel
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit

/-! Small-ball exit-potential estimates from volume growth. -/

namespace MatedCRT

open MeasureTheory Filter Metric Set HarmonicBalls
open scoped ENNReal

/-- The upper volume-growth estimate gives the small-ball logarithmic
exit-potential bound simultaneously at all sufficiently small radii and
all centres in a smaller ball. This is the potential estimate used in the
proof of Lemma 3.1. -/
theorem smallBallExitPotential_of_volumeGrowth
    {μ : Measure ℂ} {ρ R βminus β : ℝ} (hρR : ρ < R)
    (hvol : VolumeGrowth μ R βminus β) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ y ∈ ball (0 : ℂ) ρ,
      largestExitTimeRV μ (ball y r) ≤ ENNReal.ofReal (r ^ (β / 2)) := by
  obtain ⟨_, hβ, s, hs, hgrowth⟩ := hvol
  obtain ⟨t, ht, htbound⟩ := exists_pos_log_rpow_le hβ
  refine ⟨min t (min (s / 2) (min ((R - ρ) / 2) (1 / 2))),
    lt_min ht (lt_min (half_pos hs) (lt_min (half_pos (sub_pos.mpr hρR)) (by norm_num))), ?_⟩
  intro r hr hr₀ y hy
  have hrt : r < t := hr₀.trans_le (min_le_left _ _)
  have hrs : 2 * r < s := by
    have h := hr₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hrR : r < (R - ρ) / 2 := hr₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrhalf : r ≤ 1 / 2 := (hr₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hsub : ball y r ⊆ ball 0 R := by
    apply ball_subset_ball'
    rw [mem_ball] at hy
    linarith
  have hdy : DyadicVolumeBound μ R (2 * r) β := by
    intro z hz k
    have hp : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) _
    have hp1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsmall : 2 * r * (1 / 2 : ℝ) ^ k < s :=
      lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) hp1) hrs
    exact (hgrowth _ (mul_pos (by positivity) hp) hsmall z hz).2
  exact (largestExitTimeRV_ball_le_of_dyadic hr hrhalf hβ hsub hdy).trans
    (ENNReal.ofReal_le_ofReal (htbound r hr hrt))

/-- For an LQG cone, Lemma 2.7 supplies a common almost sure event on
which the small-ball exit-potential bound holds at every small radius. -/
theorem MatedCRTEnv.IsValid.ae_smallBallExitPotential
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : ρ < 1) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (h27 : VolumeGrowthStmt) :
    ∀ᵐ ω ∂S.P, ∃ q : ℝ, 0 < q ∧ ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      ∀ y ∈ ball (0 : ℂ) ρ,
        largestExitTimeRV (S.μ ω) (ball y r) ≤ ENNReal.ofReal (r ^ q) := by
  have hρR : ρ < (1 + ρ) / 2 := by linarith
  have hR1 : (1 + ρ) / 2 < 1 := by linarith
  filter_upwards [hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hR1] with ω hω
  obtain ⟨βminus, β, hvol⟩ := hω
  obtain ⟨r₀, hr₀, hbound⟩ := smallBallExitPotential_of_volumeGrowth hρR hvol
  exact ⟨β / 2, half_pos hvol.2.1, r₀, hr₀, hbound⟩

/-- Volume growth supplies the small-radius hypothesis used by the
interior equicontinuity estimate. -/
theorem MatedCRTEnv.IsValid.ae_exitPotential_goodRadii
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : ρ < 1) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (h27 : VolumeGrowthStmt) :
    ∀ᵐ ω ∂S.P, ∃ q : ℝ, 0 < q ∧ ∀ R₀ : ℝ, 0 < R₀ →
      ∃ R : ℝ, 0 < R ∧ R < R₀ ∧ ∀ y ∈ ball (0 : ℂ) ρ,
        largestExitTimeRV (S.μ ω) (ball y R) ≤ ENNReal.ofReal (R ^ q) := by
  filter_upwards [hS.ae_smallBallExitPotential hγ hγ2 hρ h27] with ω hω
  obtain ⟨q, hq, r₀, hr₀, hbound⟩ := hω
  refine ⟨q, hq, fun R₀ hR₀ => ?_⟩
  refine ⟨min R₀ r₀ / 2, half_pos (lt_min hR₀ hr₀), ?_, ?_⟩
  · have := min_le_left R₀ r₀
    linarith [lt_min hR₀ hr₀]
  · apply hbound _ (half_pos (lt_min hR₀ hr₀))
    have := min_le_right R₀ r₀
    linarith [lt_min hR₀ hr₀]

end MatedCRT
