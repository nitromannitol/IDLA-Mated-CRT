import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Infra.Setting
import LatticeProb.Analysis.LogKernel

/-!
# The logarithmic kernel under a dyadic volume bound

`𝓜(D) = sup_{z ∈ D} ∫_D (log (1/|z - w|) + 1) dμ(w)` (eq:largest-exit-time-rv) is controlled by the volume of
dyadic balls: if `μ(B_{r 2^{-k}}(z)) ≤ (r 2^{-k})^β` for all `k ∈ ℕ`, the partition of `B_r(z)` into dyadic annuli
(proof of Lemma 2.17, line 911, as in BG20 Lemma A.3) gives
`∫_{B_r(z)} (log (1/|z - w|) + 1) dμ(w) ≤ (log (1/r) + 1 + log 2) r^β (1 - 2^{-β})⁻¹`
(`setLIntegral_ball_log_le`). Consequences: bounds on `𝓜(B_δ(y))` and finiteness of `𝓜(B_ρ)`
(`largestExitTimeRV_ball_le_of_dyadic`, `largestExitTimeRV_ball_zero_lt_top_of_dyadic`), a union bound over dyadic
scales for events with polynomially high probability (`measure_compl_iInter_le`), and the limit
`(log (1/δ) + 1) δ^{β/2} → 0` (`exists_pos_log_rpow_le`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The *dyadic volume bound* with exponent `β` at the top radius `r` on `B_R`:
`μ(B_{r 2^{-k}}(z)) ≤ (r 2^{-k})^β` for every `z ∈ B_R` and every `k ∈ ℕ`. -/
def DyadicVolumeBound (μ : Measure ℂ) (R r β : ℝ) : Prop :=
  ∀ z ∈ ball (0 : ℂ) R, ∀ k : ℕ, μ (ball z (r * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((r * (1 / 2) ^ k) ^ β)

/-- `(r 2^{-k})^β = r^β (2^{-β})^k`. -/
theorem rpow_mul_half_pow {r : ℝ} (β : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    (r * (1 / 2) ^ k) ^ β = r ^ β * ((1 / 2) ^ β) ^ k :=
  LatticeProb.LogKernel.rpow_mul_half_pow β hr k

/-- Geometric sum over dyadic scales: `∑_k K (r 2^{-k})^β = K r^β (1 - 2^{-β})⁻¹`. -/
theorem tsum_ofReal_mul_rpow_half_pow {K r β : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hβ : 0 < β) :
    ∑' k : ℕ, ENNReal.ofReal (K * (r * (1 / 2) ^ k) ^ β) =
      ENNReal.ofReal (K * r ^ β * (1 - (1 / 2) ^ β)⁻¹) :=
  LatticeProb.LogKernel.tsum_ofReal_mul_rpow_half_pow hK hr hβ

/-- Pointwise dyadic bound of the logarithmic kernel on `B_r(z)`, `r ≤ 1`: with `c = log (1/r) + 1 + log 2`,
`log (1/|z - w|) + 1 ≤ c · #{k : |z - w| < r 2^{-k}}` (for `w = z` the right side is infinite). -/
theorem ofReal_log_le_tsum_indicator {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {z w : ℂ} (hw : w ∈ ball z r) :
    ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ≤
      ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator
        (fun _ => ENNReal.ofReal (Real.log (1 / r) + 1 + Real.log 2)) w :=
  LatticeProb.LogKernel.ofReal_log_le_tsum_indicator hr0 hr1 hw

/-- **Dyadic bound of the logarithmic integral.** If `μ(B_{r 2^{-k}}(z)) ≤ (r 2^{-k})^β` for all `k`, `0 < r ≤ 1`, then
`∫_{B_r(z)} (log (1/|z - w|) + 1) dμ(w) ≤ (log (1/r) + 1 + log 2) r^β (1 - 2^{-β})⁻¹`. -/
theorem setLIntegral_ball_log_le {μ : Measure ℂ} {z : ℂ} {r β : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hβ : 0 < β)
    (hvol : ∀ k : ℕ, μ (ball z (r * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((r * (1 / 2) ^ k) ^ β)) :
    ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
      ENNReal.ofReal ((Real.log (1 / r) + 1 + Real.log 2) * r ^ β * (1 - (1 / 2) ^ β)⁻¹) :=
  LatticeProb.LogKernel.setLIntegral_ball_log_le hr0 hr1 hβ hvol

/-- `𝓜(B_δ(y)) ≤ (log (1/(2δ)) + 1 + log 2) (2δ)^β (1 - 2^{-β})⁻¹` under the dyadic volume bound at the top radius
`2δ` on a ball `B_R ⊇ B_δ(y)`. -/
theorem largestExitTimeRV_ball_le_of_dyadic {μ : Measure ℂ} {y : ℂ} {R δ β : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hβ : 0 < β) (hy : ball y δ ⊆ ball 0 R) (hV : DyadicVolumeBound μ R (2 * δ) β) :
    largestExitTimeRV μ (ball y δ) ≤
      ENNReal.ofReal ((Real.log (1 / (2 * δ)) + 1 + Real.log 2) * (2 * δ) ^ β * (1 - (1 / 2) ^ β)⁻¹) := by
  unfold largestExitTimeRV
  refine iSup₂_le fun z hz => ?_
  have hsub : ball y δ ⊆ ball z (2 * δ) := by
    intro w hw
    rw [mem_ball] at hw hz ⊢
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < 2 * δ := by rw [dist_comm y z]; linarith
  exact (lintegral_mono_set hsub).trans
    (setLIntegral_ball_log_le (by linarith) (by linarith) hβ (hV z (hy hz)))

/-- A measure with `μ(B_r(z)) ≤ r^β` for every `z ∈ cl B_ρ` is finite on `B_ρ` (finite cover by `r`-balls). -/
theorem measure_ball_lt_top_of_vol {μ : Measure ℂ} {ρ r β : ℝ} (hr : 0 < r)
    (hvol : ∀ z ∈ closedBall (0 : ℂ) ρ, μ (ball z r) ≤ ENNReal.ofReal (r ^ β)) : μ (ball 0 ρ) < ⊤ :=
  LatticeProb.LogKernel.measure_ball_lt_top_of_vol hr hvol

/-- `𝓜(B_ρ) < ∞` under the dyadic volume bound at a top radius `r ≤ 1` on a ball `B_R`, `R > ρ`. -/
theorem largestExitTimeRV_ball_zero_lt_top_of_dyadic {μ : Measure ℂ} {ρ R r β : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hβ : 0 < β) (hρR : ρ < R) (hV : DyadicVolumeBound μ R r β) : largestExitTimeRV μ (ball 0 ρ) < ⊤ := by
  have hμ : μ (ball 0 ρ) < ⊤ := measure_ball_lt_top_of_vol (β := β) hr0 fun z hz => by
    simpa using hV z (closedBall_subset_ball hρR hz) 0
  have hbound : ∀ z ∈ ball (0 : ℂ) ρ,
      ∫⁻ w in ball 0 ρ, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
        ENNReal.ofReal ((Real.log (1 / r) + 1 + Real.log 2) * r ^ β * (1 - (1 / 2) ^ β)⁻¹) +
          ENNReal.ofReal (Real.log (1 / r) + 1) * μ (ball 0 ρ) := by
    intro z hz
    have hle : ∀ w ∈ ball (0 : ℂ) ρ \ ball z r,
        ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ≤ ENNReal.ofReal (Real.log (1 / r) + 1) := by
      intro w hw
      have hd : r ≤ ‖z - w‖ := by
        have h := hw.2
        rw [mem_ball, not_lt, dist_eq_norm, norm_sub_rev] at h
        exact h
      refine ENNReal.ofReal_le_ofReal ?_
      have := Real.log_le_log (one_div_pos.mpr (hr0.trans_le hd)) (one_div_le_one_div_of_le hr0 hd)
      linarith
    calc ∫⁻ w in ball 0 ρ, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
        ≤ ∫⁻ w in ball z r ∪ (ball 0 ρ \ ball z r), ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ := by
          refine lintegral_mono_set fun w hw => ?_
          by_cases h : w ∈ ball z r
          · exact Or.inl h
          · exact Or.inr ⟨hw, h⟩
      _ ≤ ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ +
            ∫⁻ w in ball 0 ρ \ ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ :=
          lintegral_union_le _ _ _
      _ ≤ _ := by
          refine add_le_add (setLIntegral_ball_log_le hr0 hr1 hβ
            (hV z (ball_subset_ball hρR.le hz))) ?_
          calc ∫⁻ w in ball 0 ρ \ ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
              ≤ ∫⁻ _ in ball 0 ρ \ ball z r, ENNReal.ofReal (Real.log (1 / r) + 1) ∂μ :=
                lintegral_mono_ae ((ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)).2
                  (Eventually.of_forall hle))
            _ = ENNReal.ofReal (Real.log (1 / r) + 1) * μ (ball 0 ρ \ ball z r) := setLIntegral_const _ _
            _ ≤ ENNReal.ofReal (Real.log (1 / r) + 1) * μ (ball 0 ρ) := by
                gcongr
                exact Set.sdiff_subset
  calc largestExitTimeRV μ (ball 0 ρ) ≤
      ENNReal.ofReal ((Real.log (1 / r) + 1 + Real.log 2) * r ^ β * (1 - (1 / 2) ^ β)⁻¹) +
        ENNReal.ofReal (Real.log (1 / r) + 1) * μ (ball 0 ρ) := by
        unfold largestExitTimeRV
        exact iSup₂_le hbound
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ⟩

/-- Union bound over the dyadic scales `r 2^{-k}` for a family of events with
`P[(E s)ᶜ] ≤ K s^p` for `0 < s < r₀`. -/
theorem measure_compl_iInter_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    {K p r₀ : ℝ} (hp : 0 < p) (hE : ∀ s, 0 < s → s < r₀ → P (E s)ᶜ ≤ ENNReal.ofReal (K * s ^ p))
    {r : ℝ} (hr : 0 < r) (hrr : r < r₀) {F : Set Ω} (hF : (⋂ k : ℕ, E (r * (1 / 2) ^ k)) ⊆ F) :
    P Fᶜ ≤ ENNReal.ofReal (max K 0 * (1 - (1 / 2) ^ p)⁻¹ * r ^ p) :=
  LatticeProb.LogKernel.measure_compl_iInter_le hp hE hr hrr hF

/-- An eventual property as `r → 0⁺` holds on an interval `(0, r₁)`. -/
theorem exists_pos_of_eventually_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → p r :=
  LatticeProb.LogKernel.exists_pos_of_eventually_nhdsGT h

/-- Absorption of the logarithm: `(log (1/(2δ)) + 1 + log 2) (2δ)^β (1 - 2^{-β})⁻¹ ≤ δ^{β/2}` for small `δ > 0`. -/
theorem exists_pos_log_rpow_le {β : ℝ} (hβ : 0 < β) :
    ∃ δ₁ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      (Real.log (1 / (2 * δ)) + 1 + Real.log 2) * (2 * δ) ^ β * (1 - (1 / 2) ^ β)⁻¹ ≤ δ ^ (β / 2) :=
  LatticeProb.LogKernel.exists_pos_log_rpow_le hβ

end MatedCRT
