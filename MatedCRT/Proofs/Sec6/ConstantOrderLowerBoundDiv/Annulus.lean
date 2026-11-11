import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv

/-!
# Lemma 6.8, Step 4 at a good annulus, route (b)

`ExitTimeLogLossStep` bounds the second moment of the exit time from `B' = B_{s}(y)`, `s = 𝐫_z/4`, by
`Q² = (sup_{v ∈ B'} ∫_{B_{ε^α}(B')} (log (s/|u - v|) + 1) dμ_h(u) + log (1/s) μ_h(B_{ε^α}(B')))²`. When `B'` and its
`ε^α`-neighbourhood lie in the annulus `𝔸 = 𝔸_{𝐫_z, 2𝐫_z}(z)` and `y ∈ 𝔸`:
* `logPotential_le`: the first term is at most `L = sup_{v ∈ 𝔸} ∫_𝔸 (log (𝐫_z/|u - v|) + 1) dμ_h(u)`;
* `measure_le_logPotential`: `μ_h(B_{ε^α}(B')) ≤ L`, since the integrand at `v = y` is at least `1` on `B_{𝐫_z}(y)`;
so `Q ≤ (1 + log (4/𝐫_z)) L` (`exitTimeLogLoss_le`), and on `E_{𝐫_z}(z)`, `L ≤ C μ_h(B_{𝐜₀ 𝐫_z}(y))`.
`ofReal_le_of_moments` is the arithmetic of the second moment method (line 2545).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

namespace ConstantOrderDiv

/-- The kernel at scale `R/4` is at most the kernel at scale `R` (with Lean's `log 0 = 0` at `x = 0`). -/
theorem ofReal_log_quarter_le {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.log (R / 4 / x) + 1) ≤ ENNReal.ofReal (Real.log (R / x) + 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact ENNReal.ofReal_le_ofReal (add_le_add (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right (by linarith) hx.le)) le_rfl)

/-- The kernel at scale `R` is at least `1` at distance `x < R`. -/
theorem one_le_ofReal_log {R x : ℝ} (hx : 0 ≤ x) (hxR : x < R) :
    1 ≤ ENNReal.ofReal (Real.log (R / x) + 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (Real.log_nonneg ?_))
    rw [le_div_iff₀ hx, one_mul]
    exact hxR.le

/-- The good-annulus quantity `L = sup_{v ∈ 𝔸} ∫_𝔸 (log (R/|u - v|) + 1) dμ(u)` (left side of eq:good-annulus-event). -/
noncomputable def annulusLogPotential (μ : Measure ℂ) (R : ℝ) (𝔸 : Set ℂ) : ℝ≥0∞ :=
  ⨆ v ∈ 𝔸, ∫⁻ u in 𝔸, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ

theorem logPotential_le (μ : Measure ℂ) {R : ℝ} (hR : 0 < R) {𝔸 D T : Set ℂ} (hD : D ⊆ 𝔸) (hT : T ⊆ 𝔸) :
    (⨆ v ∈ D, ∫⁻ u in T, ENNReal.ofReal (Real.log (R / 4 / ‖u - v‖) + 1) ∂μ) ≤ annulusLogPotential μ R 𝔸 :=
  iSup₂_le fun v hv => by
    calc ∫⁻ u in T, ENNReal.ofReal (Real.log (R / 4 / ‖u - v‖) + 1) ∂μ
        ≤ ∫⁻ u in 𝔸, ENNReal.ofReal (Real.log (R / 4 / ‖u - v‖) + 1) ∂μ := lintegral_mono_set hT
      _ ≤ ∫⁻ u in 𝔸, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ :=
          lintegral_mono fun u => ofReal_log_quarter_le hR (norm_nonneg _)
      _ ≤ annulusLogPotential μ R 𝔸 :=
          le_iSup₂ (f := fun v (_ : v ∈ 𝔸) => ∫⁻ u in 𝔸, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ) v (hD hv)

theorem measure_le_logPotential (μ : Measure ℂ) {R : ℝ} {𝔸 T : Set ℂ} {y : ℂ} (hTm : MeasurableSet T)
    (hT : T ⊆ 𝔸) (hy : y ∈ 𝔸) (hTy : T ⊆ ball y R) : μ T ≤ annulusLogPotential μ R 𝔸 :=
  calc μ T = ∫⁻ _ in T, 1 ∂μ := (setLIntegral_one T).symm
    _ ≤ ∫⁻ u in T, ENNReal.ofReal (Real.log (R / ‖u - y‖) + 1) ∂μ :=
        setLIntegral_mono' hTm fun _u hu => one_le_ofReal_log (norm_nonneg _) (mem_ball_iff_norm.1 (hTy hu))
    _ ≤ ∫⁻ u in 𝔸, ENNReal.ofReal (Real.log (R / ‖u - y‖) + 1) ∂μ := lintegral_mono_set hT
    _ ≤ annulusLogPotential μ R 𝔸 :=
        le_iSup₂ (f := fun v (_ : v ∈ 𝔸) => ∫⁻ u in 𝔸, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ) y hy

/-- **Step 4, route (b)**: the quantity of `ExitTimeLogLossStep` for `B_{R/4}(y)` is at most
`(1 + log (4/R)) L`. -/
theorem exitTimeLogLoss_le (μ : Measure ℂ) {R : ℝ} (hR : 0 < R) {𝔸 D T : Set ℂ} {y : ℂ} (hTm : MeasurableSet T)
    (hD : D ⊆ 𝔸) (hT : T ⊆ 𝔸) (hy : y ∈ 𝔸) (hTy : T ⊆ ball y R) :
    (⨆ v ∈ D, ∫⁻ u in T, ENNReal.ofReal (Real.log (R / 4 / ‖u - v‖) + 1) ∂μ) +
        ENNReal.ofReal (Real.log (1 / (R / 4))) * μ T ≤
      (1 + ENNReal.ofReal (Real.log (4 / R))) * annulusLogPotential μ R 𝔸 := by
  have h4 : 1 / (R / 4) = 4 / R := by field_simp
  rw [h4, add_mul, one_mul]
  gcongr
  · exact logPotential_le μ hR hD hT
  · exact measure_le_logPotential μ hTm hT hy hTy

/-- On the good annulus event, `L ≤ C μ(B_{c₀ R}(y))` for every `y ∈ 𝔸_{R,2R}(z)`. -/
theorem annulusLogPotential_le_of_good {μ : Measure ℂ} {c₀ C R : ℝ} {z y : ℂ}
    (hE : IsGoodAnnulusEvent μ c₀ C R z) (hy : y ∈ annulus z R (2 * R)) :
    annulusLogPotential μ R (annulus z R (2 * R)) ≤ ENNReal.ofReal C * μ (ball y (c₀ * R)) :=
  hE.trans (by gcongr; exact iInf₂_le y hy)

/-- **The arithmetic of the second moment method** (line 2545): if `c m ≤ E[V]`, `E[τ²] ≤ K m²` and
`E[V]² ≤ E[τ²] P`, with `0 < m < ∞`, then `P ≥ c²/K`. -/
theorem ofReal_le_of_moments {X Y P m : ℝ≥0∞} {c K : ℝ} (hc : 0 ≤ c) (hK : 0 < K) (hm0 : m ≠ 0)
    (hmtop : m ≠ ⊤) (hX : ENNReal.ofReal c * m ≤ X) (hY : Y ≤ ENNReal.ofReal K * m ^ 2) (hPZ : X ^ 2 ≤ Y * P) :
    ENNReal.ofReal (c ^ 2 / K) ≤ P := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hm2t : m ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hmtop
  have key : m ^ 2 * ENNReal.ofReal (c ^ 2) ≤ m ^ 2 * (ENNReal.ofReal K * P) := by
    calc m ^ 2 * ENNReal.ofReal (c ^ 2) = (ENNReal.ofReal c * m) ^ 2 := by
          rw [ENNReal.ofReal_pow hc, mul_pow, mul_comm]
      _ ≤ X ^ 2 := by gcongr
      _ ≤ Y * P := hPZ
      _ ≤ ENNReal.ofReal K * m ^ 2 * P := by gcongr
      _ = m ^ 2 * (ENNReal.ofReal K * P) := by ring
  have key' : ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal K * P := by
    calc ENNReal.ofReal (c ^ 2) = (m ^ 2)⁻¹ * (m ^ 2 * ENNReal.ofReal (c ^ 2)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hm2 hm2t, one_mul]
      _ ≤ (m ^ 2)⁻¹ * (m ^ 2 * (ENNReal.ofReal K * P)) := by gcongr
      _ = ENNReal.ofReal K * P := by rw [← mul_assoc, ENNReal.inv_mul_cancel hm2 hm2t, one_mul]
  rw [ENNReal.ofReal_div_of_pos hK]
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  exact key'

end ConstantOrderDiv

end MatedCRT
