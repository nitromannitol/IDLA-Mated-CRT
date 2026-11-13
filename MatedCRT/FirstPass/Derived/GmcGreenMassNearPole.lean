import MatedCRT.FirstPass.Derived.GmcIntensityBound
import MatedCRT.FirstPass.Derived.GmcGreenMeasureFinite
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenDomainMonotone

/-!
# The Green-weighted γ-LQG mass near a pole away from the origin

Let `h^ℂ` be a whole-plane GFF, `0 < γ < 2`, `Γ = gmcLimit γ ρ ρ₂ ψ` the cut-off γ-LQG measure of
`h^ℂ - γ log |·|`, and `m = 1_D · 2 G_D(y, ·) · Γ` the Green-weighted measure of the disc `D = B_r(z)` with pole
`y ∈ D`. For a pole `y ≠ 0` and `0 < 2 s < |y|`:

* `greenOccupationDensity_le_dyadic`: the density `1_D · 2 G_D(y, ·)` is at most
  `π⁻¹ log (2 r / s) + π⁻¹ log 2 · Σ_i 1_{closedBall y (s 2^{-i})}` (logarithmic bound of the Green function and a
  dyadic count of `log (s / |x - y|)`);
* `lintegral_gmcGreenMeasure_closedBall_ne_top`: `E m(closedBall y s) < ∞`, since
  `E Γ(closedBall y t) ≤ C t²` for `t ≤ s` (`lintegral_gmcLimit_closedBall_le`) and `Σ_i 4^{-i} < ∞`;
* `ae_gmcGreenMeasure_ball_lt_top`: almost surely `m(D) < ∞`.
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Dyadic count of a logarithm: for `0 < d` and `0 < s` there is `N` with `log (s / d) ≤ N log 2` and
`d ≤ s 2^{-i}` for every `i < N`. -/
lemma exists_dyadic_count {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    ∃ N : ℕ, Real.log (s / d) ≤ N * Real.log 2 ∧ ∀ i < N, d ≤ s * (1 / 2) ^ i := by
  classical
  have hex : ∃ n : ℕ, s / d < 2 ^ n := pow_unbounded_of_one_lt (s / d) one_lt_two
  refine ⟨Nat.find hex, ?_, fun i hi => ?_⟩
  · rw [← Real.log_pow]
    exact (Real.log_lt_log (div_pos hs hd) (Nat.find_spec hex)).le
  · have h := (le_div_iff₀ hd).1 (not_lt.1 (Nat.find_min hex hi))
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos two_pos i)]
    linarith

/-- **Dyadic bound for the occupation density near the pole.** For a pole `y ∈ B_r(z)` and `s > 0`,
everywhere the occupation density `1_D · 2 G_D(y, ·)` of `D = B_r(z)` is at most
`π⁻¹ log (2 r / s) + π⁻¹ log 2 · Σ_i 1_{closedBall y (s 2^{-i})}`. -/
lemma greenOccupationDensity_le_dyadic {z y : ℂ} {r s : ℝ} (hy : y ∈ ball z r) (hs : 0 < s) (x : ℂ) :
    greenOccupationDensity z y r x ≤ ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / s)) +
      ENNReal.ofReal (Real.pi⁻¹ * Real.log 2) *
        ∑' i : ℕ, (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x := by
  have hb : 0 < Real.pi⁻¹ * Real.log 2 := mul_pos (inv_pos.2 Real.pi_pos) (Real.log_pos one_lt_two)
  by_cases hxD : x ∈ ball z r
  swap
  · rw [greenOccupationDensity_of_notMem hxD]
    exact zero_le
  by_cases hxy : x = y
  · have h1 : ∀ i : ℕ, (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x = 1 := fun i => by
      rw [indicator_of_mem (by rw [hxy]; exact mem_closedBall_self (mul_pos hs (pow_pos (by norm_num) i)).le),
        Pi.one_apply]
    rw [tsum_congr h1, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hb).ne', add_top]
    exact le_top
  have hr : 0 < r := pos_of_mem_ball hy
  have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hO : ball z r ⊆ closedBall y (2 * r) := by
    intro w hw
    rw [mem_closedBall]
    have h1 := mem_ball.1 hw
    have h2 := mem_ball.1 hy
    linarith [dist_triangle_right w y z]
  have hG := greenFunction_le_log_div (by positivity : 0 < 2 * r) hO hy hxD (Ne.symm hxy)
  obtain ⟨N, hN, hNi⟩ := exists_dyadic_count hs hd
  have hsplit : Real.log (2 * r / ‖y - x‖) = Real.log (2 * r / s) + Real.log (s / ‖y - x‖) := by
    rw [← Real.log_mul (div_pos (by positivity) hs).ne' (div_pos hs hd).ne']
    congr 1
    field_simp
  have key : 2 * ((2 * Real.pi)⁻¹ * Real.log (2 * r / ‖y - x‖)) =
      Real.pi⁻¹ * Real.log (2 * r / s) + Real.pi⁻¹ * Real.log (s / ‖y - x‖) := by
    rw [hsplit, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul, mul_add]
  have hcount : (N : ℝ≥0∞) ≤ ∑' i : ℕ, (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x := by
    have hsum : ∑ i ∈ Finset.range N, (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x = N := by
      rw [Finset.sum_congr rfl fun i hi => indicator_of_mem (mem_closedBall.2 (by
        rw [dist_eq_norm, norm_sub_rev]; exact hNi i (Finset.mem_range.1 hi))) _]
      simp
    rw [← hsum]
    exact ENNReal.sum_le_tsum _
  rw [greenOccupationDensity_of_mem hxD]
  calc 2 * ENNReal.ofReal (greenFunction (ball z r) y x)
      = ENNReal.ofReal (2 * greenFunction (ball z r) y x) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / s) + Real.pi⁻¹ * Real.log (s / ‖y - x‖)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / s)) +
          ENNReal.ofReal (Real.pi⁻¹ * Real.log (s / ‖y - x‖)) := ENNReal.ofReal_add_le
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        calc ENNReal.ofReal (Real.pi⁻¹ * Real.log (s / ‖y - x‖))
            ≤ ENNReal.ofReal (Real.pi⁻¹ * Real.log 2 * N) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (by rw [mul_comm (Real.log 2)]; exact hN)
                (inv_nonneg.2 Real.pi_pos.le)
          _ = ENNReal.ofReal (Real.pi⁻¹ * Real.log 2) * N := by
              rw [ENNReal.ofReal_mul hb.le, ENNReal.ofReal_natCast]
          _ ≤ _ := mul_le_mul_of_nonneg_left hcount zero_le

/-- The Lebesgue measure of a disc of radius `t ≥ 0` is `π t²`. -/
lemma volume_ball_eq_ofReal (y : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    volume (ball y t) = ENNReal.ofReal (Real.pi * t ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow ht, mul_comm (ENNReal.ofReal _),
    ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

/-- **Finite expected Green-weighted mass near a pole away from the origin.** For a whole-plane GFF `h^ℂ`,
`0 < γ < 2`, `ρ < ρ₂ < 1`, a pole `y ∈ B_r(z)` and `0 < 2 s < |y|`: `E m(closedBall y s) < ∞`, with
`m = gmcGreenMeasure γ ρ ρ₂ z y r ψ` the Green-weighted cut-off γ-LQG measure of `h^ℂ - γ log |·|`. -/
theorem lintegral_gmcGreenMeasure_closedBall_ne_top {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1)
    {z y : ℂ} {r s : ℝ} (hy : y ∈ ball z r) (hs : 0 < s) (hsy : 2 * s < ‖y‖) :
    ∫⁻ ω', gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
      (closedBall y s) ∂P' ≠ ∞ := by
  set ψ := clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) with hψdef
  set a := ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / s))
  set b := ENNReal.ofReal (Real.pi⁻¹ * Real.log 2)
  set K := Real.exp (γ ^ 2 * Real.log (‖y‖ + 2 * s + 1)) * (‖y‖ - 2 * s) ^ (-γ ^ 2)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
  have hψm : Measurable ψ :=
    measurable_unitDiskCircle _ fun r' z' hr' => (hG.measurable_circle r' z' hr').sub measurable_const
  have hΓm : ∀ B : Set ℂ, MeasurableSet B → Measurable fun ω' => gmcLimit γ ρ ρ₂ (ψ ω') B :=
    fun B hB => (Measure.measurable_coe hB).comp ((measurable_gmcLimit γ ρ ρ₂).comp hψm)
  have hball : ∀ t, 0 < t → t ≤ s → ∫⁻ ω', gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y t) ∂P' ≤
      ENNReal.ofReal K * volume (ball y (2 * t)) := fun t ht hts =>
    lintegral_gmcLimit_closedBall_le hG hγ hγ2 hρρ₂ hρ₂ (by linarith : 0 < ‖y‖ - 2 * s) ht (by linarith)
      (by linarith)
  have hrad : ∀ i : ℕ, 0 < s * (1 / 2) ^ i := fun i => mul_pos hs (pow_pos (by norm_num) i)
  have hTm : Measurable fun x : ℂ => ∑' i : ℕ, (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x :=
    Measurable.tsum fun i => measurable_one.indicator measurableSet_closedBall
  have hpt : ∀ ω', gmcGreenMeasure γ ρ ρ₂ z y r (ψ ω') (closedBall y s) ≤
      a * gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y s) +
        b * ∑' i : ℕ, gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y (s * (1 / 2) ^ i)) := by
    intro ω'
    rw [gmcGreenMeasure, withDensity_apply _ measurableSet_closedBall]
    calc ∫⁻ x in closedBall y s, greenOccupationDensity z y r x ∂gmcLimit γ ρ ρ₂ (ψ ω')
        ≤ ∫⁻ x in closedBall y s, (a + b * ∑' i : ℕ,
            (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x) ∂gmcLimit γ ρ ρ₂ (ψ ω') :=
          setLIntegral_mono' measurableSet_closedBall fun x _ => greenOccupationDensity_le_dyadic hy hs x
      _ = a * gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y s) + b * ∫⁻ x in closedBall y s, ∑' i : ℕ,
            (closedBall y (s * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x ∂gmcLimit γ ρ ρ₂ (ψ ω') := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_const_mul _ hTm]
      _ ≤ a * gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y s) +
            b * ∑' i : ℕ, gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y (s * (1 / 2) ^ i)) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le)
          refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
          rw [lintegral_tsum fun i => (measurable_one.indicator measurableSet_closedBall).aemeasurable]
          exact tsum_congr fun i => lintegral_indicator_one measurableSet_closedBall
  have hE : ∫⁻ ω', gmcGreenMeasure γ ρ ρ₂ z y r (ψ ω') (closedBall y s) ∂P' ≤
      a * (ENNReal.ofReal K * volume (ball y (2 * s))) +
        b * ∑' i : ℕ, ENNReal.ofReal K * volume (ball y (2 * (s * (1 / 2) ^ i))) := by
    calc ∫⁻ ω', gmcGreenMeasure γ ρ ρ₂ z y r (ψ ω') (closedBall y s) ∂P'
        ≤ ∫⁻ ω', (a * gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y s) +
            b * ∑' i : ℕ, gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y (s * (1 / 2) ^ i))) ∂P' := lintegral_mono hpt
      _ = a * ∫⁻ ω', gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y s) ∂P' +
            b * ∑' i : ℕ, ∫⁻ ω', gmcLimit γ ρ ρ₂ (ψ ω') (closedBall y (s * (1 / 2) ^ i)) ∂P' := by
          rw [lintegral_add_left ((hΓm _ measurableSet_closedBall).const_mul a),
            lintegral_const_mul _ (hΓm _ measurableSet_closedBall),
            lintegral_const_mul _ (Measurable.tsum fun i => hΓm _ measurableSet_closedBall),
            lintegral_tsum fun i => (hΓm _ measurableSet_closedBall).aemeasurable]
      _ ≤ _ := by
          refine add_le_add (mul_le_mul_of_nonneg_left (hball s hs le_rfl) zero_le)
            (mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun i => hball _ (hrad i) ?_) zero_le)
          exact mul_le_of_le_one_right hs.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hterm : ∀ i : ℕ, ENNReal.ofReal K * volume (ball y (2 * (s * (1 / 2) ^ i))) =
      ENNReal.ofReal (K * Real.pi * (2 * s) ^ 2 * ((1 / 2 : ℝ) ^ 2) ^ i) := by
    intro i
    rw [volume_ball_eq_ofReal y (by linarith [hrad i]), ← ENNReal.ofReal_mul hK]
    congr 1
    rw [← pow_mul, mul_comm 2 i, pow_mul]
    ring
  have hsum : Summable fun i : ℕ => K * Real.pi * (2 * s) ^ 2 * ((1 / 2 : ℝ) ^ 2) ^ i :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
  have htsum : ∑' i : ℕ, ENNReal.ofReal K * volume (ball y (2 * (s * (1 / 2) ^ i))) ≠ ∞ := by
    rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) hE
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htsum

/-- **Almost-sure finiteness near the pole.** Under the hypotheses of
`lintegral_gmcGreenMeasure_closedBall_ne_top`, almost surely `m(closedBall y s) < ∞`. -/
theorem ae_gmcGreenMeasure_closedBall_lt_top {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1)
    {z y : ℂ} {r s : ℝ} (hy : y ∈ ball z r) (hs : 0 < s) (hsy : 2 * s < ‖y‖) :
    ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
      (closedBall y s) < ∞ := by
  have hψm : Measurable (clockPsi (fun ω' => fieldCircleAverage γ (hc ω'))) :=
    measurable_unitDiskCircle _ fun r' z' hr' => (hG.measurable_circle r' z' hr').sub measurable_const
  exact ae_lt_top ((Measure.measurable_coe measurableSet_closedBall).comp
    ((measurable_gmcGreenMeasure γ ρ ρ₂ z y r).comp hψm))
    (lintegral_gmcGreenMeasure_closedBall_ne_top hG hγ hγ2 hρρ₂ hρ₂ hy hs hsy)

/-- **Finiteness of the Green-weighted γ-LQG mass of the disc, pole away from the origin.** For a whole-plane GFF
`h^ℂ`, `0 < γ < 2`, `ρ < ρ₂ < 1` and a pole `y ∈ B_r(z)` with `y ≠ 0`, almost surely
`m(B_r(z)) < ∞`, with `m = 1_D · 2 G_D(y, ·) · Γ` the Green-weighted cut-off γ-LQG measure of
`h^ℂ - γ log |·|`. -/
theorem ae_gmcGreenMeasure_ball_lt_top {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1)
    {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) (hy0 : y ≠ 0) :
    ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
      (ball z r) < ∞ := by
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hs : 0 < ‖y‖ / 4 := by positivity
  filter_upwards [ae_gmcGreenMeasure_closedBall_lt_top hG hγ hγ2 hρρ₂ hρ₂ hy hs (by linarith),
    ae_gmcGreenMeasure_lt_top_gff hG hγ hγ2 hρρ₂ hρ₂] with ω' h1 h2
  have hK : IsCompact (closedBall z r \ ball y (‖y‖ / 4)) := (isCompact_closedBall z r).diff isOpen_ball
  have hyK : y ∉ closedBall z r \ ball y (‖y‖ / 4) := fun h => h.2 (mem_ball_self hs)
  have hsub : ball z r ⊆ (closedBall z r \ ball y (‖y‖ / 4)) ∪ closedBall y (‖y‖ / 4) := by
    intro x hx
    by_cases hxy : x ∈ ball y (‖y‖ / 4)
    · exact Or.inr (ball_subset_closedBall hxy)
    · exact Or.inl ⟨ball_subset_closedBall hx, hxy⟩
  exact (measure_mono hsub).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h2 z y r hy _ hK hyK, h1⟩))

end MatedCRT.KilledOccupation
