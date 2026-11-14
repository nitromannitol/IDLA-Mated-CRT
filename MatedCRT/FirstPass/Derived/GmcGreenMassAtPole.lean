import MatedCRT.FirstPass.Derived.GmcAnnulusSeriesFinite
import MatedCRT.FirstPass.Derived.GmcGreenMassNearPole
import MatedCRT.FirstPass.Derived.LimClockOccupationAgreement

/-!
# The Green-weighted γ-LQG mass at the logarithmic singularity

Let `h^ℂ` be a whole-plane GFF, `0 < γ < 2`, `Γ = gmcLimit γ ρ ρ₂ ψ` the cut-off γ-LQG measure of
`h^ℂ - γ log |·|`, and `m = 1_D · 2 G_D(0, ·) · Γ` the Green-weighted measure of a disc `D = B_r(z)` containing the
origin, with pole at the origin, where the field has its `γ`-log singularity.

* `mem_eAdicAnnulus_floor`: the `e`-adic annuli `A_n = eAdicAnnulus 0 n` cover the punctured disc
  `0 < |x| ≤ 1/2`;
* `greenOccupationDensity_le_of_mem_eAdicAnnulus`: on `A_n` the density `1_D · 2 G_D(0, ·)` is at most
  `C_r (n + 1)` (`greenOccupationDensity_le_dyadic` with `s = 1/2`; only the dyadic scales `i < 2 (n + 1)` meet
  `A_n`, since `e < 4`);
* `ae_gmcGreenMeasure_ball_lt_top_pole_zero`: almost surely `m(D) < ∞`. Near the origin
  `m(B̄_{1/2}(0)) ≤ m{0} + Σ_n C_r (n + 1) Γ(A_n)`, where `Γ{0} = 0` and `Σ_n (n + 1) Γ(A_n) < ∞` almost surely
  (`ae_tsum_succ_mul_gmcLimit_eAdicAnnulus_lt_top`); away from the origin the Green-weighted measure is finite on
  compact sets (`ae_gmcGreenMeasure_lt_top_gff`).
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- `e^{-t} / (2e) = e^{-(t + 1)} / 2`. -/
lemma exp_neg_div_two_mul_exp (t : ℝ) :
    Real.exp (-t) / (2 * Real.exp 1) = Real.exp (-(t + 1)) / 2 := by
  rw [neg_add, Real.exp_add, Real.exp_neg 1]
  ring

/-- **The `e`-adic annuli cover the punctured disc.** A point `x` with `0 < |x| ≤ 1/2` lies in the annulus
`A_n = eAdicAnnulus 0 n` with `n = ⌊-log (2 |x|)⌋₊`. -/
lemma mem_eAdicAnnulus_floor {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1 / 2) :
    x ∈ eAdicAnnulus 0 ⌊-Real.log (2 * ‖x‖)⌋₊ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set u := -Real.log (2 * ‖x‖) with hu
  have hu0 : 0 ≤ u := by
    have := Real.log_le_sub_one_of_pos (mul_pos two_pos hn)
    linarith
  have hxu : ‖x‖ = Real.exp (-u) / 2 := by
    rw [hu, neg_neg, Real.exp_log (mul_pos two_pos hn)]
    ring
  have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
  have h2 : u < ⌊u⌋₊ + 1 := Nat.lt_floor_add_one u
  show Real.exp (-((0 : ℝ) + (⌊u⌋₊ : ℝ))) / (2 * Real.exp 1) ≤ ‖x‖ ∧
    ‖x‖ ≤ Real.exp (-((0 : ℝ) + (⌊u⌋₊ : ℝ))) / 2
  rw [zero_add, exp_neg_div_two_mul_exp, hxu]
  constructor
  · gcongr
  · gcongr

/-- The constant `C_r = π⁻¹ log (4 r) + 2 π⁻¹ log 2` of the occupation density on the `e`-adic annuli. -/
noncomputable def poleDensityConst (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / (1 / 2))) + 2 * ENNReal.ofReal (Real.pi⁻¹ * Real.log 2)

lemma poleDensityConst_lt_top (r : ℝ) : poleDensityConst r < ∞ :=
  ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top⟩

/-- **The occupation density on an `e`-adic annulus.** For a disc `D = B_r(z)` containing the origin, on the
annulus `A_n = eAdicAnnulus 0 n` the occupation density `1_D · 2 G_D(0, ·)` with pole `0` is at most
`C_r (n + 1)`. -/
lemma greenOccupationDensity_le_of_mem_eAdicAnnulus {z : ℂ} {r : ℝ} (h0 : (0 : ℂ) ∈ ball z r) {n : ℕ}
    {x : ℂ} (hx : x ∈ eAdicAnnulus 0 n) :
    greenOccupationDensity z 0 r x ≤ poleDensityConst r * ENNReal.ofReal ((n : ℝ) + 1) := by
  refine (greenOccupationDensity_le_dyadic h0 (by norm_num : (0 : ℝ) < 1 / 2) x).trans ?_
  have hx1 : Real.exp (-((0 : ℝ) + n)) / (2 * Real.exp 1) ≤ ‖x‖ := hx.1
  rw [zero_add, exp_neg_div_two_mul_exp] at hx1
  have hz : ∀ i ∉ Finset.range (2 * n + 2),
      (closedBall (0 : ℂ) (1 / 2 * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x = 0 := by
    intro i hi
    rw [Finset.mem_range, not_lt] at hi
    refine indicator_of_notMem (fun hxi => ?_) _
    rw [mem_closedBall, dist_zero_right] at hxi
    have hpow : (1 / 2 : ℝ) ^ i ≤ (1 / 4 : ℝ) ^ (n + 1) := by
      calc (1 / 2 : ℝ) ^ i ≤ (1 / 2) ^ (2 * (n + 1)) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = (1 / 4) ^ (n + 1) := by rw [pow_mul]; norm_num
    have he4 : 1 / 4 < Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
    have hlt : (1 / 4 : ℝ) ^ (n + 1) < Real.exp (-1) ^ (n + 1) :=
      pow_lt_pow_left₀ he4 (by norm_num) (by omega)
    have heq : Real.exp (-1) ^ (n + 1) = Real.exp (-((n : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    linarith
  rw [tsum_eq_sum hz]
  have hcount : ∑ i ∈ Finset.range (2 * n + 2),
      (closedBall (0 : ℂ) (1 / 2 * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x ≤
        2 * ENNReal.ofReal ((n : ℝ) + 1) := by
    calc ∑ i ∈ Finset.range (2 * n + 2),
          (closedBall (0 : ℂ) (1 / 2 * (1 / 2) ^ i)).indicator (1 : ℂ → ℝ≥0∞) x
        ≤ ∑ _i ∈ Finset.range (2 * n + 2), (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun i _ => indicator_le_self' (fun _ _ => zero_le) x
      _ = 2 * ENNReal.ofReal ((n : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast]
          push_cast
          ring
  have ha1 : 1 ≤ ENNReal.ofReal ((n : ℝ) + 1) := ENNReal.one_le_ofReal.2 (by linarith [n.cast_nonneg (α := ℝ)])
  calc ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / (1 / 2))) + ENNReal.ofReal (Real.pi⁻¹ * Real.log 2) *
        ∑ i ∈ Finset.range (2 * n + 2), (closedBall (0 : ℂ) (1 / 2 * (1 / 2) ^ i)).indicator 1 x
      ≤ ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / (1 / 2))) * ENNReal.ofReal ((n : ℝ) + 1) +
          ENNReal.ofReal (Real.pi⁻¹ * Real.log 2) * (2 * ENNReal.ofReal ((n : ℝ) + 1)) := by
        gcongr
        calc ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / (1 / 2)))
            = ENNReal.ofReal (Real.pi⁻¹ * Real.log (2 * r / (1 / 2))) * 1 := (mul_one _).symm
          _ ≤ _ := by gcongr
    _ = poleDensityConst r * ENNReal.ofReal ((n : ℝ) + 1) := by
        rw [poleDensityConst]
        ring

/-- **Finiteness of the Green-weighted γ-LQG mass of a disc, pole at the logarithmic singularity.** For a
whole-plane GFF `h^ℂ`, `0 < γ < 2`, `ρ < ρ₂ < 1` and a disc `B_r(z)` containing the origin, almost surely
`m(B_r(z)) < ∞`, with `m = 1_D · 2 G_D(0, ·) · Γ` the Green-weighted cut-off γ-LQG measure of
`h^ℂ - γ log |·|`. -/
theorem ae_gmcGreenMeasure_ball_lt_top_pole_zero {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z : ℂ} {r : ℝ} (h0 : (0 : ℂ) ∈ ball z r) :
    ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ρ₂ z 0 r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
      (ball z r) < ∞ := by
  filter_upwards [ae_tsum_succ_mul_gmcLimit_eAdicAnnulus_lt_top hG hγ hγ2 hρρ₂ hρ₂ le_rfl,
    ae_gmcLimit_singleton_gff hG hγ hγ2 hρρ₂ hρ₂, ae_gmcGreenMeasure_lt_top_gff hG hγ hγ2 hρρ₂ hρ₂]
    with ω' hS h1 h2
  set ψ := clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' with hψ
  have hAn : ∀ n : ℕ, gmcGreenMeasure γ ρ ρ₂ z 0 r ψ (eAdicAnnulus 0 n) ≤
      poleDensityConst r * (ENNReal.ofReal ((n : ℝ) + 1) * gmcLimit γ ρ ρ₂ ψ (eAdicAnnulus 0 n)) := by
    intro n
    rw [gmcGreenMeasure, withDensity_apply _ (measurableSet_eAdicAnnulus 0 n), ← mul_assoc,
      ← setLIntegral_const]
    exact setLIntegral_mono' (measurableSet_eAdicAnnulus 0 n) fun x hx =>
      greenOccupationDensity_le_of_mem_eAdicAnnulus h0 hx
  have hm0 : gmcGreenMeasure γ ρ ρ₂ z 0 r ψ {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (h1 0)
  have hcov : closedBall (0 : ℂ) (1 / 2) ⊆ {0} ∪ ⋃ n : ℕ, eAdicAnnulus 0 n := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · rw [mem_closedBall, dist_zero_right] at hx
      exact Or.inr (mem_iUnion.2 ⟨_, mem_eAdicAnnulus_floor hx0 hx⟩)
  have hnear : gmcGreenMeasure γ ρ ρ₂ z 0 r ψ (closedBall 0 (1 / 2)) < ∞ := by
    refine (measure_mono hcov).trans_lt ((measure_union_le _ _).trans_lt ?_)
    rw [hm0, zero_add]
    refine ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hAn)).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (poleDensityConst_lt_top r) hS
  have hK : IsCompact (closedBall z r \ ball (0 : ℂ) (1 / 2)) := (isCompact_closedBall z r).diff isOpen_ball
  have h0K : (0 : ℂ) ∉ closedBall z r \ ball (0 : ℂ) (1 / 2) := fun h => h.2 (mem_ball_self (by norm_num))
  have hsub : ball z r ⊆ (closedBall z r \ ball (0 : ℂ) (1 / 2)) ∪ closedBall 0 (1 / 2) := by
    intro x hx
    by_cases hx0 : x ∈ ball (0 : ℂ) (1 / 2)
    · exact Or.inr (ball_subset_closedBall hx0)
    · exact Or.inl ⟨ball_subset_closedBall hx, hx0⟩
  exact (measure_mono hsub).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h2 z 0 r h0 _ hK h0K, hnear⟩))

end MatedCRT.KilledOccupation
