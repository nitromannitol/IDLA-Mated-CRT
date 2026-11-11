import Mathlib
import HarmonicBalls.Defs.Brownian
import MatedCRT.Proofs.Sec3.KilledOccupation.Potential
import MatedCRT.Proofs.Sec3.KilledOccupation.OriginTails
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentificationConcrete

/-!
# The removed `φ`-part is small in probability (Appendix B, printed tex:386-400, input `hR` of S6)

Source: `paper/appendix-occupation-C16.tex`, proof of thm:occ-main, lines 386-400: with
`R_{ε,a} = ∫_0^σ 1{|B_u| < 2a} ε^{γ²/2} e^{γ h_ε(B_u)} du`, the conditional mean
`E[R_{ε,a} | g] = U_{ε,a} = 2 ∫_{D ∩ B_{2a}} G_D(y,x) μ_ε(dx)` (ordinary Brownian occupation, S0), the Green bound
`G_D(y,x) ≤ K (1 + log(1/|x|))` near `0`, the origin tail moment `E[(∫_{B_s} (1+log(1/|x|)) μ_ε)^p] ≤ C s^κ (1+log(1/s))^p`
(`origin_tail_moment`, `OriginTails.lean`), and the conditional Markov inequality `P(R > η | g) ≤ min{1, U/η} ≤ (U/η)^p`.

Inputs (explicit hypotheses): `BrownianOccupationOnBall z r` (S0 in lintegral form, the ENNReal form of
`KilledBrownianOccupationOnBall`, `Potential.lean:275`), `GreenDiskFormula z r` (`Potential.lean:34`),
the GFF hypotheses of `origin_tail_moment`, and the measurability inputs `hreg`, `hRm` (implicit in the paper).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.KilledOccupation

/-- The exit time `σ` of the disk `ball z r` for a continuous path, as a nonnegative real (tex:37). -/
def exitNN (z : ℂ) (r : ℝ) (b : ContinuousPath ℂ) : ℝ≥0 :=
  (HarmonicBalls.pathExitTime (ball z r) ⇑b).toNNReal

/-- **Step S0** in lintegral form (tex:48-52): the ordinary Brownian occupation identity for standard planar
Brownian motion killed on exiting `D = ball z r`: for `y ∈ D` and every measurable `f ≥ 0`,
`E_y ∫_0^σ f(B_t) dt = 2 ∫_D G_D(y,x) f(x) dx` (generator `½Δ`, Green function `ΔG = -δ`). This is the
nonnegative-integrand form of `KilledBrownianOccupationOnBall` (`Potential.lean:275`, bounded `f`); the passage
from bounded to nonnegative integrands is not written here and is an explicit hypothesis. -/
def BrownianOccupationOnBall (z : ℂ) (r : ℝ) : Prop :=
  ∀ y ∈ ball z r, ∀ f : ℂ → ℝ≥0∞, Measurable f →
    ∫⁻ b, (∫⁻ u in Icc 0 (exitNN z r b), f (b u) ∂timeLeb) ∂(HarmonicBalls.planarBrownianMotion y) =
      2 * ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) * f x

lemma log_one_div_norm_nonneg {x : ℂ} (hx : ‖x‖ ≤ 1) : 0 ≤ Real.log (1 / ‖x‖) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h, div_zero, Real.log_zero]
  · exact Real.log_nonneg ((one_le_div h).2 hx)

/-- **Green bound near the pole-free origin** (tex:395-396, `G_D(y,x) ≤ C_D (1 + log (1/|x|))` for `x` near `0`):
for `y ∈ D = ball z r` there are `K ≥ 0` and `ρ > 0` with `G_D(y,x) ≤ K (1 + log (1/|x|))` for `x ∈ D`, `x ≠ y`,
`|x| < ρ`. Proof from `greenFunction_disk_le_log` (`Potential.lean:47`). -/
lemma greenFunction_origin_bound {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r)
    {y : ℂ} (hy : y ∈ ball z r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ ball z r, x ≠ y → ‖x‖ < ρ →
      HarmonicBalls.greenFunction (ball z r) y x ≤ K * (1 + Real.log (1 / ‖x‖)) := by
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  by_cases hy0 : y = 0
  · refine ⟨3, by norm_num, 1, one_pos, fun x hx hxy hxn => ?_⟩
    subst hy0
    have hG0 := greenFunction_disk_le_log hr hr2 hG hy hx (Ne.symm hxy)
    have hx1 : ‖x‖ ≤ 1 := hxn.le
    have hL := log_one_div_norm_nonneg hx1
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hxy
    have hlog : Real.log (4 / ‖(0 : ℂ) - x‖) = Real.log 4 + Real.log (1 / ‖x‖) := by
      rw [zero_sub, norm_neg, ← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    have hpos : 0 ≤ Real.log 4 + Real.log (1 / ‖x‖) := by
      have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      linarith
    rw [hlog] at hG0
    calc HarmonicBalls.greenFunction (ball z r) 0 x
        ≤ (2 * Real.pi)⁻¹ * (Real.log 4 + Real.log (1 / ‖x‖)) := hG0
      _ ≤ Real.log 4 + Real.log (1 / ‖x‖) := mul_le_of_le_one_left hpos hpi
      _ ≤ 3 * (1 + Real.log (1 / ‖x‖)) := by linarith
  · have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy0
    refine ⟨3 + |Real.log (8 / ‖y‖)|, by positivity, min 1 (‖y‖ / 2), lt_min one_pos (by positivity),
      fun x hx hxy hxn => ?_⟩
    have hx1 : ‖x‖ ≤ 1 := le_trans hxn.le (min_le_left _ _)
    have hxy' : ‖x‖ < ‖y‖ / 2 := lt_of_lt_of_le hxn (min_le_right _ _)
    have hyx : ‖y‖ / 2 ≤ ‖y - x‖ := by
      have := norm_sub_norm_le y x
      linarith
    have hpos : 0 < ‖y - x‖ := lt_of_lt_of_le (by positivity) hyx
    have hG0 := greenFunction_disk_le_log hr hr2 hG hy hx (Ne.symm hxy)
    have hle : Real.log (4 / ‖y - x‖) ≤ Real.log (8 / ‖y‖) :=
      Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hpos hy']; linarith)
    have hL := log_one_div_norm_nonneg hx1
    have hK : 0 ≤ 3 + |Real.log (8 / ‖y‖)| := by positivity
    calc HarmonicBalls.greenFunction (ball z r) y x
        ≤ (2 * Real.pi)⁻¹ * Real.log (4 / ‖y - x‖) := hG0
      _ ≤ (2 * Real.pi)⁻¹ * max (Real.log (4 / ‖y - x‖)) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ max (Real.log (4 / ‖y - x‖)) 0 := mul_le_of_le_one_left (le_max_right _ _) hpi
      _ ≤ max (Real.log (8 / ‖y‖)) 0 := max_le_max hle le_rfl
      _ ≤ |Real.log (8 / ‖y‖)| := max_le (le_abs_self _) (abs_nonneg _)
      _ ≤ (3 + |Real.log (8 / ‖y‖)|) * (1 + Real.log (1 / ‖x‖)) := by
          nlinarith [abs_nonneg (Real.log (8 / ‖y‖))]

/-- Pointwise domination of the Green weight on `B_{2a}` by the origin mass (tex:395-400): for `2a ≤ ρ`,
`∫_D G_D(y,·) 1_{B_{2a}} μ_ε ≤ K ∫_{B_{2a}} (1 + log(1/|x|)) μ_ε = K · weightedMass(B_{2a})`. -/
lemma lintegral_green_le_weightedMass {γ ε : ℝ} (hc : ℝ → ℂ → ℝ) {z : ℂ} {r : ℝ} {y : ℂ} {K ρ a : ℝ}
    (hK : 0 ≤ K) (hsa : 2 * a ≤ ρ) (h1 : 2 * a ≤ 1)
    (hG : ∀ x ∈ ball z r, x ≠ y → ‖x‖ < ρ →
      HarmonicBalls.greenFunction (ball z r) y x ≤ K * (1 + Real.log (1 / ‖x‖))) :
    ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) *
        (if ‖x‖ < 2 * a then regDensity γ ε hc x else 0)
      ≤ ENNReal.ofReal K * weightedMass γ ε hc (ball 0 (2 * a)) := by
  set G' : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal K * (ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) *
    regDensity γ ε hc x) with hG'
  have hae : ∀ᵐ x ∂(volume.restrict (ball z r)), x ≠ y :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton y))
  have hpt : ∀ᵐ x ∂(volume.restrict (ball z r)),
      ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) *
          (if ‖x‖ < 2 * a then regDensity γ ε hc x else 0)
        ≤ (ball (0 : ℂ) (2 * a)).indicator G' x := by
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with x hxy hxD
    by_cases hx : ‖x‖ < 2 * a
    · have hmem : x ∈ ball (0 : ℂ) (2 * a) := mem_ball_zero_iff.2 hx
      have hxval : (if ‖x‖ < 2 * a then regDensity γ ε hc x else 0) = regDensity γ ε hc x := by
        simp [hx]
      rw [hxval, indicator_of_mem hmem, hG']
      have hL : 0 ≤ 1 + Real.log (1 / ‖x‖) := by
        have := log_one_div_norm_nonneg (show ‖x‖ ≤ 1 by linarith)
        linarith
      have hgr : ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) ≤
          ENNReal.ofReal K * ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) := by
        rw [← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (hG x hxD hxy (by linarith))
      calc _ ≤ (ENNReal.ofReal K * ENNReal.ofReal (1 + Real.log (1 / ‖x‖))) * regDensity γ ε hc x := by
            gcongr
        _ = _ := by ring
    · have hxval : (if ‖x‖ < 2 * a then regDensity γ ε hc x else 0) = 0 := by
        simp [hx]
      rw [hxval, mul_zero]
      exact zero_le
  calc ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) y x) *
          (if ‖x‖ < 2 * a then regDensity γ ε hc x else 0)
      ≤ ∫⁻ x in ball z r, (ball (0 : ℂ) (2 * a)).indicator G' x := lintegral_mono_ae hpt
    _ ≤ ∫⁻ x, (ball (0 : ℂ) (2 * a)).indicator G' x := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x in ball (0 : ℂ) (2 * a), G' x := lintegral_indicator measurableSet_ball _
    _ = ENNReal.ofReal K * weightedMass γ ε hc (ball 0 (2 * a)) := by
        unfold weightedMass
        rw [hG', lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `t^κ (1 + log (1/t))^p → 0` as `t ↓ 0` (for `κ, p > 0`; the limit used for the bound in `a`). -/
lemma tendsto_rpow_mul_log_rpow {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) :
    Tendsto (fun t : ℝ => t ^ κ * (1 + Real.log (1 / t)) ^ p) (𝓝[>] 0) (𝓝 0) := by
  have hq0 : 0 < κ / p := div_pos hκ hp
  have h1 : Tendsto (fun t : ℝ => t ^ (κ / p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => t ^ (κ / p)) (𝓝 0) (𝓝 (0 ^ (κ / p))) :=
      (Real.continuousAt_rpow_const 0 (κ / p) (Or.inr hq0.le)).tendsto
    rw [Real.zero_rpow hq0.ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ => Real.log t * t ^ (κ / p)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero hq0
  have h3 : Tendsto (fun t : ℝ => (1 + Real.log (1 / t)) * t ^ (κ / p)) (𝓝[>] 0) (𝓝 0) := by
    have hfun : (fun t : ℝ => (1 + Real.log (1 / t)) * t ^ (κ / p)) =
        fun t : ℝ => t ^ (κ / p) - Real.log t * t ^ (κ / p) := by
      funext t
      rw [one_div, Real.log_inv]
      ring
    rw [hfun]
    simpa using h1.sub h2
  have h4 : Tendsto (fun t : ℝ => ((1 + Real.log (1 / t)) * t ^ (κ / p)) ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := h3.rpow_const (Or.inr hp.le)
    rw [Real.zero_rpow hp.ne'] at this
    exact this
  refine h4.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have ht0 : 0 < t := ht.1
  have hL : 0 ≤ 1 + Real.log (1 / t) := by
    have := Real.log_nonneg (show 1 ≤ 1 / t from one_le_one_div ht.1 ht.2.le)
    linarith
  rw [Real.mul_rpow hL (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le, div_mul_cancel₀ κ hp.ne',
    mul_comm]

/-- Elementary: `x ≤ 1`, `η x ≤ M` and `0 < p ≤ 1` give `x ≤ (M/η)^p` (`min{1, M/η} ≤ (M/η)^p`). -/
lemma prob_le_rpow_of_mul_le {x M η : ℝ≥0∞} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hη : η ≠ 0)
    (hηt : η ≠ ⊤) (hx1 : x ≤ 1) (h : η * x ≤ M) : x ≤ (M / η) ^ p := by
  have hx : x ≤ M / η := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hη) (Or.inl hηt), mul_comm]
    exact h
  by_cases hq : M / η ≤ 1
  · calc x ≤ M / η := hx
      _ = (M / η) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ (M / η) ^ p := ENNReal.rpow_le_rpow_of_exponent_ge hq hp1
  · calc x ≤ 1 := hx1
      _ ≤ (M / η) ^ p := ENNReal.one_le_rpow (not_le.1 hq).le hp0

/-- **Conditional Markov bound for the removed part** (tex:391-395): for fixed `ε, a` with `2a ≤ min(ρ, 1)`,
`P ⊗ P_y(R_{ε,a} > η) ≤ (2 ofReal K / ofReal η)^p ∫ W_{2a}(ω)^p dP`, where `W_s(ω) = weightedMass γ ε (hc ω) (B_s)`.
The inner expectation is S0 (`BrownianOccupationOnBall`) and the Green bound (`greenFunction_origin_bound`). -/
lemma removed_tail_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ : ℝ} (hc : Ω → ℝ → ℂ → ℝ) {z : ℂ} {r : ℝ} {y : ℂ}
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)]
    (hS0 : BrownianOccupationOnBall z r) {K ρ : ℝ} (hK : 0 ≤ K)
    (hG : ∀ x ∈ ball z r, x ≠ y → ‖x‖ < ρ →
      HarmonicBalls.greenFunction (ball z r) y x ≤ K * (1 + Real.log (1 / ‖x‖)))
    {ε a p η : ℝ} (h2a : 2 * a ≤ ρ) (h1 : 2 * a ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hη : 0 < η) (hreg : ∀ ω, Measurable (regDensity γ ε (hc ω)))
    (hRm : Measurable (clockDistR γ hc (exitNN z r) ε a))
    (hy : y ∈ ball z r) :
    (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a x} ≤
      (2 * ENNReal.ofReal K / ENNReal.ofReal η) ^ p *
        ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P := by
  set c : ℝ≥0∞ := 2 * ENNReal.ofReal K / ENNReal.ofReal η with hc_def
  have hηne : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.2 hη).ne'
  have hηt : ENNReal.ofReal η ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcfin : c ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    hηne
  -- per-ω bound
  have hslice : ∀ ω, HarmonicBalls.planarBrownianMotion y
      {b | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)} ≤
        (c * weightedMass γ ε (hc ω) (ball 0 (2 * a))) ^ p := by
    intro ω
    have hmeasR : Measurable fun b : ContinuousPath ℂ => clockDistR γ hc (exitNN z r) ε a (ω, b) :=
      hRm.comp measurable_prodMk_left
    have hMarkov := mul_meas_ge_le_lintegral (μ := HarmonicBalls.planarBrownianMotion y) hmeasR (ENNReal.ofReal η)
    have hint : ∫⁻ b, clockDistR γ hc (exitNN z r) ε a (ω, b) ∂(HarmonicBalls.planarBrownianMotion y) ≤
        2 * (ENNReal.ofReal K * weightedMass γ ε (hc ω) (ball 0 (2 * a))) := by
      have hf : Measurable fun x : ℂ => if ‖x‖ < 2 * a then regDensity γ ε (hc ω) x else 0 :=
        Measurable.ite (measurableSet_lt measurable_norm measurable_const) (hreg ω) measurable_const
      have hS := hS0 y hy _ hf
      have heq : ∫⁻ b, clockDistR γ hc (exitNN z r) ε a (ω, b) ∂(HarmonicBalls.planarBrownianMotion y) =
          ∫⁻ b, (∫⁻ u in Icc 0 (exitNN z r b),
            (fun x : ℂ => if ‖x‖ < 2 * a then regDensity γ ε (hc ω) x else 0) (b u) ∂timeLeb)
            ∂(HarmonicBalls.planarBrownianMotion y) := rfl
      rw [heq, hS]
      gcongr
      exact lintegral_green_le_weightedMass (hc ω) hK h2a h1 hG
    have hmul : ENNReal.ofReal η * HarmonicBalls.planarBrownianMotion y
        {b | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)} ≤
        2 * (ENNReal.ofReal K * weightedMass γ ε (hc ω) (ball 0 (2 * a))) := by
      have hsub : HarmonicBalls.planarBrownianMotion y
          {b | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)} ≤
          HarmonicBalls.planarBrownianMotion y
          {b | ENNReal.ofReal η ≤ clockDistR γ hc (exitNN z r) ε a (ω, b)} :=
        measure_mono fun b (hb : ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)) => le_of_lt hb
      calc ENNReal.ofReal η * HarmonicBalls.planarBrownianMotion y
            {b | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)}
          ≤ ENNReal.ofReal η * HarmonicBalls.planarBrownianMotion y
            {b | ENNReal.ofReal η ≤ clockDistR γ hc (exitNN z r) ε a (ω, b)} := by gcongr
        _ ≤ _ := hMarkov
        _ ≤ _ := hint
    have hM : (2 * (ENNReal.ofReal K * weightedMass γ ε (hc ω) (ball 0 (2 * a)))) /
        ENNReal.ofReal η = c * weightedMass γ ε (hc ω) (ball 0 (2 * a)) := by
      rw [hc_def, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ring
    have := prob_le_rpow_of_mul_le (x := HarmonicBalls.planarBrownianMotion y
        {b | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)}) hp0 hp1 hηne hηt
      (prob_le_one) hmul
    rwa [hM] at this
  have hSet : MeasurableSet {x : Ω × ContinuousPath ℂ |
      ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a x} :=
    measurableSet_lt measurable_const hRm
  rw [Measure.prod_apply hSet]
  calc ∫⁻ ω, HarmonicBalls.planarBrownianMotion y
        {b | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a (ω, b)} ∂P
      ≤ ∫⁻ ω, c ^ p * weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P := by
        refine lintegral_mono fun ω => (hslice ω).trans ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    _ = c ^ p * ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le hcfin)

/-- **hR, derived** (printed tex:386-400): for fixed `y ∈ D = ball z r` the removed `φ`-part `R_{ε,a}` is small in
probability, uniformly in small `ε`, as `a → 0`. Inputs: `origin_tail_moment` (proved from the GFF structure `hGFF`),
S0 (`hS0`), the Green bound (from `GreenDiskFormula`), and the measurability `hRm`. -/
theorem removed_tail_small {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    (hc : Ω → ℝ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r) {y : ℂ} (hy : y ∈ ball z r)
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)] (hS0 : BrownianOccupationOnBall z r)
    (hreg : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (hc ω)))
    (hRm : ∀ ε a : ℝ, Measurable (clockDistR γ hc (exitNN z r) ε a)) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a x} ≤ δ := by
  intro η hη δ hδ
  obtain ⟨K, hK, ρ, hρ, hG'⟩ := greenFunction_origin_bound hr hr2 hG hy
  have hp1' : p < 4 / γ ^ 2 - 1 := lt_of_lt_of_le hp1 (min_le_right _ _)
  have hp1le : p ≤ 1 := (hp1.trans_le (min_le_left _ _)).le
  have hκpos : 0 < κ := by
    have h5 : p + 1 < 4 / γ ^ 2 := by linarith
    have h6 : (p + 1) * γ ^ 2 < 4 := (lt_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)).1 h5
    have hfac : κ = p / 2 * (4 - γ ^ 2 * (p + 1)) := by rw [hκ]; ring
    rw [hfac]
    have : 0 < 4 - γ ^ 2 * (p + 1) := by linarith
    exact mul_pos (by linarith) this
  obtain ⟨C, a₀, ha₀, hT⟩ := origin_tail_moment P hC hc hGFF hγ0 hγ2 hp0 hp1 hκ
  set c : ℝ≥0∞ := 2 * ENNReal.ofReal K / ENNReal.ofReal η with hc_def
  have hηne : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.2 hη).ne'
  have hcfin : c ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hηne
  have hcpne : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le hcfin
  -- the deterministic bound in `a`
  have h2a : Tendsto (fun a : ℝ => 2 * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun a ha => ?_⟩
    · have h0 : Tendsto (fun a : ℝ => 2 * a) (𝓝 0) (𝓝 0) :=
        (by fun_prop : Continuous fun a : ℝ => 2 * a).tendsto' 0 0 (by simp)
      exact h0.mono_left nhdsWithin_le_nhds
    · exact mul_pos two_pos (mem_Ioi.1 ha)
  have hlim2 : Tendsto (fun a : ℝ => C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((tendsto_rpow_mul_log_rpow hκpos hp0).comp h2a).const_mul C
    rw [mul_zero] at this
    exact this
  have hlim3 : Tendsto (fun a : ℝ => ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hlim2
    rw [ENNReal.ofReal_zero] at this
    exact this
  have hB : Tendsto (fun a : ℝ => c ^ p * ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hlim3 (Or.inr hcpne)
    rw [mul_zero] at this
    exact this
  have hsmall := hB.eventually (gt_mem_nhds hδ)
  have hA : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioo 0 (min (a₀ / 2) (min (ρ / 2) (1 / 2))) :=
    Ioo_mem_nhdsGT (lt_min (by linarith) (lt_min (by linarith) (by norm_num)))
  filter_upwards [hsmall, hA] with a hsa hAa
  obtain ⟨ha0, haL⟩ := hAa
  have h2a0 : 2 * a < a₀ := by
    have := lt_of_lt_of_le haL (min_le_left _ _)
    linarith
  have h2ρ : 2 * a ≤ ρ := by
    have := lt_of_lt_of_le haL (min_le_right _ _ |>.trans (min_le_left _ _))
    linarith
  have h21 : 2 * a ≤ 1 := by
    have := lt_of_lt_of_le haL (min_le_right _ _ |>.trans (min_le_right _ _))
    linarith
  filter_upwards [Ioo_mem_nhdsGT ha₀] with ε hε
  have hbound := removed_tail_bound P hc hS0 hK hG' h2ρ h21 hp0 hp1le hη (fun ω => hreg ω ε hε.1)
    (hRm ε a) hy (γ := γ) (ε := ε) (a := a) (p := p) (η := η)
  have hW : ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P ≤
      ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)) := by
    have := hT (2 * a) ⟨by linarith, h2a0⟩ ε hε
    rwa [mul_assoc] at this
  calc (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistR γ hc (exitNN z r) ε a x}
      ≤ c ^ p * ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 (2 * a)) ^ p ∂P := hbound
    _ ≤ c ^ p * ENNReal.ofReal (C * ((2 * a) ^ κ * (1 + Real.log (1 / (2 * a))) ^ p)) := by
        gcongr
    _ ≤ δ := hsa.le

/-- **Identification of the clock from the GFF data** (tex:370-414): `regClock_identification` with its hypothesis
`hR` derived by `removed_tail_small`. -/
theorem regClock_identification_of_GFF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {p κ : ℝ} (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    (hc : Ω → ℝ → ℂ → ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r) {y : ℂ} (hy : y ∈ ball z r)
    [IsProbabilityMeasure (HarmonicBalls.planarBrownianMotion y)] (hS0 : BrownianOccupationOnBall z r)
    (hreg : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (regDensity γ ε (hc ω)))
    (hνm : ∀ ω, ∀ ε : ℝ, 0 < ε → Measurable (nuDensity γ ε (hc ω)))
    (hRm : ∀ ε a : ℝ, Measurable (clockDistR γ hc (exitNN z r) ε a))
    (hQm : ∀ a : ℝ, Measurable (clockDistQ γ dA (exitNN z r) a))
    (hfin : ∀ᵐ x ∂(P.prod (HarmonicBalls.planarBrownianMotion y)),
      weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (exitNN z r x.2) (exitNN z r x.2) ≠ ⊤)
    (hE : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistE γ hc dA (exitNN z r) ε a x}) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => (P.prod (HarmonicBalls.planarBrownianMotion y))
        {x | ENNReal.ofReal η < clockDistD γ hc dA (exitNN z r) ε x}) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  regClock_identification P (HarmonicBalls.planarBrownianMotion y) hγ0.ne' hc dA (exitNN z r) hreg hνm hQm
    hfin hE (removed_tail_small P hγ0 hγ2 hp0 hp1 hκ hc hC hGFF hr hr2 hG hy hS0 hreg hRm)

end MatedCRT.KilledOccupation
