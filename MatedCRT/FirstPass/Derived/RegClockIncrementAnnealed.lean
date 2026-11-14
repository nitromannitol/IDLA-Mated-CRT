import MatedCRT.FirstPass.Derived.RegClockIncrementPath
import MatedCRT.FirstPass.Derived.RegClockIntegralMeasurable
import MatedCRT.FirstPass.Derived.BrownianExitTimeTail
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders

/-!
# The dyadic increment of the regularized clock, averaged over the Brownian path

For a planar Brownian motion `b` started at `y` and killed on exiting `B_r(z) ⊆ B_ρ(0)`, and an independent
whole-plane GFF, the `L¹` norm of the dyadic increment `T_{ε/2} - T_ε` of the regularized clock integrals of a
continuous weight `g ≥ 0` (vanishing on `B_ε(0)` and outside `B_r(z)`) is bounded by the dyadic increment rate
evaluated at the mean near-diagonal mass and the mean total mass of the occupation measure. Path by path this is
`lintegral_abs_regClock_dyadic_increment_le`; the rate is affine in both masses with nonnegative coefficients,
the near-diagonal mass of the bounded singular weight is at most `M²` times the occupation pair mass
`|{(u, v) ∈ [0, σ]² : |b_u - b_v| < 2ε}|`, the total mass at most `M σ`, and the expected exit time is finite.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- `dyadicIncrementRate` is affine in the near-diagonal mass and the total mass, with nonnegative coefficients and
constant term `ε^{γ²/2} t / 2`. -/
lemma exists_dyadicIncrementRate_eq_affine (γ α : ℝ) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ I A : ℝ,
      dyadicIncrementRate γ α ε t I A = ε ^ (γ ^ 2 / 2) * t / 2 + c₁ * I + c₂ * A := by
  have hX : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 := by
    have : 0 ≤ γ ^ 2 * Real.log 2 := mul_nonneg (sq_nonneg γ) (Real.log_nonneg one_le_two)
    linarith [Real.add_one_le_exp (γ ^ 2 * Real.log 2)]
  have hε' : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε.le _
  refine ⟨ε ^ (γ ^ 2 / 2) * ((Real.exp (γ ^ 2 * Real.log 2) - 1) *
      Real.exp (Real.log (1 / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2))) / (2 * t),
    2 * ε ^ (γ ^ 2 / 2) * Real.exp (Real.log (1 / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)),
    div_nonneg (mul_nonneg hε' (mul_nonneg hX (Real.exp_pos _).le)) (by positivity),
    mul_nonneg (mul_nonneg zero_le_two hε') (Real.exp_pos _).le, fun I A => ?_⟩
  unfold dyadicIncrementRate
  field_simp
  ring

/-- The restriction of `lebNN` to `[0, s]` is a finite measure. -/
lemma isFiniteMeasure_lebNN_restrict_Icc (s : ℝ≥0) : IsFiniteMeasure (lebNN.restrict (Icc 0 s)) :=
  ⟨by rw [Measure.restrict_apply_univ, lebNN_Icc]; exact ENNReal.coe_lt_top⟩

/-- **Near-diagonal mass of a bounded weight under the occupation measure.** If `|w| ≤ M`, the mass of
`|w| ⊗ |w|` on `{|x - x'| < a}` under `ν_b ⊗ ν_b`, `ν_b = (du|_{[0,s]}) ∘ b⁻¹`, is at most `M²` times the
occupation pair mass `|{(u, v) ∈ [0, s]² : |b_u - b_v| < a}|`. -/
lemma integral_indicator_occupation_prod_le (b : ContinuousPath ℂ) (s : ℝ≥0) {w : ℂ → ℝ} {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) (a : ℝ) :
    ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < a}.indicator (fun p => |w p.1| * |w p.2|) p
        ∂(((lebNN.restrict (Icc 0 s)).map fun u => b u).prod
          ((lebNN.restrict (Icc 0 s)).map fun u => b u)) ≤
      M ^ 2 * (((lebNN.restrict (Icc 0 s)).prod (lebNN.restrict (Icc 0 s)))
        {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < a}).toReal := by
  have hμf := isFiniteMeasure_lebNN_restrict_Icc s
  have hνf := isFiniteMeasure_occupation s b
  have hbm : Measurable fun u : ℝ≥0 => b u := (map_continuous b).measurable
  have hS : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < a} :=
    (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)) continuous_const).measurableSet
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc _ ≤ ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < a}.indicator (fun _ => M ^ 2) p
        ∂(((lebNN.restrict (Icc 0 s)).map fun u => b u).prod
          ((lebNN.restrict (Icc 0 s)).map fun u => b u)) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun p => ?_) ((integrable_const _).indicator hS)
          (ae_of_all _ fun p => ?_)
        · exact Set.indicator_nonneg (fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) p
        · refine Set.indicator_le_indicator ?_
          rw [sq]
          exact mul_le_mul (hM _) (hM _) (abs_nonneg _) hM0
    _ = _ := by
        rw [integral_indicator_const _ hS, Measure.map_prod_map _ _ hbm hbm, measureReal_def,
          Measure.map_apply (hbm.prodMap hbm) hS, smul_eq_mul]
        exact mul_comm _ _

/-- **Total mass of a bounded weight under the occupation measure.** If `|w| ≤ M`, then
`∫ |w| dν_b ≤ M s` for the occupation measure `ν_b` of `b` on `[0, s]`. -/
lemma integral_abs_occupation_le (b : ContinuousPath ℂ) (s : ℝ≥0) {w : ℂ → ℝ} {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) :
    ∫ x, |w x| ∂((lebNN.restrict (Icc 0 s)).map fun u => b u) ≤ M * s := by
  have hνf := isFiniteMeasure_occupation s b
  have hbm : Measurable fun u : ℝ≥0 => b u := (map_continuous b).measurable
  calc _ ≤ ∫ _x, M ∂((lebNN.restrict (Icc 0 s)).map fun u => b u) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const M) (ae_of_all _ hM)
    _ = M * s := by
        rw [integral_const, smul_eq_mul, measureReal_def, Measure.map_apply hbm MeasurableSet.univ,
          preimage_univ, Measure.restrict_apply_univ, lebNN_Icc, ENNReal.coe_toReal, mul_comm]

/-- The expected exit time of planar Brownian motion from a ball is finite. -/
lemma lintegral_exitNN_ne_top (y z : ℂ) (r : ℝ) :
    ∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤ :=
  ne_top_of_le_ne_top (lintegral_pathExitTime_planar_ne_top y z r)
    (lintegral_mono fun _ => ENNReal.coe_toNNReal_le_self)

/-- **`L¹` bound for the dyadic increment of the regularized clock, averaged over the Brownian path.** Let `b` be a
planar Brownian motion from `y`, killed at the exit time `σ` of `B_r(z) ⊆ B_ρ(0)`, independent of a whole-plane GFF,
and let `g ≥ 0` be continuous, vanishing on `B_ε(0)` and outside `B_r(z)`, `0 < ε < 1 - ρ`, with singular weight
`|g(x) |x|^{-γ²}| ≤ M`. If the mean occupation pair mass at distance `2ε` is at most `C (2ε)^{2(1-θ)}`, then
`E |T_{ε/2} - T_ε| ≤ dyadicIncrementRate γ α ε t (M² C (2ε)^{2(1-θ)}) (M E σ)` for `γ ≤ α ≤ 2γ`, `t > 0`. -/
theorem lintegral_prod_abs_regClock_dyadic_increment_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc) (γ : ℝ) {ρ r ε : ℝ} {z : ℂ} (y : ℂ)
    (hball : ball z r ⊆ ball 0 ρ) (hε : 0 < ε) (hερ : ε < 1 - ρ)
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖)
    (hgr : ∀ x, g x ≠ 0 → x ∈ ball z r) {M : ℝ} (hM : ∀ x, |singularWeight γ g x| ≤ M)
    {α t : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) (ht : 0 < t) {C θ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∫⁻ b, ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
          {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * ε} ∂planarBrownianMotion y ≤
        ENNReal.ofReal (C * (2 * ε) ^ (2 * (1 - θ)))) :
    ∫⁻ p : Ω' × ContinuousPath ℂ, ENNReal.ofReal
        |(∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (ε / 2) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal -
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal| ∂(P'.prod (planarBrownianMotion y)) ≤
      ENNReal.ofReal (dyadicIncrementRate γ α ε t (M ^ 2 * (C * (2 * ε) ^ (2 * (1 - θ))))
        (M * (∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y).toReal)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK : 0 ≤ C * (2 * ε) ^ (2 * (1 - θ)) := mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
  have hne := lintegral_exitNN_ne_top y z r
  obtain ⟨c₁, c₂, hc₁, hc₂, hrate⟩ := exists_dyadicIncrementRate_eq_affine γ α hε ht
  have hc0 : 0 ≤ ε ^ (γ ^ 2 / 2) * t / 2 := by positivity
  set c0 := ε ^ (γ ^ 2 / 2) * t / 2 with hc0def
  have hσm : AEMeasurable (fun b : ContinuousPath ℂ => ENNReal.ofReal c₂ *
      (ENNReal.ofReal M * (exitNN z r b : ℝ≥0∞))) (planarBrownianMotion y) :=
    (((measurable_exitNN z r).coe_nnreal_ennreal.const_mul _).const_mul _).aemeasurable
  refine (lintegral_prod_symm _ ?_).trans_le ?_
  · exact (continuous_abs.measurable.comp
      ((measurable_prod_setLIntegral_regClockMeasure hwp γ (ε / 2) r z hg.measurable).ennreal_toReal.sub
        (measurable_prod_setLIntegral_regClockMeasure hwp γ ε r z hg.measurable).ennreal_toReal)).ennreal_ofReal
      |>.aemeasurable
  calc _ ≤ ∫⁻ b, (ENNReal.ofReal c0 + (ENNReal.ofReal c₁ * (ENNReal.ofReal (M ^ 2) *
            ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
              {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * ε}) +
          ENNReal.ofReal c₂ * (ENNReal.ofReal M * (exitNN z r b : ℝ≥0∞)))) ∂planarBrownianMotion y := by
        refine lintegral_mono fun b => ?_
        refine (lintegral_abs_regClock_dyadic_increment_le hwp γ hball hε hερ hg hg0 hgε hgr (exitNN z r) b
          (fun s hs => mem_ball_of_lt_exitNN hs) hγα hα ht).trans ?_
        have hI := integral_indicator_occupation_prod_le b (exitNN z r b) hM (2 * ε)
        have hA := integral_abs_occupation_le b (exitNN z r b) hM
        have hX : ENNReal.ofReal ((((lebNN.restrict (Icc 0 (exitNN z r b))).prod
            (lebNN.restrict (Icc 0 (exitNN z r b)))) {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * ε}).toReal) ≤
            ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
              {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * ε} := ENNReal.ofReal_toReal_le
        rw [hrate]
        refine (ENNReal.ofReal_le_ofReal (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hI hc₁))
          (mul_le_mul_of_nonneg_left hA hc₂))).trans ?_
        rw [ENNReal.ofReal_add (add_nonneg hc0 (mul_nonneg hc₁ (mul_nonneg (sq_nonneg M) ENNReal.toReal_nonneg)))
            (mul_nonneg hc₂ (mul_nonneg hM0 (NNReal.coe_nonneg _))),
          ENNReal.ofReal_add hc0 (mul_nonneg hc₁ (mul_nonneg (sq_nonneg M) ENNReal.toReal_nonneg)),
          ENNReal.ofReal_mul hc₁, ENNReal.ofReal_mul hc₂, ENNReal.ofReal_mul (sq_nonneg M),
          ENNReal.ofReal_mul hM0, ENNReal.ofReal_coe_nnreal, add_assoc]
        gcongr
    _ = ENNReal.ofReal c0 + (ENNReal.ofReal c₁ * (ENNReal.ofReal (M ^ 2) *
            ∫⁻ b, ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
              {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * ε} ∂planarBrownianMotion y) +
          ENNReal.ofReal c₂ * (ENNReal.ofReal M *
            ∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_add_right' _ hσm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c0 + (ENNReal.ofReal c₁ * (ENNReal.ofReal (M ^ 2) *
            ENNReal.ofReal (C * (2 * ε) ^ (2 * (1 - θ)))) +
          ENNReal.ofReal c₂ * (ENNReal.ofReal M *
            ∫⁻ b, (exitNN z r b : ℝ≥0∞) ∂planarBrownianMotion y)) := by
        gcongr
    _ = _ := by
        rw [hrate, ENNReal.ofReal_add (add_nonneg hc0 (mul_nonneg hc₁ (mul_nonneg (sq_nonneg M) hK)))
            (mul_nonneg hc₂ (mul_nonneg hM0 ENNReal.toReal_nonneg)),
          ENNReal.ofReal_add hc0 (mul_nonneg hc₁ (mul_nonneg (sq_nonneg M) hK)),
          ENNReal.ofReal_mul hc₁, ENNReal.ofReal_mul hc₂, ENNReal.ofReal_mul (sq_nonneg M),
          ENNReal.ofReal_mul hM0, ENNReal.ofReal_toReal hne, add_assoc]

end MatedCRT.KilledOccupation
