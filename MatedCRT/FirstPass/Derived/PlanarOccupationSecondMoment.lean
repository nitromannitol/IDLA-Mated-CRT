import MatedCRT.FirstPass.Derived.LQGApproxClockRevuz
import MatedCRT.FirstPass.Derived.RevuzWeightedStart
import MatedCRT.FirstPass.Derived.LBMApproxRestart
import MatedCRT.FirstPass.Derived.RevuzTimeChangeSemigroup

/-!
# Second moment of the occupation integral of planar Brownian motion over a unit window

For a measurable `g : ℂ → [0, ∞]`, let `I(b) = ∫_{(0,1]} g(b_s) ds` (`windowOcc g b`).  If `g` vanishes outside the
closed disc `B̄(0, n)` and the Green potential `J(y) = E_y I = ∫_{(0,1]} ∫ g d p_r(y, ·) dr` is bounded by `U` on
`B̄(0, n)`, then `E_z[I²] ≤ 2 U E_z[I]` for every start `z` (Khas'minskii-type second moment bound):

* `sq_setLIntegral_Ioc_le`: pathwise, `(∫_{(0,1]} φ)² ≤ 2 ∫_{(0,1]} φ(s) ∫_{(0,1] ∩ [s, ∞)} φ(t) dt ds`;
* `lintegral_eval_mul_shift`: the simple Markov property at a fixed time for a position-weighted functional;
* `lintegral_windowOcc_sq_le`: the bound `E_z[I²] ≤ 2 (U E_z[I])`.
-/

open MeasureTheory MarkovProcess Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The occupation integral of `g` along the path `b` over the time window `(0, 1]`. -/
noncomputable def windowOcc (g : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) 1, g (b s.toNNReal)

/-- **Pathwise symmetrization**: the square of a window integral is at most twice the integral over ordered
pairs of times. -/
theorem sq_setLIntegral_Ioc_le {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ s in Ioc (0 : ℝ) 1, φ s) ^ 2 ≤
      2 * ∫⁻ s in Ioc (0 : ℝ) 1, φ s * ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t := by
  set Q1 : ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun p => φ p.1 * φ p.2 with hQ1
  set Q2 : ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => φ p.1 * φ p.2 with hQ2
  have hΦ : Measurable fun p : ℝ × ℝ => φ p.1 * φ p.2 :=
    (hφ.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hS1 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  have hS2 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hQ1m : Measurable Q1 := hΦ.indicator hS1
  have hQ2m : Measurable Q2 := hΦ.indicator hS2
  have hsq : (∫⁻ s in Ioc (0 : ℝ) 1, φ s) ^ 2 =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, φ s * φ t := by
    rw [sq, ← lintegral_mul_const _ hφ]
    refine lintegral_congr fun s => ?_
    rw [lintegral_const_mul _ hφ]
  have hpt : ∀ s t : ℝ, φ s * φ t ≤ Q1 (s, t) + Q2 (s, t) := by
    intro s t
    rcases le_total t s with h | h
    · have : Q1 (s, t) = φ s * φ t := by
        rw [hQ1, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from h)]
      rw [this]
      exact le_self_add
    · have : Q2 (s, t) = φ s * φ t := by
        rw [hQ2, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} from h)]
      rw [this]
      exact le_add_self
  have hswap : ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q1 (s, t) =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t) := by
    rw [lintegral_lintegral_swap (f := fun s t => Q1 (s, t)) hQ1m.aemeasurable]
    refine lintegral_congr fun t => lintegral_congr fun s => ?_
    by_cases h : t ≤ s
    · rw [hQ1, hQ2, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from h),
        Set.indicator_of_mem (show (t, s) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} from h), mul_comm]
    · rw [hQ1, hQ2, Set.indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | p.2 ≤ p.1} from h),
        Set.indicator_of_notMem (show (t, s) ∉ {p : ℝ × ℝ | p.1 ≤ p.2} from h)]
  have hQ2eq : ∀ s : ℝ, ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t) =
      φ s * ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t := by
    intro s
    rw [← lintegral_const_mul _ (hφ.indicator measurableSet_Ici)]
    refine lintegral_congr fun t => ?_
    by_cases h : s ≤ t
    · rw [hQ2, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} from h),
        Set.indicator_of_mem (show t ∈ Ici s from h)]
    · rw [hQ2, Set.indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | p.1 ≤ p.2} from h),
        Set.indicator_of_notMem (show t ∉ Ici s from h), mul_zero]
  calc (∫⁻ s in Ioc (0 : ℝ) 1, φ s) ^ 2
      = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, φ s * φ t := hsq
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, (Q1 (s, t) + Q2 (s, t)) :=
        lintegral_mono fun s => lintegral_mono fun t => hpt s t
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, ((∫⁻ t in Ioc (0 : ℝ) 1, Q1 (s, t)) +
          ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t)) :=
        lintegral_congr fun s => lintegral_add_left (hQ1m.comp measurable_prodMk_left) _
    _ = (∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q1 (s, t)) +
          ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t) :=
        lintegral_add_left hQ1m.lintegral_prod_right' _
    _ = 2 * ∫⁻ s in Ioc (0 : ℝ) 1, φ s * ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t := by
        rw [hswap, ← two_mul]
        congr 1
        exact lintegral_congr hQ2eq

/-- **The future window is a shifted window**: for `s ≥ 0`, `∫_{(0,1]} 1_{[s, ∞)} φ ≤ ∫_{(0,1]} φ(s + r) dr`. -/
theorem setLIntegral_Ioc_indicator_Ici_le (φ : ℝ → ℝ≥0∞) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t ≤ ∫⁻ r in Ioc (0 : ℝ) 1, φ (s + r) := by
  calc ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t
      = ∫⁻ t, (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) t :=
        (lintegral_indicator measurableSet_Ioc _).symm
    _ = ∫⁻ r, (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) (s + r) :=
        (lintegral_add_left_eq_self (fun t => (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) t) s).symm
    _ ≤ ∫⁻ r, (Icc (0 : ℝ) 1).indicator (fun r => φ (s + r)) r := by
        refine lintegral_mono fun r => ?_
        by_cases h : s + r ∈ Ioc (0 : ℝ) 1 ∧ s + r ∈ Ici s
        · have hr : r ∈ Icc (0 : ℝ) 1 := ⟨by simpa using h.2, by linarith [h.1.2]⟩
          rw [Set.indicator_of_mem h.1, Set.indicator_of_mem h.2, Set.indicator_of_mem hr]
        · have h0 : (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) (s + r) = 0 := by
            by_cases h1 : s + r ∈ Ioc (0 : ℝ) 1
            · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h2 => h ⟨h1, h2⟩)]
            · rw [Set.indicator_of_notMem h1]
          rw [h0]
          exact zero_le
    _ = ∫⁻ r in Icc (0 : ℝ) 1, φ (s + r) := lintegral_indicator measurableSet_Icc _
    _ = ∫⁻ r in Ioc (0 : ℝ) 1, φ (s + r) := (setLIntegral_congr Ioc_ae_eq_Icc).symm

/-- **Simple Markov property at a fixed time, position-weighted form.** -/
theorem lintegral_eval_mul_shift {g : ℂ → ℝ≥0∞} (hg : Measurable g) {Ψ : ContinuousPath ℂ → ℝ≥0∞}
    (hΨ : Measurable Ψ) (s : ℝ≥0) (z : ℂ) :
    ∫⁻ b, g (b s) * Ψ (ContinuousPath.shift s b) ∂planarLaw z =
      ∫⁻ y, g y * ∫⁻ b, Ψ b ∂planarLaw y ∂HarmonicBalls.planarGaussian z s := by
  have hΦ : Measurable fun b : ContinuousPath ℂ => g (b 0) * Ψ b :=
    (hg.comp (continuous_eval_const 0).measurable).mul hΨ
  have h1 : ∫⁻ b, g (b s) * Ψ (ContinuousPath.shift s b) ∂planarLaw z =
      ∫⁻ b', g (b' 0) * Ψ b' ∂(planarLaw z).map (ContinuousPath.shift s) := by
    rw [lintegral_map hΦ (ContinuousPath.measurable_shift_fixed s)]
    simp only [ContinuousPath.shift_apply, add_zero]
  rw [h1, planarLaw, planarBrownianMotion_map_shift z s,
    Measure.lintegral_bind (HarmonicBalls.planarBrownianMotion.measurable.aemeasurable) hΦ.aemeasurable,
    HarmonicBalls.planarHeatSemigroup_apply]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_const_mul _ hΨ]
  exact lintegral_congr_ae (by filter_upwards [ae_planarLaw_eval_zero y] with b hb; rw [hb])

/-- Joint measurability of the path evaluation at a real time. -/
theorem measurable_eval_toNNReal_uncurry {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun p : ℝ × ContinuousPath ℂ => g (p.2 p.1.toNNReal) :=
  hg.comp (measurable_path_eval_uncurry.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))

/-- The window occupation integral is measurable in the path. -/
theorem measurable_windowOcc {g : ℂ → ℝ≥0∞} (hg : Measurable g) : Measurable (windowOcc g) := by
  have h : Measurable fun p : ContinuousPath ℂ × ℝ => g (p.1 p.2.toNNReal) :=
    (measurable_eval_toNNReal_uncurry hg).comp measurable_swap
  exact h.lintegral_prod_right'

/-- The window occupation integral of the shifted path is jointly measurable in the shift and the path. -/
theorem measurable_windowOcc_shift_uncurry {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun p : ℝ × ContinuousPath ℂ => windowOcc g (ContinuousPath.shift p.1.toNNReal p.2) := by
  have h : Measurable fun q : (ℝ × ContinuousPath ℂ) × ℝ =>
      g (q.1.2 (q.1.1.toNNReal + q.2.toNNReal)) :=
    hg.comp (measurable_path_eval_uncurry.comp
      ((((measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst)).add
        (measurable_real_toNNReal.comp measurable_snd))).prodMk (measurable_snd.comp measurable_fst)))
  exact h.lintegral_prod_right'

/-- **The expected window occupation integral** is the time integral of the Gaussian marginals. -/
theorem lintegral_windowOcc_planarLaw {g : ℂ → ℝ≥0∞} (hg : Measurable g) (y : ℂ) :
    ∫⁻ b, windowOcc g b ∂planarLaw y =
      ∫⁻ r in Ioc (0 : ℝ) 1, ∫⁻ x, g x ∂HarmonicBalls.planarGaussian y r.toNNReal := by
  have : IsProbabilityMeasure (planarLaw y) := by unfold planarLaw; infer_instance
  unfold windowOcc
  rw [lintegral_lintegral_swap (f := fun (b : ContinuousPath ℂ) (s : ℝ) => g (b s.toNNReal))
    (((measurable_eval_toNNReal_uncurry hg).comp measurable_swap).aemeasurable)]
  exact setLIntegral_congr_fun measurableSet_Ioc (fun r _ => lintegral_planarLaw_eval_eq r.toNNReal hg y)

/-- **Second moment of the window occupation integral** (Khas'minskii-type bound).  If `g` vanishes outside
`B̄(0, n)` and the Green potential `J(y) = ∫_{(0,1]} ∫ g d p_r(y, ·) dr` is at most `U` on `B̄(0, n)`, then
`E_z[I²] ≤ 2 U E_z[I]` for every start `z`. -/
theorem lintegral_windowOcc_sq_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) {n : ℝ}
    (hn : ∀ y : ℂ, n < ‖y‖ → g y = 0) {U : ℝ≥0∞}
    (hU : ∀ y : ℂ, ‖y‖ ≤ n →
      ∫⁻ r in Ioc (0 : ℝ) 1, ∫⁻ x, g x ∂HarmonicBalls.planarGaussian y r.toNNReal ≤ U) (z : ℂ) :
    ∫⁻ b, windowOcc g b ^ 2 ∂planarLaw z ≤ 2 * (U * ∫⁻ b, windowOcc g b ∂planarLaw z) := by
  have : IsProbabilityMeasure (planarLaw z) := by unfold planarLaw; infer_instance
  have hev := measurable_eval_toNNReal_uncurry hg
  have hW := measurable_windowOcc_shift_uncurry hg
  have hevb : ∀ b : ContinuousPath ℂ, Measurable fun t : ℝ => g (b t.toNNReal) := fun b =>
    hg.comp (b.continuous.comp continuous_real_toNNReal).measurable
  calc ∫⁻ b, windowOcc g b ^ 2 ∂planarLaw z
      ≤ ∫⁻ b, (2 * ∫⁻ s in Ioc (0 : ℝ) 1, g (b s.toNNReal) *
          windowOcc g (ContinuousPath.shift s.toNNReal b)) ∂planarLaw z := by
        refine lintegral_mono fun b => ?_
        refine (sq_setLIntegral_Ioc_le (hevb b)).trans ?_
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_)
        refine mul_le_mul' le_rfl ?_
        refine (setLIntegral_Ioc_indicator_Ici_le _ hs.1.le).trans (le_of_eq ?_)
        unfold windowOcc
        refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        simp only [ContinuousPath.shift_apply]
        rw [Real.toNNReal_add hs.1.le hr.1.le]
    _ = 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ b, g (b s.toNNReal) *
          windowOcc g (ContinuousPath.shift s.toNNReal b) ∂planarLaw z := by
        rw [lintegral_const_mul' _ _ (by simp)]
        congr 1
        exact lintegral_lintegral_swap (f := fun (b : ContinuousPath ℂ) (s : ℝ) => g (b s.toNNReal) *
          windowOcc g (ContinuousPath.shift s.toNNReal b))
          ((((hev.mul hW).comp measurable_swap)).aemeasurable)
    _ = 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ y, g y * ∫⁻ b, windowOcc g b ∂planarLaw y
          ∂HarmonicBalls.planarGaussian z s.toNNReal := by
        congr 1
        exact setLIntegral_congr_fun measurableSet_Ioc fun s _ =>
          lintegral_eval_mul_shift hg (measurable_windowOcc hg) s.toNNReal z
    _ ≤ 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ y, g y * U ∂HarmonicBalls.planarGaussian z s.toNNReal := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc fun s _ =>
          lintegral_mono fun y => ?_)
        by_cases hy : ‖y‖ ≤ n
        · rw [lintegral_windowOcc_planarLaw hg y]
          exact mul_le_mul' le_rfl (hU y hy)
        · rw [hn y (not_le.1 hy)]
          simp
    _ = 2 * (U * ∫⁻ b, windowOcc g b ∂planarLaw z) := by
        have hm : Measurable fun s : ℝ => ∫⁻ b, g (b s.toNNReal) ∂planarLaw z :=
          hev.lintegral_prod_right'
        have h1 : ∀ s : ℝ, ∫⁻ y, g y * U ∂HarmonicBalls.planarGaussian z s.toNNReal =
            (∫⁻ b, g (b s.toNNReal) ∂planarLaw z) * U := fun s => by
          rw [lintegral_mul_const _ hg, lintegral_planarLaw_eval_eq s.toNNReal hg z]
        rw [lintegral_windowOcc_planarLaw hg z]
        simp_rw [h1]
        rw [lintegral_mul_const _ hm, mul_comm U]
        congr 2
        exact setLIntegral_congr_fun measurableSet_Ioc fun s _ => lintegral_planarLaw_eval_eq s.toNNReal hg z

end MatedCRT.FirstPass.Derived
