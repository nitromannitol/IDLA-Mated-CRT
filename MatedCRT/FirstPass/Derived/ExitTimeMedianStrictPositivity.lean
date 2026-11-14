import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import MatedCRT.Defs.Notation
import MatedCRT.FirstPass.Derived.ExitTimeScaling

/-!
# Positivity of log-normal mixtures and the strict median bound for exit-time distribution functions

Two elementary facts used to show that the exit-time distribution function of the Liouville Brownian motion is
strictly above `1/2` to the right of its lower median (the hypothesis `hstrict` of
`MatedCRT.ExitTimeCdf.tendsto_medianOf_exitCdf`).

* `MatedCRT.measure_exp_mul_mem_Ioc_pos`: if `Y` is a centred Gaussian with nonzero variance, `W > 0` almost surely
  and `Y` is independent of `W`, then the log-normal mixture `e^{γ Y} W` (`γ > 0`) charges every interval
  `(a, c]` with `0 < a < c`.
* `MatedCRT.half_lt_measure_le_of_medianOf_lt`: if a `[0, ∞]`-valued random variable `T` is almost surely finite
  and charges every interval `(a, c]` with `0 < a < c`, then its distribution function `G s = P[T ≤ s]` satisfies
  `G s > 1/2` for every `s` strictly larger than the lower median `medianOf G`.
* `MatedCRT.ExitTimeCdf.half_lt_exitCdf_of_medianOf_lt`: the same statement for the exit-time distribution
  function `exitCdf U μ` of an open set `U` under a probability measure `μ` on paths, in the form of the hypothesis
  `hstrict` of `MatedCRT.ExitTimeCdf.tendsto_medianOf_exitCdf`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- **Positivity of a log-normal mixture on intervals.** Let `Y` have the centred Gaussian law of variance
`v ≠ 0`, let `W > 0` almost surely, and let `Y` and `W` be independent. Then for `γ > 0` and `0 < a < c`, the
random variable `e^{γ Y} W` lies in `(a, c]` with positive probability. -/
theorem measure_exp_mul_mem_Ioc_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y W : Ω → ℝ} (hYm : Measurable Y) (hWm : Measurable W)
    {v : ℝ≥0} (hv : v ≠ 0) (hY : P.map Y = gaussianReal 0 v) (hW : ∀ᵐ ω ∂P, 0 < W ω)
    (hind : IndepFun Y W P) {γ : ℝ} (hγ : 0 < γ) {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < P {ω | Real.exp (γ * Y ω) * W ω ∈ Ioc a c} := by
  have hE : MeasurableSet {p : ℝ × ℝ | Real.exp (γ * p.2) * p.1 ∈ Ioc a c} :=
    measurableSet_Ioc.preimage
      ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
        continuous_fst).measurable
  have hprod : P.map (fun ω => (W ω, Y ω)) = (P.map W).prod (gaussianReal 0 v) := by
    rw [← hY]
    exact (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hYm.aemeasurable).1 hind.symm
  -- for a fixed value `w > 0` of `W`, the Gaussian charges the interval of `y` with `e^{γ y} w ∈ (a, c]`
  have hpt : ∀ w : ℝ, 0 < w →
      gaussianReal 0 v (Prod.mk w ⁻¹' {p : ℝ × ℝ | Real.exp (γ * p.2) * p.1 ∈ Ioc a c}) ≠ 0 := by
    intro w hw h0
    have hsub : Ioo (Real.log (a / w) / γ) (Real.log (c / w) / γ) ⊆
        Prod.mk w ⁻¹' {p : ℝ × ℝ | Real.exp (γ * p.2) * p.1 ∈ Ioc a c} := by
      intro y hy
      have h1 : Real.log (a / w) < γ * y := (div_lt_iff₀' hγ).1 hy.1
      have h2 : γ * y < Real.log (c / w) := (lt_div_iff₀' hγ).1 hy.2
      have h3 : a / w < Real.exp (γ * y) := (Real.log_lt_iff_lt_exp (div_pos ha hw)).1 h1
      have h4 : Real.exp (γ * y) < c / w :=
        (Real.lt_log_iff_exp_lt (div_pos (ha.trans hac) hw)).1 h2
      show a < Real.exp (γ * y) * w ∧ Real.exp (γ * y) * w ≤ c
      exact ⟨(div_lt_iff₀ hw).1 h3, ((lt_div_iff₀ hw).1 h4).le⟩
    have hl : Real.log (a / w) / γ < Real.log (c / w) / γ :=
      div_lt_div_of_pos_right
        (Real.log_lt_log (div_pos ha hw) (div_lt_div_of_pos_right hac hw)) hγ
    have hvol := gaussianReal_absolutelyContinuous' 0 hv (measure_mono_null hsub h0)
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hvol
    linarith
  have hνW : ∀ᵐ w ∂(P.map W), 0 < w :=
    (ae_map_iff (p := fun w : ℝ => 0 < w) hWm.aemeasurable measurableSet_Ioi).2 hW
  have hνP : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hWm.aemeasurable).2 inferInstance
  have hpre : {ω | Real.exp (γ * Y ω) * W ω ∈ Ioc a c} =
      (fun ω => (W ω, Y ω)) ⁻¹' {p : ℝ × ℝ | Real.exp (γ * p.2) * p.1 ∈ Ioc a c} := rfl
  rw [hpre, ← Measure.map_apply (hWm.prodMk hYm) hE, hprod, Measure.prod_apply hE]
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hE)] at h0
  have hfalse : ∀ᵐ w ∂(P.map W), False := by
    filter_upwards [h0, hνW] with w hw hwpos
    exact hpt w hwpos hw
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  have h1 := measure_univ (μ := P.map W)
  rw [hfalse] at h1
  simp at h1

/-- **Strict median bound.** Let `T` be an almost surely finite `[0, ∞]`-valued random variable that charges every
interval `(a, c]` with `0 < a < c`, and let `G s = P[T ≤ s]` be its distribution function. Then `G s > 1/2` for
every `s` strictly larger than the lower median `medianOf G`. -/
theorem half_lt_measure_le_of_medianOf_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → ℝ≥0∞} (hT : Measurable T) (hfin : ∀ᵐ x ∂μ, T x < ∞)
    (hpos : ∀ a c : ℝ, 0 < a → a < c →
      0 < μ {x | T x ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)})
    {s : ℝ} (hs : medianOf (fun r => μ {x | T x ≤ ENNReal.ofReal r}) < s) :
    (1 / 2 : ℝ≥0∞) < μ {x | T x ≤ ENNReal.ofReal s} := by
  -- the distribution function tends to `1` at infinity, so the median set is nonempty
  have hmono : Monotone fun n : ℕ => {x | T x ≤ ENNReal.ofReal n} := fun i j hij x hx =>
    le_trans hx (ENNReal.ofReal_le_ofReal (Nat.cast_le.2 hij))
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n : ℕ, {x | T x ≤ ENNReal.ofReal n} := by
    filter_upwards [hfin] with x hx
    obtain ⟨n, hn⟩ := exists_nat_ge (T x).toReal
    exact mem_iUnion.2
      ⟨n, (ENNReal.ofReal_toReal hx.ne).symm.le.trans (ENNReal.ofReal_le_ofReal hn)⟩
  have hU : μ (⋃ n : ℕ, {x | T x ≤ ENNReal.ofReal n}) = 1 := by
    rw [← measure_univ (μ := μ)]
    exact measure_congr (ae_eq_univ.2 (mem_ae_iff.1 hcov))
  have htend : Tendsto (μ ∘ fun n : ℕ => {x | T x ≤ ENNReal.ofReal n}) atTop (𝓝 1) := by
    rw [← hU]
    exact tendsto_measure_iUnion_atTop hmono
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).1 _
    (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top)).exists
  have hne : {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ μ {x | T x ≤ ENNReal.ofReal m}}.Nonempty :=
    ⟨n, Nat.cast_nonneg n, hn.le⟩
  have hbdd : BddBelow {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ μ {x | T x ≤ ENNReal.ofReal m}} :=
    ⟨0, fun m hm => hm.1⟩
  -- a point `m < s` of the median set, and the interval `(max m (s/2), s]` charged by `T`
  obtain ⟨m, ⟨hm0, hmG⟩, hms⟩ := (csInf_lt_iff hbdd hne).1 hs
  have hs0 : 0 < s := hm0.trans_lt hms
  have ha0 : 0 < max m (s / 2) := lt_max_of_lt_right (half_pos hs0)
  have has : max m (s / 2) < s := max_lt hms (half_lt_self hs0)
  have hA : (1 / 2 : ℝ≥0∞) ≤ μ {x | T x ≤ ENNReal.ofReal (max m (s / 2))} :=
    hmG.trans (measure_mono fun x hx =>
      le_trans hx (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hdisj : Disjoint {x | T x ≤ ENNReal.ofReal (max m (s / 2))}
      {x | T x ∈ Ioc (ENNReal.ofReal (max m (s / 2))) (ENNReal.ofReal s)} :=
    Set.disjoint_left.2 fun x hxA hxB => not_le.2 hxB.1 hxA
  have hsub : {x | T x ≤ ENNReal.ofReal (max m (s / 2))} ∪
      {x | T x ∈ Ioc (ENNReal.ofReal (max m (s / 2))) (ENNReal.ofReal s)} ⊆
      {x | T x ≤ ENNReal.ofReal s} :=
    union_subset (fun x hx => le_trans hx (ENNReal.ofReal_le_ofReal has.le)) fun x hx => hx.2
  calc (1 / 2 : ℝ≥0∞)
      < 1 / 2 + μ {x | T x ∈ Ioc (ENNReal.ofReal (max m (s / 2))) (ENNReal.ofReal s)} :=
        ENNReal.lt_add_right (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero).ne
          (hpos _ _ ha0 has).ne'
    _ ≤ μ {x | T x ≤ ENNReal.ofReal (max m (s / 2))} +
        μ {x | T x ∈ Ioc (ENNReal.ofReal (max m (s / 2))) (ENNReal.ofReal s)} := by gcongr
    _ = μ ({x | T x ≤ ENNReal.ofReal (max m (s / 2))} ∪
        {x | T x ∈ Ioc (ENNReal.ofReal (max m (s / 2))) (ENNReal.ofReal s)}) :=
        (measure_union hdisj (hT measurableSet_Ioc)).symm
    _ ≤ μ {x | T x ≤ ENNReal.ofReal s} := measure_mono hsub

namespace ExitTimeCdf

/-- **Strict median bound for exit-time distribution functions.** Let `U` be open and let `μ` be a probability
measure on paths under which the exit time from `U` is almost surely finite and charges every interval `(a, c]`
with `0 < a < c`. Then the exit-time distribution function `exitCdf U μ` is strictly above `1/2` to the right of
its lower median: this is the hypothesis `hstrict` of `MatedCRT.ExitTimeCdf.tendsto_medianOf_exitCdf`. -/
theorem half_lt_exitCdf_of_medianOf_lt {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [BorelSpace α] {U : Set α} (hU : IsOpen U) {μ : Measure (ContinuousPath α)}
    [IsProbabilityMeasure μ] (hfin : ∀ᵐ g ∂μ, ContinuousPath.exitTime U g < ∞)
    (hpos : ∀ a c : ℝ, 0 < a → a < c →
      0 < μ {g | ContinuousPath.exitTime U g ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)}) :
    ∀ s, medianOf (exitCdf U μ) < s → (1 / 2 : ℝ≥0∞) < exitCdf U μ s :=
  fun _ hs => half_lt_measure_le_of_medianOf_lt (ContinuousPath.measurable_exitTime U hU) hfin hpos hs

end ExitTimeCdf

end MatedCRT
