import MarkovProcess.Path.ExitTimeShift

/-!
# The exit time of a time-scaled path and the exit-time distribution function

For a continuous path `f : ℝ≥0 → α` and `c > 0`, the time-scaled path `t ↦ f (c t)` leaves an open set
`U` at the time `(exit time of f) / c`.  Consequently the distribution function `x ↦ μ {exit time ≤ x}`
of the exit time under the image of a path measure `μ` by `f ↦ f (c ·)` is `x ↦ (exit cdf of μ) (c x)`.
The exit-time distribution function is a measurable function of the path measure (for the `σ`-algebra of
`Measure (ContinuousPath α)`).  These are the elementary facts that let the median of the exit time
recover the constant `c` of a time change (BG20, proof of Lemma 7.18).

* `MatedCRT.timeScalePath c f`: the path `t ↦ f (c t)`; `measurable_timeScalePath`.
* `MatedCRT.exitTime_timeScalePath`: `exitTime U (timeScalePath c f) = exitTime U f / c` for `c ≠ 0`.
* `MatedCRT.exitCdf U μ x = μ {f | exitTime U f ≤ x}`; `MatedCRT.measurable_exitCdf`,
  `MatedCRT.exitCdf_mono`.
* `MatedCRT.exitCdf_map_timeScalePath`: `exitCdf U (μ.map (timeScalePath c)) x = exitCdf U μ (c * x)`.
-/

open MeasureTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace MatedCRT

variable {α : Type*} [PseudoMetricSpace α]

/-- The time-scaled path `t ↦ f (c t)`. -/
def timeScalePath (c : ℝ≥0) (f : ContinuousPath α) : ContinuousPath α :=
  ContinuousMap.comp f ⟨fun t => c * t, continuous_const.mul continuous_id⟩

@[simp] theorem timeScalePath_apply (c : ℝ≥0) (f : ContinuousPath α) (t : ℝ≥0) :
    timeScalePath c f t = f (c * t) := rfl

theorem continuous_timeScalePath (c : ℝ≥0) : Continuous (timeScalePath (α := α) c) :=
  ContinuousMap.continuous_precomp ⟨fun t => c * t, continuous_const.mul continuous_id⟩

theorem measurable_timeScalePath (c : ℝ≥0) : Measurable (timeScalePath (α := α) c) :=
  (continuous_timeScalePath c).measurable

/-- A path `g` with `g t = f (c t)` leaves `U` no later than `f` does, divided by `c`. -/
theorem exitTime_le_div_of_comp (U : Set α) {c : ℝ≥0} (hc : c ≠ 0) (f g : ContinuousPath α)
    (hg : ∀ t, g t = f (c * t)) :
    ContinuousPath.exitTime U g ≤ ContinuousPath.exitTime U f / c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hc)) (Or.inl ENNReal.coe_ne_top)]
  refine le_sInf ?_
  rintro s ⟨u, rfl, hu⟩
  have hcu : c * (u / c) = u := by field_simp
  have hmem : g (u / c) ∉ U := by rwa [hg, hcu]
  calc ContinuousPath.exitTime U g * (c : ℝ≥0∞)
      ≤ ((u / c : ℝ≥0) : ℝ≥0∞) * (c : ℝ≥0∞) :=
        mul_le_mul_left (ContinuousPath.exitTime_le_of_notMem U g (u / c) hmem) _
    _ = (u : ℝ≥0∞) := by rw [← ENNReal.coe_mul, div_mul_cancel₀ u hc]

/-- **Exit time of a time-scaled path.**  `exitTime U (f (c ·)) = exitTime U f / c` for `c ≠ 0`. -/
theorem exitTime_timeScalePath (U : Set α) {c : ℝ≥0} (hc : c ≠ 0) (f : ContinuousPath α) :
    ContinuousPath.exitTime U (timeScalePath c f) = ContinuousPath.exitTime U f / c := by
  refine le_antisymm (exitTime_le_div_of_comp U hc f _ fun t => rfl) ?_
  have h := exitTime_le_div_of_comp U (inv_ne_zero hc) (timeScalePath c f) f fun t => by
    rw [timeScalePath_apply, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [ENNReal.coe_inv hc, div_eq_mul_inv, inv_inv] at h
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hc)) (Or.inl ENNReal.coe_ne_top)]
  exact h

/-- The distribution function `x ↦ μ {f | exitTime U f ≤ x}` of the exit time from `U` under the path
measure `μ`. -/
noncomputable def exitCdf (U : Set α) (μ : Measure (ContinuousPath α)) (x : ℝ) : ℝ≥0∞ :=
  μ {f | ContinuousPath.exitTime U f ≤ ENNReal.ofReal x}

theorem exitCdf_mono (U : Set α) (μ : Measure (ContinuousPath α)) : Monotone (exitCdf U μ) :=
  fun _ _ hxy => measure_mono fun _ hf => hf.trans (ENNReal.ofReal_le_ofReal hxy)

/-- The exit-time distribution function is a measurable function of the path measure when `U` is
open. -/
theorem measurable_exitCdf [MeasurableSpace α] [BorelSpace α] (U : Set α) (hU : IsOpen U) (x : ℝ) :
    Measurable fun μ : Measure (ContinuousPath α) => exitCdf U μ x :=
  Measure.measurable_coe (measurableSet_le (ContinuousPath.measurable_exitTime U hU) measurable_const)

/-- **Exit-time distribution function under a time change.**  Under the image of `μ` by
`f ↦ f (c ·)`, the exit time is at most `x` with probability `exitCdf U μ (c x)`. -/
theorem exitCdf_map_timeScalePath [MeasurableSpace α] [BorelSpace α] (U : Set α) (hU : IsOpen U)
    {c : ℝ≥0} (hc : c ≠ 0)
    (μ : Measure (ContinuousPath α)) (x : ℝ) :
    exitCdf U (μ.map (timeScalePath c)) x = exitCdf U μ (c * x) := by
  unfold exitCdf
  rw [Measure.map_apply (measurable_timeScalePath c)
    (measurableSet_le (ContinuousPath.measurable_exitTime U hU) measurable_const)]
  congr 1
  ext f
  have h1 : ENNReal.ofReal ((c : ℝ) * x) = (c : ℝ≥0∞) * ENNReal.ofReal x := by
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  show ContinuousPath.exitTime U (timeScalePath c f) ≤ ENNReal.ofReal x ↔
    ContinuousPath.exitTime U f ≤ ENNReal.ofReal ((c : ℝ) * x)
  rw [exitTime_timeScalePath U hc, h1, ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl ENNReal.coe_ne_top),
    mul_comm]

end MatedCRT
