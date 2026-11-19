import MatedCRT.FirstPass.Derived.RevuzInvariant
import MatedCRT.FirstPass.Derived.RevuzPositive
import MatedCRT.FirstPass.Derived.RevuzKernel

/-!
# Excessive measures of the time change are invariant

Let `A` be a PCAF of planar Brownian motion with a good clock, `P_u = timeChangeKernel A u` the kernel of the
time change `B ∘ τ`, and `μ_A` the Revuz measure of `A`.  A `σ`-finite measure `κ` that is excessive for the time
change (`κ P_u ≤ κ` for every `u`) and finite on some Borel set of positive `μ_A`-measure is invariant
(`κ P_u = κ` for every `u`).

The proof is the defect argument already used for `μ_A` itself (`RevuzInvariant.lean`), for a general `κ`: the
defect `D_h = κ − κ P_h` satisfies `∑_{k<n} (D_h P_{s+kh})(E) ≤ κ(E)`, hence, integrating over `s ∈ (0, h]`,
`∫ D_h(dx) ∫_{(0,∞)} P_r(x, E) dr ≤ h κ(E)`; on the other hand `∫_{(0,∞)} P_r(x, E) dr = ∞` for every `x` when
`μ_A(E) ≠ 0` (occupation-time recurrence of the time change, `setLIntegral_Ioi_timeChangeKernel_eq_top`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- The defect `D_h = κ − κ P_h` of a measure `κ` under the time change, written as `κ` with density
`1 − d(κ P_h)/dκ`. -/
noncomputable def timeChangeDefect (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (κ : Measure ℂ) (h : ℝ≥0) :
    Measure ℂ :=
  κ.withDensity (1 - (timeChangeKernel A h ∘ₘ κ).rnDeriv κ)

/-- **`κ = κ P_h + D_h`** when `κ P_h ≤ κ`. -/
theorem eq_bind_add_timeChangeDefect {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {κ : Measure ℂ} [SigmaFinite κ]
    {h : ℝ≥0} (hle : timeChangeKernel A h ∘ₘ κ ≤ κ) :
    κ = timeChangeKernel A h ∘ₘ κ + timeChangeDefect A κ h := by
  have : SigmaFinite (timeChangeKernel A h ∘ₘ κ) := Measure.sigmaFinite_of_le _ hle
  have hρ := Measure.rnDeriv_le_one_of_le hle
  calc κ = κ.withDensity 1 := withDensity_one.symm
    _ = κ.withDensity ((timeChangeKernel A h ∘ₘ κ).rnDeriv κ +
          (1 - (timeChangeKernel A h ∘ₘ κ).rnDeriv κ)) := by
        refine withDensity_congr_ae ?_
        filter_upwards [hρ] with x hx
        simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hx ⊢
        exact (add_tsub_cancel_of_le hx).symm
    _ = κ.withDensity ((timeChangeKernel A h ∘ₘ κ).rnDeriv κ) + timeChangeDefect A κ h :=
        withDensity_add_left (Measure.measurable_rnDeriv _ _) _
    _ = timeChangeKernel A h ∘ₘ κ + timeChangeDefect A κ h := by
        rw [Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hle)]

/-- **One step**: `(κ P_t)(E) = (κ P_{h+t})(E) + (D_h P_t)(E)`. -/
theorem bind_timeChangeKernel_apply_eq_add_defect {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {κ : Measure ℂ} [SigmaFinite κ] {h : ℝ≥0}
    (hle : timeChangeKernel A h ∘ₘ κ ≤ κ) (t : ℝ≥0) {E : Set ℂ} (hE : MeasurableSet E) :
    (timeChangeKernel A t ∘ₘ κ) E =
      (timeChangeKernel A (h + t) ∘ₘ κ) E + (timeChangeKernel A t ∘ₘ timeChangeDefect A κ h) E := by
  conv_lhs => rw [eq_bind_add_timeChangeDefect hle]
  rw [comp_timeChangeKernel_add hA hG _ h t, Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _), Measure.bind_apply hE (Kernel.aemeasurable _),
    lintegral_add_measure]

/-- **The iterated identity**: `(κ P_s)(E) = (κ P_{s+nh})(E) + ∑_{k<n} (D_h P_{s+kh})(E)`. -/
theorem bind_timeChangeKernel_apply_eq_add_sum_defect {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {κ : Measure ℂ} [SigmaFinite κ] {h : ℝ≥0}
    (hle : timeChangeKernel A h ∘ₘ κ ≤ κ) (s : ℝ≥0) {E : Set ℂ} (hE : MeasurableSet E) (n : ℕ) :
    (timeChangeKernel A s ∘ₘ κ) E =
      (timeChangeKernel A (s + n * h) ∘ₘ κ) E +
        ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ timeChangeDefect A κ h) E := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, bind_timeChangeKernel_apply_eq_add_defect hA hG hle (s + n * h) hE,
      show h + (s + n * h) = s + ((n + 1 : ℕ) : ℝ≥0) * h by push_cast; ring]
    ring

/-- **The defects of the time-shifted kernels sum below the mass of an excessive measure**:
`∑_{k<n} (D_h P_{s+kh})(E) ≤ κ(E)`. -/
theorem sum_bind_timeChangeKernel_defect_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {κ : Measure ℂ} [SigmaFinite κ]
    (hκ : ∀ u, timeChangeKernel A u ∘ₘ κ ≤ κ) (h s : ℝ≥0) {E : Set ℂ} (hE : MeasurableSet E) (n : ℕ) :
    ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ timeChangeDefect A κ h) E ≤ κ E :=
  calc ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ timeChangeDefect A κ h) E
      ≤ (timeChangeKernel A (s + n * h) ∘ₘ κ) E +
          ∑ k ∈ Finset.range n, (timeChangeKernel A (s + k * h) ∘ₘ timeChangeDefect A κ h) E := le_add_self
    _ = (timeChangeKernel A s ∘ₘ κ) E :=
        (bind_timeChangeKernel_apply_eq_add_sum_defect hA hG (hκ h) s hE n).symm
    _ ≤ κ E := Measure.le_iff'.1 (hκ s) E

/-- **The defect against the time-changed occupation**: `∫ D_h(dx) ∫_{(0,∞)} P_r(x, E) dr ≤ h κ(E)` for
`h > 0`. -/
theorem lintegral_setLIntegral_Ioi_timeChangeKernel_defect_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {κ : Measure ℂ} [SigmaFinite κ]
    (hκ : ∀ u, timeChangeKernel A u ∘ₘ κ ≤ κ) {h : ℝ≥0} (hh : 0 < h) {E : Set ℂ} (hE : MeasurableSet E) :
    ∫⁻ x, (∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x E) ∂timeChangeDefect A κ h ≤
      (h : ℝ≥0∞) * κ E := by
  have : SFinite (timeChangeDefect A κ h) := by unfold timeChangeDefect; infer_instance
  rw [lintegral_setLIntegral_Ioi_timeChangeKernel_eq_tsum hA.meas _ hh hE]
  calc ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ, (timeChangeKernel A (s + k * h).toNNReal ∘ₘ timeChangeDefect A κ h) E
      = ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ,
          (timeChangeKernel A (s.toNNReal + k * h) ∘ₘ timeChangeDefect A κ h) E := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => tsum_congr fun k => ?_
        have e : (s + k * h : ℝ).toNNReal = s.toNNReal + k * h := by
          apply NNReal.eq
          rw [Real.coe_toNNReal _ (add_nonneg hs.1.le (by positivity)), NNReal.coe_add,
            Real.coe_toNNReal _ hs.1.le]
          norm_cast
        rw [e]
    _ ≤ ∫⁻ _ in Ioc (0 : ℝ) h, κ E :=
        lintegral_mono fun s => ENNReal.tsum_le_of_sum_range_le fun n =>
          sum_bind_timeChangeKernel_defect_le hA hG hκ h s.toNNReal hE n
    _ = (h : ℝ≥0∞) * κ E := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_coe_nnreal, mul_comm]

/-- **The defect of an excessive measure vanishes**: `D_h = 0` for `h > 0`, when `κ(E) < ∞` for some Borel set
`E` with `μ_A(E) ≠ 0`. -/
theorem timeChangeDefect_eq_zero {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {κ : Measure ℂ} [SigmaFinite κ]
    (hκ : ∀ u, timeChangeKernel A u ∘ₘ κ ≤ κ) {E : Set ℂ} (hE : MeasurableSet E)
    (hμE : revuz planarLaw A E ≠ 0) (hκE : κ E ≠ ∞) {h : ℝ≥0} (hh : 0 < h) :
    timeChangeDefect A κ h = 0 := by
  have hle := lintegral_setLIntegral_Ioi_timeChangeKernel_defect_le hA hG hκ hh hE
  simp_rw [setLIntegral_Ioi_timeChangeKernel_eq_top hA hG hE hμE] at hle
  rw [lintegral_const] at hle
  refine Measure.measure_univ_eq_zero.1 ?_
  by_contra hD
  rw [ENNReal.top_mul hD] at hle
  exact lt_irrefl (∞ : ℝ≥0∞) (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.coe_lt_top hκE.lt_top))

/-- **Excessive measures of the time change are invariant**: a `σ`-finite `κ` with `κ P_u ≤ κ` for every `u`,
finite on some Borel set of positive Revuz measure, satisfies `κ P_u = κ` for every `u`. -/
theorem bind_timeChangeKernel_eq_of_excessive {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {κ : Measure ℂ} [SigmaFinite κ]
    (hκ : ∀ u, timeChangeKernel A u ∘ₘ κ ≤ κ) {E : Set ℂ} (hE : MeasurableSet E)
    (hμE : revuz planarLaw A E ≠ 0) (hκE : κ E ≠ ∞) (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ κ = κ := by
  rcases eq_zero_or_pos u with rfl | hu
  · ext S hS
    rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
    calc ∫⁻ x, timeChangeKernel A 0 x S ∂κ = ∫⁻ x, S.indicator 1 x ∂κ :=
          lintegral_congr fun x => timeChangeKernel_zero_apply hA hG x hS
      _ = κ S := lintegral_indicator_one hS
  · have := eq_bind_add_timeChangeDefect (hκ u)
    rw [timeChangeDefect_eq_zero hA hG hκ hE hμE hκE hu, add_zero] at this
    exact this.symm

/-- The Revuz measure of a PCAF of planar Brownian motion with a good clock is nonzero. -/
theorem revuz_planarLaw_ne_zero {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) : revuz planarLaw A ≠ 0 :=
  revuz_ne_zero_of_goodClock measurable_planarLaw planarLaw_ne_zero ae_planarLaw_eval_zero hA hG
    (measurable_occupationMeasure_regularize hA.meas)

/-- For every `σ`-finite `ρ` there is a Borel set of positive Revuz measure and finite `ρ`-measure. -/
theorem exists_measurableSet_revuz_ne_zero_lt_top {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (ρ : Measure ℂ) [SigmaFinite ρ] :
    ∃ E, MeasurableSet E ∧ revuz planarLaw A E ≠ 0 ∧ ρ E < ∞ := by
  obtain ⟨n, hn⟩ : ∃ n, revuz planarLaw A (spanningSets ρ n) ≠ 0 := by
    by_contra hcon
    apply revuz_planarLaw_ne_zero hA hG
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ρ]
    exact measure_iUnion_null fun i => not_not.1 (not_exists.1 hcon i)
  exact ⟨_, measurableSet_spanningSets ρ n, hn, measure_spanningSets_lt_top ρ n⟩

end MatedCRT
