import Mathlib

/-!
# One-test estimate (chat 188, §3 `S5_oneTest`): the deterministic part

For a measure `P` (for the paper, the conditional law given `(h, η)`) and a measurable one-test variable
`V : Ω → ℝ≥0∞`:
* `paley_zygmund_sq`: `(∫⁻ V dP)² ≤ (∫⁻ V² dP) · P{V ≠ 0}` (second-moment method, Cauchy-Schwarz = Hölder with p = q = 2);
* `oneTest_prob_lower` (S5.3): under the first moment `c ε⁻¹ m ≤ E V` (S5.1) and the second moment
  `E V² ≤ C ε⁻² (1 + log(1/R))² m²` (S5.2), with `0 < R ≤ 1`: `c²/(C (1 + log(1/R))²) ≤ P{V ≠ 0}`;
* `oneTest_prob_lower_log` (S5.4): for `r² ≤ R ≤ 1` and `0 < r ≤ 1`: `(c²/(4C)) / (1 + log(1/r))² ≤ P{V ≠ 0}`.

NAMED INPUTS, not proved in this file: the first moment (S5.1) and the second moment (S5.2) are hypotheses of the
statements. In the chat they come from the printed Steps 2-4 with the corrected good event, the Green lower bound
(Lemma 2.16), the corrected ball-form exit-time estimate, and the mass condition `μ_h(B_{R/4}(x)) ≥ c R^{β⁻}`. The
shell form of the test start (S7' step 9, `S5_geometry_at_shell_test`) is likewise not proved here. `m` is the real
value of `m_R^φ` (positive and finite on the good event). `V` is abstract: the chat does not define it in §7.

Terminology: second-moment (Paley-Zygmund) method; Armstrong-Kuusi-Mourrat (good annuli and one-test estimates).
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Window

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(x ^ (1/2))² = x` in `ℝ≥0∞`. -/
lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Second-moment (Paley-Zygmund) inequality: `(∫ V)² ≤ (∫ V²) · P{V ≠ 0}`. -/
theorem paley_zygmund_sq (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    (∫⁻ ω, V ω ∂P) ^ 2 ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} := by
  have hS : MeasurableSet {ω | V ω ≠ 0} := hV (measurableSet_singleton (0 : ℝ≥0∞)).compl
  set g : Ω → ℝ≥0∞ := {ω | V ω ≠ 0}.indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator hS
  have hVg : ∀ ω, V ω * g ω = V ω := by
    intro ω
    by_cases h : V ω = 0
    · simp [h]
    · simp [hg, Set.indicator_of_mem (show ω ∈ {ω | V ω ≠ 0} from h)]
  have hgg : ∀ ω, g ω ^ (2 : ℝ) = g ω := by
    intro ω
    by_cases h : V ω = 0
    · simp [hg, Set.indicator_of_notMem (show ω ∉ {ω | V ω ≠ 0} from fun h' => h' h)]
    · simp [hg, Set.indicator_of_mem (show ω ∈ {ω | V ω ≠ 0} from h)]
  have hVsq : ∀ ω, V ω ^ (2 : ℝ) = V ω ^ 2 := fun ω => by
    rw [← ENNReal.rpow_natCast]
    norm_num
  have hint : ∫⁻ ω, g ω ∂P = P {ω | V ω ≠ 0} := by
    rw [hg, lintegral_indicator_one hS]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P (Real.HolderConjugate.two_two) hV.aemeasurable hgm.aemeasurable
  have hA : ∫⁻ ω, V ω ∂P ≤ (∫⁻ ω, V ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (P {ω | V ω ≠ 0}) ^ (1 / 2 : ℝ) := by
    have hEq : ∫⁻ ω, V ω ∂P = ∫⁻ ω, (V * g) ω ∂P := lintegral_congr fun ω => (hVg ω).symm
    rw [hEq]
    simpa [hVsq, hgg, hint] using hHolder
  calc (∫⁻ ω, V ω ∂P) ^ 2
      ≤ ((∫⁻ ω, V ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (P {ω | V ω ≠ 0}) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} := by
      rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- (S5.3) of chat 188 §7: the one-test lower bound `P{V ≠ 0} ≥ c²/(C (1 + log(1/R))²)` from the first moment (S5.1) and
the second moment (S5.2); `0 < R ≤ 1` makes `1 + log(1/R) ≥ 1 > 0`. -/
theorem oneTest_prob_lower {c C ε m R : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hR : 0 < R) (hR1 : R ≤ 1) (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (h1 : ENNReal.ofReal (c * ε⁻¹ * m) ≤ ∫⁻ ω, V ω ∂P)
    (h2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C * (ε⁻¹ ^ 2) * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)) :
    ENNReal.ofReal (c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2)) ≤ P {ω | V ω ≠ 0} := by
  set L := Real.log (1 / R) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_one_div hR hR1)
  have hpos1 : 0 < 1 + L := by linarith
  set a := c * ε⁻¹ * m with ha
  set b := C * (ε⁻¹ ^ 2) * (1 + L) ^ 2 * m ^ 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 < b := by positivity
  have hPZ := paley_zygmund_sq P hV
  have hsq : ENNReal.ofReal (a ^ 2) ≤ (∫⁻ ω, V ω ∂P) ^ 2 := by
    rw [ENNReal.ofReal_pow ha0]
    gcongr
  have hmain : ENNReal.ofReal (a ^ 2) ≤ P {ω | V ω ≠ 0} * ENNReal.ofReal b := by
    calc ENNReal.ofReal (a ^ 2) ≤ (∫⁻ ω, V ω ∂P) ^ 2 := hsq
      _ ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | V ω ≠ 0} := hPZ
      _ ≤ ENNReal.ofReal b * P {ω | V ω ≠ 0} := by
        gcongr
      _ = P {ω | V ω ≠ 0} * ENNReal.ofReal b := mul_comm _ _
  have hratio : a ^ 2 / b = c ^ 2 / (C * (1 + L) ^ 2) := by
    rw [ha, hb]
    field_simp
  rw [← hratio, ENNReal.ofReal_div_of_pos hb0]
  exact ENNReal.div_le_of_le_mul hmain

/-- (S5.4) of chat 188 §7: for `r² ≤ R ≤ 1`, `log(1/R) ≤ 2 log(1/r)`, so the one-test bound has the form
`q(r) / (1 + log(1/r))²` with `q = c²/(4C)`. -/
theorem oneTest_prob_lower_log {c C ε m r R : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r ≤ 1) (hRr : r ^ 2 ≤ R) (hR : 0 < R) (hR1 : R ≤ 1)
    (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (h1 : ENNReal.ofReal (c * ε⁻¹ * m) ≤ ∫⁻ ω, V ω ∂P)
    (h2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C * (ε⁻¹ ^ 2) * (1 + Real.log (1 / R)) ^ 2 * m ^ 2)) :
    ENNReal.ofReal (c ^ 2 / (4 * C) / (1 + Real.log (1 / r)) ^ 2) ≤ P {ω | V ω ≠ 0} := by
  have hmain := oneTest_prob_lower hc hC hε hm hR hR1 P hV h1 h2
  have hx0 : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hL0 : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hL : Real.log (1 / R) ≤ 2 * Real.log (1 / r) := by
    have hle : 1 / R ≤ (1 / r) ^ 2 := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) hRr
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hsq : (1 + Real.log (1 / R)) ^ 2 ≤ 4 * (1 + Real.log (1 / r)) ^ 2 := by
    nlinarith
  have hcmp : c ^ 2 / (4 * C) / (1 + Real.log (1 / r)) ^ 2 ≤ c ^ 2 / (C * (1 + Real.log (1 / R)) ^ 2) := by
    have hpos : 0 < (1 + Real.log (1 / R)) ^ 2 := by nlinarith
    have hpos2 : 0 < (1 + Real.log (1 / r)) ^ 2 := by nlinarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ c ^ 2 * C)]
  exact (ENNReal.ofReal_le_ofReal hcmp).trans hmain

end Lemma68Window

end MatedCRT
