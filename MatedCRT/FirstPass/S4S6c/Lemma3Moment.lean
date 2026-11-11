import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Lemma 3: the second-moment step

The lower bound of eq (15) is a Paley–Zygmund / Cauchy–Schwarz argument for the occupation count
`V = ∑_{n < σ_D} 1{X_n ∈ I(D) \ A}` (300-330, eqs (20)-(22)):
* `E[V] ≥ ¼ ε⁻¹ m₀` (eq (20): the Green function identity and (18)-(19), from `GreenKernelLowerBoundStmt`, Draft Section2:207);
* `E[V²] ≤ C₂ ε⁻² (1 + log(1/R))² m₀²` (eq (22): the printed Lemma 2.18 with `N = 2`, Draft Section2:234, together with
  the bound (21) on the sup of the log potential by `C₁ (1 + log(1/R)) m₀`).
The generic inequality `(E V)² ≤ E[V²] · P(V > 0)` is proved here, by Hölder with exponents `2` and `2`; the eq (15)
constant is then `q* = 1/(16 C₂ (1 + log(1/R))²)`. The two expectation bounds are hypotheses of the final theorem.
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma3Moment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz for the occupation count: `(∫⁻ V)² ≤ (∫⁻ V²) · P(V > 0)`. -/
theorem sq_lintegral_le_lintegral_sq_mul_measure (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    (∫⁻ ω, V ω ∂P) ^ 2 ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | 0 < V ω} := by
  have hS : MeasurableSet {ω | 0 < V ω} := measurableSet_lt measurable_const hV
  have hgm : Measurable ({ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞)) := measurable_one.indicator hS
  have hpt : ∀ ω, V ω = V ω * {ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    by_cases h : 0 < V ω
    · simp [h]
    · have h0 : V ω = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h)
      simp [h0]
  have hint : ∫⁻ ω, V ω ∂P = ∫⁻ ω, V ω * {ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞) ω ∂P :=
    lintegral_congr hpt
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (f := V) (g := {ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞)) hV.aemeasurable hgm.aemeasurable
  have hV2 : ∀ ω, V ω ^ (2 : ℝ) = V ω ^ 2 := fun ω => ENNReal.rpow_two _
  have hg2 : ∀ ω, ({ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞) ω) ^ (2 : ℝ) =
      {ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, hV2, hg2, lintegral_indicator_one hS] at hH
  calc (∫⁻ ω, V ω ∂P) ^ 2 = (∫⁻ ω, V ω * {ω | 0 < V ω}.indicator (1 : Ω → ℝ≥0∞) ω ∂P) ^ 2 := by
        rw [hint]
    _ ≤ ((∫⁻ ω, V ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (P {ω | 0 < V ω}) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | 0 < V ω} := by rw [mul_pow, hsq, hsq]

/-- Paley–Zygmund form: from `a ≤ E V` and `E V² ≤ b`, `a² ≤ b · P(V > 0)`. -/
theorem sq_le_mul_measure_pos (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V) {a b : ℝ≥0∞}
    (ha : a ≤ ∫⁻ ω, V ω ∂P) (hb : ∫⁻ ω, V ω ^ 2 ∂P ≤ b) :
    a ^ 2 ≤ b * P {ω | 0 < V ω} := by
  calc a ^ 2 ≤ (∫⁻ ω, V ω ∂P) ^ 2 := by gcongr
    _ ≤ (∫⁻ ω, V ω ^ 2 ∂P) * P {ω | 0 < V ω} := sq_lintegral_le_lintegral_sq_mul_measure P hV
    _ ≤ b * P {ω | 0 < V ω} := by gcongr

/-- **eq (15) constant.** If `E V ≥ ¼ ε⁻¹ m₀` (eq (20)) and `E V² ≤ C₂ ε⁻² L² m₀²` with `L = 1 + log(1/R) > 0` (eq (22)),
then `P(V > 0) ≥ 1/(16 C₂ L²)`, the constant `q*` of eq (15). -/
theorem probability_pos_lower_bound (P : Measure Ω) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    {ε m0 C2 L : ℝ} (hε : 0 < ε) (hm0 : 0 < m0) (hC2 : 0 < C2) (hL : 0 < L)
    (hE1 : ENNReal.ofReal ((1 / 4) * ε⁻¹ * m0) ≤ ∫⁻ ω, V ω ∂P)
    (hE2 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2)) :
    ENNReal.ofReal (1 / (16 * C2 * L ^ 2)) ≤ P {ω | 0 < V ω} := by
  have key := sq_le_mul_measure_pos P hV hE1 hE2
  have hbpos : 0 < C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2 := by positivity
  have hb0 : ENNReal.ofReal (C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hbpos).ne'
  have hbt : ENNReal.ofReal (C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcpos : 0 ≤ 1 / (16 * C2 * L ^ 2) := by positivity
  have hapos : 0 ≤ (1 / 4) * ε⁻¹ * m0 := by positivity
  have hcb : ENNReal.ofReal (1 / (16 * C2 * L ^ 2)) * ENNReal.ofReal (C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) =
      (ENNReal.ofReal ((1 / 4) * ε⁻¹ * m0)) ^ 2 := by
    rw [← ENNReal.ofReal_mul hcpos, ← ENNReal.ofReal_pow hapos]
    congr 1
    field_simp
    ring
  have h3 : ENNReal.ofReal (1 / (16 * C2 * L ^ 2)) * ENNReal.ofReal (C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) ≤
      P {ω | 0 < V ω} * ENNReal.ofReal (C2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) := by
    rw [hcb, mul_comm (P {ω | 0 < V ω})]
    exact key
  exact (ENNReal.mul_le_mul_iff_left hb0 hbt).1 h3

#print axioms MatedCRT.Lemma3Moment.sq_lintegral_le_lintegral_sq_mul_measure
#print axioms MatedCRT.Lemma3Moment.probability_pos_lower_bound

end Lemma3Moment

end MatedCRT
