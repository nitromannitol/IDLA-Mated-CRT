import MatedCRT.FirstPass.S4S6c.Lemma3Moment

/-!
# LEMMA68 Lemma 3, eqs (21)-(22): the second-moment wiring and eq (15) (q2, task fp-S4S6c; write-up B5)

Inputs (hypotheses, with their sources):
* the printed Lemma 2.18 with `N = 2` (Draft `ExitTimeUpperBoundStmt`, Section2.lean:234): `E[τ²] ≤ 2! C² ε⁻² S²`, where
  `S` is the supremum over the centre of the log-potential integral and `τ = σ_D` is the exit time;
* eq (21) (LEMMA68.md 330-345): `S ≤ C₁ (1 + log(1/R)) m₀`, from Lemma 1 (eq (5)) and the mass bound (eq (6)).
The occupation count `V = ∑_{n < σ_D} 1{X_n ∈ I(D) \ A}` satisfies `V ≤ σ_D = τ`. The eq (20) lower bound `E V ≥ ¼ ε⁻¹ m₀`
is a further hypothesis (Green identity and Lemma 2.16, write-up B4).
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Lemma3Second

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **eq (22)**: the second moment of the occupation count, from the Lemma 2.18 moment bound and eq (21). -/
theorem second_moment_le {P : Measure Ω} {V τ : Ω → ℝ≥0∞} (hVτ : ∀ ω, V ω ≤ τ ω)
    {ε C C1 L m0 S : ℝ} (hS0 : 0 ≤ S) (hSm : S ≤ C1 * L * m0)
    (hmom : ∫⁻ ω, τ ω ^ 2 ∂P ≤ ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2 * S ^ 2)) :
    ∫⁻ ω, V ω ^ 2 ∂P ≤ ENNReal.ofReal (2 * C ^ 2 * C1 ^ 2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) := by
  have h1 : ∫⁻ ω, V ω ^ 2 ∂P ≤ ∫⁻ ω, τ ω ^ 2 ∂P :=
    lintegral_mono fun ω => by
      have := hVτ ω
      gcongr
  have hS2 : S ^ 2 ≤ (C1 * L * m0) ^ 2 := by gcongr
  have h2 : ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2 * S ^ 2) ≤
      ENNReal.ofReal (2 * C ^ 2 * C1 ^ 2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    have hc : 0 ≤ 2 * C ^ 2 * ε⁻¹ ^ 2 := by positivity
    calc 2 * C ^ 2 * ε⁻¹ ^ 2 * S ^ 2 ≤ 2 * C ^ 2 * ε⁻¹ ^ 2 * (C1 * L * m0) ^ 2 :=
          mul_le_mul_of_nonneg_left hS2 hc
      _ = 2 * C ^ 2 * C1 ^ 2 * ε⁻¹ ^ 2 * L ^ 2 * m0 ^ 2 := by ring
  exact h1.trans (hmom.trans h2)

/-- **eq (15), from the second moment and the first moment (20)**: `P(V > 0) ≥ 1/(16 C₂ L²)` with `C₂ = 2 C² C₁²`, the
constant `q*` of eq (15) (`L = 1 + log(1/R)`). -/
theorem eq15_of_moments {P : Measure Ω} {V τ : Ω → ℝ≥0∞} (hV : Measurable V) (hVτ : ∀ ω, V ω ≤ τ ω)
    {ε m0 C C1 L S : ℝ} (hε : 0 < ε) (hm0 : 0 < m0) (hC : 0 < C) (hC1 : 0 < C1) (hL : 0 < L)
    (hS0 : 0 ≤ S) (hSm : S ≤ C1 * L * m0)
    (hE1 : ENNReal.ofReal ((1 / 4) * ε⁻¹ * m0) ≤ ∫⁻ ω, V ω ∂P)
    (hmom : ∫⁻ ω, τ ω ^ 2 ∂P ≤ ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2 * S ^ 2)) :
    ENNReal.ofReal (1 / (16 * (2 * C ^ 2 * C1 ^ 2) * L ^ 2)) ≤ P {ω | 0 < V ω} := by
  have hE2 := second_moment_le (P := P) hVτ hS0 hSm hmom
  have hC2 : 0 < 2 * C ^ 2 * C1 ^ 2 := by positivity
  exact Lemma3Moment.probability_pos_lower_bound P hV hε hm0 hC2 hL hE1 hE2

#print axioms MatedCRT.Lemma3Second.second_moment_le
#print axioms MatedCRT.Lemma3Second.eq15_of_moments

end Lemma3Second

end MatedCRT
