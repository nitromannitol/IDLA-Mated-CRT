import MatedCRT.FirstPass.S4S6c.Lemma3Counting
import MatedCRT.FirstPass.S4S6c.Lemma3Second
import MatedCRT.FirstPass.S4S6c.Lemma3Green

/-!
# LEMMA68 Lemma 3, eq (15), in the walk model (q2, task fp-S4S6c; write-up B1-B5)

The occupation count `occ A B x = ∑_{n} 1{n < τ_A(x), x_n ∈ B}` of a finite set `B` before the exit time `τ_A = vExitTime A`.
The eq (15) probability `P(occ > 0)` is bounded below by `q* = 1/(16 C₂ L²)`, `C₂ = 2 C² C₁²`, from:
* the Green lower bound `G(b) ≥ ½` on `B` (Lemma 2.16 in the walk model, hypothesis `hG`), giving `E[occ] ≥ |B|/2` (eq (20));
* the counting bound (eqs (16)-(18), `counting_half`), giving `|B| ≥ ½ ε⁻¹ m₀` and `E[occ] ≥ ¼ ε⁻¹ m₀`;
* the second moment: `occ ≤ τ_A` and the Lemma 2.18 bound `E[τ²] ≤ 2C²ε⁻²S²` (hypothesis `hmom`), with `S ≤ C₁ L m₀` (eq (21)).
Paley–Zygmund then gives the bound. The identification of `B` and the event with the printed objects is the remaining step.
-/

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

namespace Eq15Walk

/-- The occupation count of `B` before the exit time `vExitTime A`. -/
noncomputable def occ (A : Set ℤ) (B : Finset ℤ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  ∑' n : ℕ, (if (n : ℕ∞) < vExitTime A x ∧ x n ∈ B then (1 : ℝ≥0∞) else 0)

theorem tsum_ite_le_toENNReal (τ : ℕ∞) (p : ℕ → Prop) [DecidablePred p] :
    ∑' n : ℕ, (if (n : ℕ∞) < τ ∧ p n then (1 : ℝ≥0∞) else 0) ≤ ENat.toENNReal τ := by
  induction τ using ENat.recTopCoe with
  | top => simp
  | coe k =>
    rw [ENat.toENNReal_coe]
    have hzero : ∀ n ∉ Finset.range k, (if (n : ℕ∞) < (k : ℕ∞) ∧ p n then (1 : ℝ≥0∞) else 0) = 0 := by
      intro n hn
      split_ifs with h
      · exact absurd (Finset.mem_range.2 (by exact_mod_cast h.1)) hn
      · rfl
    rw [tsum_eq_sum hzero]
    calc ∑ n ∈ Finset.range k, (if (n : ℕ∞) < (k : ℕ∞) ∧ p n then (1 : ℝ≥0∞) else 0)
        ≤ ∑ n ∈ Finset.range k, (1 : ℝ≥0∞) := Finset.sum_le_sum fun n _ => by
          split_ifs <;> simp
      _ = (k : ℝ≥0∞) := by simp

/-- The occupation count is at most the exit time. -/
theorem occ_le_exit (A : Set ℤ) (B : Finset ℤ) (x : ℕ → ℤ) :
    occ A B x ≤ ENat.toENNReal (vExitTime A x) :=
  tsum_ite_le_toENNReal (vExitTime A x) (fun n => x n ∈ B)

/-- The occupation count is measurable on path space. -/
theorem measurable_occ (A : Set ℤ) (B : Finset ℤ) : Measurable (occ A B) := by
  unfold occ
  refine Measurable.tsum fun n => ?_
  have h1 : MeasurableSet {x : ℕ → ℤ | x n ∈ (B : Set ℤ)} := (measurable_pi_apply n) B.measurableSet
  have h2 := (ConstantOrderDiv.measurableSet_lt_vExitTime A n).inter h1
  have hset : MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime A x ∧ x n ∈ B} := by
    convert h2 using 1
    ext x
    simp
  exact Measurable.ite hset measurable_const measurable_const

/-- **eq (15) in the walk model**: `P(occ > 0) ≥ q* = 1/(16 C₂ L²)`, `C₂ = 2 C² C₁²`, from the Green lower bound (Lemma 2.16),
the counting bound (eqs (16)-(18)) and the Lemma 2.18 second-moment bound with eq (21). -/
theorem eq15_walk (μ : Measure (ℕ → ℤ)) (A : Set ℤ) (D0 Aset : Finset ℤ)
    {ε m0 C C1 L Sr e1 s : ℝ}
    (hε : 0 < ε) (hm0 : 0 < m0) (hC : 0 < C) (hC1 : 0 < C1) (hL : 0 < L)
    (hS0 : 0 ≤ Sr) (hSm : Sr ≤ C1 * L * m0)
    (he1 : e1 ≤ m0 / 4) (hs : s ≤ m0 / 4)
    (hS : ε⁻¹ * (m0 - e1) ≤ (D0.card : ℝ)) (hT : (Aset.card : ℝ) ≤ ε⁻¹ * s)
    (hG : ∀ b ∈ D0 \ Aset, (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, μ {x | (n : ℕ∞) < vExitTime A x ∧ x n = b})
    (hmom : ∫⁻ x, (ENat.toENNReal (vExitTime A x)) ^ 2 ∂μ ≤ ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2)) :
    ENNReal.ofReal (1 / (16 * (2 * C ^ 2 * C1 ^ 2) * L ^ 2)) ≤ μ {x | 0 < occ A (D0 \ Aset) x} := by
  have hEV : (((D0 \ Aset).card : ℕ) : ℝ≥0∞) * (1 / 2) ≤ ∫⁻ x, occ A (D0 \ Aset) x ∂μ :=
    Lemma3Green.green_occupation_ge μ A (D0 \ Aset) hG
  have hE1 : ENNReal.ofReal ((1 / 4) * ε⁻¹ * m0) ≤ ∫⁻ x, occ A (D0 \ Aset) x ∂μ :=
    Lemma3Counting.first_moment_ge D0 Aset hε hm0 he1 hs hS hT hEV
  exact Lemma3Second.eq15_of_moments (measurable_occ A (D0 \ Aset))
    (fun x => occ_le_exit A (D0 \ Aset) x) hε hm0 hC hC1 hL hS0 hSm hE1 hmom

#print axioms MatedCRT.Eq15Walk.tsum_ite_le_toENNReal
#print axioms MatedCRT.Eq15Walk.eq15_walk

end Eq15Walk

end MatedCRT
