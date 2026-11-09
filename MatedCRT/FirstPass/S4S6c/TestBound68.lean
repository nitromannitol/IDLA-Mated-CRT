import MatedCRT.FirstPass.S4S6c.Lemma3Walk

/-!
# The per-test bound `hc` of printed Lemma 6.8 from Lemma 3, equation (15) (q2, task fp-S4S6c)

LEMMA68 per-test bound (notes/fp-gaps/CHATGPT-lemma68-open-parts.md, C4 and C15-C16): the walk started at `y`
stays in `A` until it exits the test window `W y` with probability at most `1 - q(r)`, where
`q(r) = q0 / (1 + log(1/r))²`. The walk-level input is Lemma 3, equation (15) (`Eq15Walk.eq15_walk`), a lower
bound on the probability that the walk visits the target `D0 \ Aset` before exiting `W y`. The target lies in
`W y \ A`, so such a visit is a failure of `stayIn W A y`; the complement of the target event is therefore
an upper bound for `stayIn`.

The environment-level hypotheses are NOT proved here: the counting bounds `hS`, `hT` (write-up B3, C4), the
Green lower bound `hG` (B4, the interior-ball Green bound), and the second moment `hmom` (B5, Lemma 1 potential
bound with its logarithmic loss). The second-moment constant is `C0 (1 + log(1/r))`.

`stayIn W A y` is the set `stayInRegion W A y` of `SuccessiveExitStop.lean:24` (same definition, restated here so
that this file does not import the exit-stop chain, which clashes with the `Lemma3Walk` chain on `pathShift`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

namespace TestBound68

/-- The walk started at `y` stays in `A` until its exit from the window `W y` (printed `stayInRegion`). -/
def stayIn (W : ℤ → Set ℤ) (A : Set ℤ) (y : ℤ) : Set (ℕ → ℤ) :=
  {w | ∀ n : ℕ, (n : ℕ∞) < vExitTime (W y) w → w n ∈ A}

/-- **Lemma 3, equation (15), per-test form.** The probability that the walk started at `y` stays in `A` until
its exit from `W y` is at most `1 - c`, with `c = 1 / (16 (2 C² C1²) L²)`, where the target `D0 \ Aset` lies in
`W y \ A`. -/
theorem stayIn_le_of_eq15 {m : ℤ → ℤ → ℕ} {y : ℤ} {W : ℤ → Set ℤ} {A : Set ℤ} {D0 Aset : Finset ℤ}
    {ε m0 C C1 L Sr e1 s : ℝ} (hε : 0 < ε) (hm0 : 0 < m0) (hC : 0 < C) (hC1 : 0 < C1) (hL : 0 < L)
    (hS0 : 0 ≤ Sr) (hSm : Sr ≤ C1 * L * m0) (he1 : e1 ≤ m0 / 4) (hs : s ≤ m0 / 4)
    (hS : ε⁻¹ * (m0 - e1) ≤ (D0.card : ℝ)) (hT : (Aset.card : ℝ) ≤ ε⁻¹ * s)
    (hD : ∀ b ∈ D0 \ Aset, b ∈ W y ∧ b ∉ A)
    (hG : ∀ b ∈ D0 \ Aset,
      (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, srwLaw m y {x | (n : ℕ∞) < vExitTime (W y) x ∧ x n = b})
    (hmom : ∫⁻ x, (ENat.toENNReal (vExitTime (W y) x)) ^ 2 ∂(srwLaw m y) ≤
      ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2)) :
    srwLaw m y (stayIn W A y) ≤ 1 - ENNReal.ofReal (1 / (16 * (2 * C ^ 2 * C1 ^ 2) * L ^ 2)) := by
  classical
  have h15 := Eq15Walk.eq15_walk (srwLaw m y) (W y) D0 Aset hε hm0 hC hC1 hL hS0 hSm he1 hs hS hT hG hmom
  have hsub : stayIn W A y ⊆ {x : ℕ → ℤ | 0 < Eq15Walk.occ (W y) (D0 \ Aset) x}ᶜ := by
    intro w hw hpos
    have hpos' : 0 < Eq15Walk.occ (W y) (D0 \ Aset) w := hpos
    have hw' : ∀ n : ℕ, (n : ℕ∞) < vExitTime (W y) w → w n ∈ A := hw
    obtain ⟨n, hn, hnB⟩ : ∃ n : ℕ, (n : ℕ∞) < vExitTime (W y) w ∧ w n ∈ D0 \ Aset := by
      by_contra hcon
      have hz : Eq15Walk.occ (W y) (D0 \ Aset) w = 0 := by
        unfold Eq15Walk.occ
        refine ENNReal.tsum_eq_zero.2 fun n => ?_
        split_ifs with h
        · exact (hcon ⟨n, h⟩).elim
        · rfl
      rw [hz] at hpos'
      exact lt_irrefl 0 hpos'
    obtain ⟨_, hnA⟩ := hD (w n) hnB
    exact hnA (hw' n hn)
  have hmeas : MeasurableSet {x : ℕ → ℤ | 0 < Eq15Walk.occ (W y) (D0 \ Aset) x} :=
    measurableSet_lt measurable_const (Eq15Walk.measurable_occ (W y) (D0 \ Aset))
  calc srwLaw m y (stayIn W A y)
      ≤ srwLaw m y {x : ℕ → ℤ | 0 < Eq15Walk.occ (W y) (D0 \ Aset) x}ᶜ := measure_mono hsub
    _ = 1 - srwLaw m y {x : ℕ → ℤ | 0 < Eq15Walk.occ (W y) (D0 \ Aset) x} :=
        prob_compl_eq_one_sub hmeas
    _ ≤ 1 - ENNReal.ofReal (1 / (16 * (2 * C ^ 2 * C1 ^ 2) * L ^ 2)) := tsub_le_tsub_left h15 1

/-- **The printed per-test bound `hc` (LEMMA68 C15-C16), with the logarithmic loss.** With `q0 = 1 / (32 C0² C1² L²)`
the walk started at `y` stays in `A` until exiting `W y` with probability at most `1 - q0 / (1 + log(1/r))²`,
given the second moment bound with constant `C0 (1 + log(1/r))`. This is the shape of the hypothesis `hc` of
`TailBound68.printed68_tail_bound`. -/
theorem stayIn_le_log {m : ℤ → ℤ → ℕ} {y : ℤ} {W : ℤ → Set ℤ} {A : Set ℤ} {D0 Aset : Finset ℤ}
    {ε m0 C0 C1 L Sr e1 s r : ℝ} (hε : 0 < ε) (hm0 : 0 < m0) (hC0 : 0 < C0) (hC1 : 0 < C1) (hL : 0 < L)
    (hr : 0 < r) (hr1 : r ≤ 1) (hS0 : 0 ≤ Sr) (hSm : Sr ≤ C1 * L * m0) (he1 : e1 ≤ m0 / 4) (hs : s ≤ m0 / 4)
    (hS : ε⁻¹ * (m0 - e1) ≤ (D0.card : ℝ)) (hT : (Aset.card : ℝ) ≤ ε⁻¹ * s)
    (hD : ∀ b ∈ D0 \ Aset, b ∈ W y ∧ b ∉ A)
    (hG : ∀ b ∈ D0 \ Aset,
      (1 / 2 : ℝ≥0∞) ≤ ∑' n : ℕ, srwLaw m y {x | (n : ℕ∞) < vExitTime (W y) x ∧ x n = b})
    (hmom : ∫⁻ x, (ENat.toENNReal (vExitTime (W y) x)) ^ 2 ∂(srwLaw m y) ≤
      ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2)) :
    srwLaw m y (stayIn W A y) ≤
      ENNReal.ofReal (1 - (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2) := by
  have hl : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hpos : 0 < 1 + Real.log (1 / r) := by linarith
  have hC : 0 < C0 * (1 + Real.log (1 / r)) := mul_pos hC0 hpos
  have h := stayIn_le_of_eq15 (m := m) (y := y) (W := W) (A := A) (D0 := D0) (Aset := Aset) hε hm0 hC hC1 hL
    hS0 hSm he1 hs hS hT hD hG hmom
  have hne : (1 + Real.log (1 / r)) ≠ 0 := hpos.ne'
  have hq : 1 / (16 * (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * C1 ^ 2) * L ^ 2) =
      (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2 := by
    field_simp
    ring
  have hq0 : 0 ≤ (1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2)) / (1 + Real.log (1 / r)) ^ 2 := by
    have h1 : 0 ≤ 1 / (32 * C0 ^ 2 * C1 ^ 2 * L ^ 2) := by positivity
    exact div_nonneg h1 (sq_nonneg _)
  rw [hq] at h
  rw [ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one]
  exact h

end TestBound68

end MatedCRT

#print axioms MatedCRT.TestBound68.stayIn_le_of_eq15
#print axioms MatedCRT.TestBound68.stayIn_le_log
