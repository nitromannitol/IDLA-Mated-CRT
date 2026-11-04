import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Annulus

/-!
# Lemma 6.8, Steps 2-4: the walk from `b` hits `𝔈 = V^ε(B') \ A` before exiting `B'` (lines 2537-2620)

`prob_hit_lower`: with `W = V^ε(B') \ V^ε(∂B')` and `E' ⊆ W \ A` finite with `G_W(b, b') ≥ 1/2` for `b' ∈ E'`
(Step 3, Lemma 2.16 and eq:choice-of-constant-annulus), the expected number of visits to `W \ A` before `τ_W` is at
least `|E'|/2`. If `|E'|/2 ≥ c M` (Step 3, Lemma 2.9 and the assumption on `A`) and `E[τ_W²] ≤ K M²` (Step 4), the
second moment method gives `P[the walk visits W \ A before τ_W] ≥ c²/K`.
`prob_stay_le`: if moreover `W ⊆ U`, the walk stays in `A` until it exits `U` with probability at most `1 - c²/K`.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

namespace ConstantOrderDiv

/-- `E[V] ≥ |E'|/2`: the expected number of visits to `W \ A` before `τ_W` is at least half the number of vertices
`b' ∈ E' ⊆ W \ A` with `G_W(b, b') ≥ 1/2`. -/
theorem ofReal_ncard_half_le {m : ℤ → ℤ → ℕ} {W A E' : Set ℤ} {b : ℤ} (hE' : E' ⊆ W \ A) (hfin : E'.Finite)
    (hG : ∀ b' ∈ E', (1 / 2 : ℝ) ≤ greenFn m W b b') :
    ENNReal.ofReal ((E'.ncard : ℝ) / 2) ≤
      ∑' b' : (W \ A : Set ℤ), ∫⁻ x, visitsBeforeExit W b' x ∂srwLaw m b := by
  set f : ℤ → ℝ≥0∞ := fun b' => ∫⁻ x, visitsBeforeExit W b' x ∂srwLaw m b with hf
  rw [tsum_subtype (W \ A) f]
  calc ENNReal.ofReal ((E'.ncard : ℝ) / 2) = ∑ _b' ∈ hfin.toFinset, ENNReal.ofReal (1 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card E' hfin, div_eq_mul_one_div,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ∑ b' ∈ hfin.toFinset, (W \ A).indicator f b' := by
        refine Finset.sum_le_sum fun b' hb' => ?_
        have hb'E : b' ∈ E' := hfin.mem_toFinset.1 hb'
        rw [indicator_of_mem (hE' hb'E)]
        exact (ENNReal.ofReal_le_ofReal (hG b' hb'E)).trans ENNReal.ofReal_toReal_le
    _ ≤ ∑' b', (W \ A).indicator f b' := ENNReal.sum_le_tsum _

/-- **Steps 2-4** (lines 2537-2620): the walk from `b` visits `W \ A` before `τ_W` with probability at least
`c²/K`. -/
theorem prob_hit_lower {m : ℤ → ℤ → ℕ} {W A E' : Set ℤ} {b : ℤ} (hE' : E' ⊆ W \ A) (hfin : E'.Finite)
    (hG : ∀ b' ∈ E', (1 / 2 : ℝ) ≤ greenFn m W b b') {M : ℝ≥0∞} {c K : ℝ} (hc : 0 ≤ c) (hK : 0 < K)
    (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (hN : ENNReal.ofReal c * M ≤ ENNReal.ofReal ((E'.ncard : ℝ) / 2))
    (hY : exitTimeMoment m W b 2 ≤ ENNReal.ofReal K * M ^ 2) :
    ENNReal.ofReal (c ^ 2 / K) ≤
      srwLaw m b {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime W x ∧ x n ∈ W \ A} :=
  ofReal_le_of_moments hc hK hM0 hMt (hN.trans (ofReal_ncard_half_le hE' hfin hG)) hY
    (srwVisitSecondMomentStep m W (W \ A) b)

/-- If `W ⊆ U` and the walk visits `W \ A` before `τ_W` with probability at least `p`, it stays in `A` until it
exits `U` with probability at most `1 - p`. -/
theorem prob_stay_le {m : ℤ → ℤ → ℕ} {W U A : Set ℤ} {b : ℤ} (hWU : W ⊆ U) {p : ℝ} (hp : 0 ≤ p)
    (hhit : ENNReal.ofReal p ≤ srwLaw m b {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime W x ∧ x n ∈ W \ A}) :
    srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ ENNReal.ofReal (1 - p) := by
  set H : Set (ℕ → ℤ) := {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime W x ∧ x n ∈ W \ A} with hHdef
  have hH : MeasurableSet H := by
    have : H = ⋃ n : ℕ, {x : ℕ → ℤ | (n : ℕ∞) < vExitTime W x ∧ x n ∈ W \ A} := by
      ext x
      simp [hHdef]
    rw [this]
    exact MeasurableSet.iUnion fun n => measurableSet_visit W (W \ A) n
  have hsub : {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ⊆ Hᶜ := by
    rintro x hx ⟨n, hn, hxW, hxA⟩
    refine hxA (hx n ?_)
    rw [lt_vExitTime_iff'] at hn ⊢
    exact fun j hj => hWU (hn j hj)
  calc srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ srwLaw m b Hᶜ := measure_mono hsub
    _ = 1 - srwLaw m b H := prob_compl_eq_one_sub hH
    _ ≤ 1 - ENNReal.ofReal p := tsub_le_tsub_left hhit 1
    _ = ENNReal.ofReal (1 - p) := by rw [ENNReal.ofReal_sub 1 hp, ENNReal.ofReal_one]

end ConstantOrderDiv

end MatedCRT
