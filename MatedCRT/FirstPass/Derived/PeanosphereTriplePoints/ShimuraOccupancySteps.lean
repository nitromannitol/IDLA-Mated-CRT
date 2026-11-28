import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyPaths

/-!
# The occupation of a later cell in Shimura's argument: the three steps

`ShimuraOccupancy γ` (`ShimuraSteps.lean`; Shimura (4.2)–(4.7), pp. 174–176; the written answer to the question on
Shimura's theorem, §2, (2) and (3)) follows from three statements on the cell `I_k = [(k - 1)/n, k/n]`, the drop
`U_k = R(k/n) - min_{I_k} R` of the second coordinate across it (`cellDropR`), the past event
`C_k` (`pastEvent`: the left test at `k` holds and every earlier cell fails its tests truncated at `k/n`, Lemma B,
`mem_firstCellEvent_iff`) and the event `F` that both drops across `I_k` are at most `√d`, `d = (j - 1)/n`
(`tameEvent`):

* `OccupancyUpper γ` (answer (2)): `P(B_k) ≤ K E[1_{C_k ∩ F} U_k] + P(Fᶜ)`; on `C_k` the right test at `k` asks the
  future of `R` after `k/n` to stay above `-U_k`, which has probability at most a constant times `U_k` by the
  reflection barrier.
* `OccupancyLower γ` (answer (3)): `P(B_k ∩ A_{k+j}) ≥ c/(j - 1) · E[1_{C_k ∩ F} U_k]` for `1 + 6 log n < j`, from
  Shimura's Lemma 2 on the gap `[k/n, (k + j - 1)/n]`, a polygonal tube on the cell `k + j` and the survival of `R`
  after it.
* `OccupancyTails γ` (answer §2, before (2)): `P(Fᶜ) ≤ 4/n³` for `1 + 6 log n < j`.

`shimuraOccupancy_of_steps` combines them: for `P(B_k) ≥ 2/n²` and `n ≥ 4`, `P(Fᶜ) ≤ P(B_k)/2`, so
`E[1_{C_k ∩ F} U_k] ≥ P(B_k)/(2K)`.
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2)
open scoped ENNReal NNReal

namespace MatedCRT.PeanosphereTriplePoints

/-- The drop `R(k/n) - min_{[(k - 1)/n, k/n]} R` of the second coordinate across the cell `k` at mesh `1/n`. -/
noncomputable def cellDropR (n k : ℕ) (p : Path2) : ℝ :=
  ⨆ s : Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n), ((p ((k : ℝ) / n)).2 - (p s).2)

/-- The drop `L(k/n) - min_{[(k - 1)/n, k/n]} L` of the first coordinate across the cell `k` at mesh `1/n`. -/
noncomputable def cellDropL (n k : ℕ) (p : Path2) : ℝ :=
  ⨆ s : Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n), ((p ((k : ℝ) / n)).1 - (p s).1)

/-- The past event `C_k`: the left test at `k` holds and every earlier cell fails its left test or its right test
truncated at `k/n`. -/
def pastEvent (n k : ℕ) : Set Path2 :=
  {p | priorCellsFail n k (fun t => (p t).1) (fun t => (p t).2)}

/-- The event `F` that both drops across the cell `k` are at most `√((j - 1)/n)`. -/
def tameEvent (n k j : ℕ) : Set Path2 :=
  {p | cellDropR n k p ≤ Real.sqrt (((j : ℝ) - 1) / n) ∧ cellDropL n k p ≤ Real.sqrt (((j : ℝ) - 1) / n)}

/-- **The tails of the drops** (answer §2): `P(Fᶜ) ≤ 4/n³` for `1 + 6 log n < j`. -/
def OccupancyTails (γ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ n : ℕ, N ≤ n → ∀ k j : ℕ, 1 ≤ k → k + j ≤ 2 * n →
    1 + 6 * Real.log n < j → μ (tameEvent n k j)ᶜ ≤ ENNReal.ofReal (4 / (n : ℝ) ^ 3)

/-- **The upper bound** (answer (2)): `P(B_k) ≤ K E[1_{C_k ∩ F} U_k] + P(Fᶜ)`. -/
def OccupancyUpper (γ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ n : ℕ, N ≤ n →
    ∀ k j : ℕ, 1 ≤ k → k ≤ n → 2 ≤ j → k + j ≤ 2 * n →
      μ (firstCellEvent n k) ≤
        ENNReal.ofReal K * ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ +
          μ (tameEvent n k j)ᶜ

/-- **The lower bound** (answer (3)): `P(B_k ∩ A_{k+j}) ≥ c/(j - 1) · E[1_{C_k ∩ F} U_k]` for `1 + 6 log n < j`. -/
def OccupancyLower (γ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ n : ℕ, N ≤ n →
    ∀ k j : ℕ, 1 ≤ k → k ≤ n → 1 + 6 * Real.log n < j → k + j ≤ 2 * n →
      ENNReal.ofReal (c / ((j : ℝ) - 1)) *
          ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ ≤
        μ (firstCellEvent n k ∩ cellEvent n (k + j))

/-- **The occupation of a later cell from the three steps.** -/
theorem shimuraOccupancy_of_steps {γ : ℝ} (hU : OccupancyUpper γ) (hL : OccupancyLower γ)
    (hT : OccupancyTails γ) : ShimuraOccupancy γ := by
  obtain ⟨K, hK, NU, hU⟩ := hU
  obtain ⟨c, hc, NL, hL⟩ := hL
  obtain ⟨NT, hT⟩ := hT
  refine ⟨c / (2 * K), by positivity, max (max NU NL) (max NT 4), fun μ hμ n hn k j hk1 hkn hp hj hkj => ?_⟩
  have hNU : NU ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hNL : NL ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hNT : NT ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have h4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast h4
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hj2 : 2 ≤ j := by
    have : (1 : ℝ) < j := by linarith
    exact_mod_cast this
  have hjR : (1 : ℝ) < j := by exact_mod_cast hj2
  set I := ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ with hIdef
  set B := μ (firstCellEvent n k) with hBdef
  have hBtop : B ≠ ⊤ := by
    have := hμ.isProbabilityMeasure
    exact measure_ne_top μ _
  -- the tails are at most half of `P(B_k)`
  have h2 : ENNReal.ofReal (2 / (n : ℝ) ^ 2) / 2 = ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by rw [ENNReal.ofReal_ofNat], ← ENNReal.ofReal_div_of_pos two_pos]
    congr 1
    field_simp
  have htail : μ (tameEvent n k j)ᶜ ≤ B / 2 := by
    refine (hT μ hμ n hNT k j hk1 hkj hj).trans (le_trans ?_ (ENNReal.div_le_div_right hp 2))
    rw [h2]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (n : ℝ)]
  -- hence `P(B_k) / 2 ≤ K I`
  have hupper := hU μ hμ n hNU k j hk1 hkn hj2 hkj
  have hhalf : B / 2 ≤ ENNReal.ofReal K * I := by
    have h1 : B ≤ ENNReal.ofReal K * I + B / 2 := hupper.trans (add_le_add le_rfl htail)
    have hB2 : B / 2 ≠ ⊤ := ENNReal.div_ne_top hBtop two_ne_zero
    have h3 : B / 2 + B / 2 ≤ ENNReal.ofReal K * I + B / 2 := by rwa [ENNReal.add_halves]
    exact (ENNReal.add_le_add_iff_right hB2).1 h3
  have hBle : B ≤ ENNReal.ofReal (2 * K) * I := by
    calc B = B / 2 + B / 2 := (ENNReal.add_halves B).symm
      _ = 2 * (B / 2) := (two_mul _).symm
      _ ≤ 2 * (ENNReal.ofReal K * I) := by gcongr
      _ = ENNReal.ofReal (2 * K) * I := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
  have hlower := hL μ hμ n hNL k j hk1 hkn hj hkj
  -- combine
  have hjpos : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  calc ENNReal.ofReal (c / (2 * K) / ((j : ℝ) - 1)) * B
      ≤ ENNReal.ofReal (c / (2 * K) / ((j : ℝ) - 1)) * (ENNReal.ofReal (2 * K) * I) := by gcongr
    _ = ENNReal.ofReal (c / ((j : ℝ) - 1)) * I := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
    _ ≤ μ (firstCellEvent n k ∩ cellEvent n (k + j)) := hlower

end MatedCRT.PeanosphereTriplePoints
