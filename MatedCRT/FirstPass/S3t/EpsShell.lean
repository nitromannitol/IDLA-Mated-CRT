import MatedCRT.FirstPass.S3t.Defs
import MatedCRT.Defs.Notation

/-!
# Truncated quenched laws, Step 12: epsilon-first, shell-width-second

Probability lemmas only: no environment structure is used.

Input shape. `A ε ω`, `C ε ω` are the quenched discrete and stopped occupations; `R n ε ω` is the quenched shell
functional at boundary shell `n` (Step 6); `Rlim n ω` its LBM limit. Step 11 gives, for each `n`, eventually in `ε`,
on the mesh-good event `Good ε ω`: `|A - C| ≤ E ε + M · R n ε ω`, with `E → 0` (Steps 7, 8).

Measure-theoretic input. `Rlim n → 0` almost surely (Step 6) is converted to convergence in probability in `n` using
`AEMeasurable (Rlim n)`. This measurability is not written in the answer; it enters as a hypothesis (see `S3t.lean`).
Without it a.s. convergence does not give convergence of outer probabilities (Bernstein-type counterexample), so it
cannot be dropped.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- Convergence in probability to `0` of `Y n` from almost-sure convergence and a.e.-measurability, for the strict
threshold event `{c < |Y n|}` (Mathlib `tendstoInMeasure_of_tendsto_ae`). -/
theorem tendsto_measure_lt_abs_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hY : ∀ n, AEMeasurable (Y n) P) (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => P {ω | c < |Y n ω|}) atTop (𝓝 0) := by
  have hconv : TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hY n).aestronglyMeasurable) hlim
  have h := hconv (ENNReal.ofReal c) (ENNReal.ofReal_pos.2 hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) (fun n => ?_)
  refine measure_mono fun ω hω => ?_
  have hω' : c < |Y n ω| := hω
  show ENNReal.ofReal c ≤ edist (Y n ω) 0
  rw [edist_dist, Real.dist_eq, sub_zero]
  exact ENNReal.ofReal_le_ofReal hω'.le

/-- **Step 12, abstract form.** Suppose that, for each shell index `n`, eventually in `ε` and on the good event, the
integrated comparison `|A - C| ≤ E + M · R n` holds with `E → 0`; the good events have probability tending to `0`; for
each `n` the shell functional converges in probability to `Rlim n`; and `Rlim n → 0` almost surely with a.e.-measurable
`Rlim n`. Then `A - C → 0` in probability. The proof fixes `n` first (outer limit), then lets `ε → 0`. -/
theorem tendstoInProbability_sub_zero_of_shell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A C : ℝ → Ω → ℝ} {R : ℕ → ℝ → Ω → ℝ} {Rlim : ℕ → Ω → ℝ} {Good : ℝ → Ω → Prop}
    {E : ℝ → ℝ} {M : ℝ} (hM : 0 < M)
    (hpath : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω → |A ε ω - C ε ω| ≤ E ε + M * R n ε ω)
    (hE : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hGood : Tendsto (fun ε => P {ω | ¬ Good ε ω}) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hshell : ∀ n, TendstoInProbability P (R n) (Rlim n))
    (hRmeas : ∀ n, AEMeasurable (Rlim n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Rlim n ω) atTop (𝓝 0)) :
    TendstoInProbability P (fun ε ω => A ε ω - C ε ω) (fun _ => 0) := by
  intro δ hδ
  refine ENNReal.tendsto_nhds_zero.2 fun κ hκ => ?_
  have hκ3 : (0 : ℝ≥0∞) < κ / 3 := ENNReal.div_pos hκ.ne' (by norm_num)
  -- 1. Fix the shell index `n`: the shell limit is small in probability.
  have hlimM : ∀ᵐ ω ∂P, Tendsto (fun n => M * Rlim n ω) atTop (𝓝 0) := by
    filter_upwards [hlim] with ω hω
    simpa using hω.const_mul M
  have hY : Tendsto (fun n => P {ω | δ / 3 < |M * Rlim n ω|}) atTop (𝓝 0) :=
    tendsto_measure_lt_abs_of_ae_tendsto (Y := fun n ω => M * Rlim n ω) (fun n => (hRmeas n).const_mul M)
      hlimM (by positivity)
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hY) (κ / 3) hκ3).exists
  -- 2. With `n` fixed, let `ε → 0`.
  have hS := ENNReal.tendsto_nhds_zero.1 ((hshell n) (δ / (3 * M)) (by positivity)) (κ / 3) hκ3
  have hG := ENNReal.tendsto_nhds_zero.1 hGood (κ / 3) hκ3
  have hEε := hE.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 3))
  filter_upwards [hS, hG, hEε, hpath n] with ε h2 h1 h0 h3
  have hsub : {ω | δ < |A ε ω - C ε ω - 0|} ⊆
      {ω | ¬ Good ε ω} ∪ {ω | δ / (3 * M) < |R n ε ω - Rlim n ω|} ∪ {ω | δ / 3 < |M * Rlim n ω|} := by
    intro ω hω
    have hω0 : δ < |A ε ω - C ε ω - 0| := hω
    rw [sub_zero] at hω0
    by_cases hG' : Good ε ω
    swap
    · exact Or.inl (Or.inl hG')
    by_cases hB2 : δ / (3 * M) < |R n ε ω - Rlim n ω|
    swap
    · by_cases hB3 : δ / 3 < |M * Rlim n ω|
      · exact Or.inr hB3
      · exfalso
        have hb := h3 ω hG'
        have hx : R n ε ω ≤ |R n ε ω - Rlim n ω| + Rlim n ω := by
          linarith [le_abs_self (R n ε ω - Rlim n ω)]
        have hMx : M * R n ε ω ≤ M * |R n ε ω - Rlim n ω| + |M * Rlim n ω| := by
          calc M * R n ε ω ≤ M * (|R n ε ω - Rlim n ω| + Rlim n ω) := mul_le_mul_of_nonneg_left hx hM.le
            _ = M * |R n ε ω - Rlim n ω| + M * Rlim n ω := by ring
            _ ≤ M * |R n ε ω - Rlim n ω| + |M * Rlim n ω| := by linarith [le_abs_self (M * Rlim n ω)]
        have hM2 : M * |R n ε ω - Rlim n ω| ≤ δ / 3 := by
          have hle : |R n ε ω - Rlim n ω| ≤ δ / (3 * M) := le_of_not_gt hB2
          calc M * |R n ε ω - Rlim n ω| ≤ M * (δ / (3 * M)) := mul_le_mul_of_nonneg_left hle hM.le
            _ = δ / 3 := by field_simp
        have hM3 : |M * Rlim n ω| ≤ δ / 3 := le_of_not_gt hB3
        have h0' : E ε < δ / 3 := h0
        linarith
    · exact Or.inl (Or.inr hB2)
  have hcount : P {ω | δ < |A ε ω - C ε ω - 0|} ≤ κ / 3 + κ / 3 + κ / 3 := by
    calc P {ω | δ < |A ε ω - C ε ω - 0|}
        ≤ P ({ω | ¬ Good ε ω} ∪ {ω | δ / (3 * M) < |R n ε ω - Rlim n ω|} ∪ {ω | δ / 3 < |M * Rlim n ω|}) :=
          measure_mono hsub
      _ ≤ P ({ω | ¬ Good ε ω} ∪ {ω | δ / (3 * M) < |R n ε ω - Rlim n ω|}) + P {ω | δ / 3 < |M * Rlim n ω|} :=
          measure_union_le _ _
      _ ≤ (P {ω | ¬ Good ε ω} + P {ω | δ / (3 * M) < |R n ε ω - Rlim n ω|}) + P {ω | δ / 3 < |M * Rlim n ω|} :=
          add_le_add_left (measure_union_le _ _) _
      _ ≤ κ / 3 + κ / 3 + κ / 3 := add_le_add (add_le_add h1 h2) hn
  calc P {ω | δ < |A ε ω - C ε ω - 0|} ≤ κ / 3 + κ / 3 + κ / 3 := hcount
    _ = κ := ENNReal.add_thirds κ

end MatedCRT.TruncatedLaws
