import MatedCRT.FirstPass.Derived.BlockExitSkeletonProkhorov
import MatedCRT.FirstPass.Derived.BrownianBlockExitReachGoodStop

/-!
# The stopped-path comparison from block-exit data: choice of the block parameters

`exists_blockExit_parameters_allSet_le` combines the stopped-path comparison from a one-sided Prokhorov bound for the
block-exit skeletons (`measure_stopAtExit_le_of_prokhorovLE_of_transferLemma`) with the Brownian side
(`exists_planarBrownianMotion_reach_and_goodStop_compl_le`, uniform in the start in `closedBall 0 ρ`).  For `0 ≤ ρ < R`
and `κ > 0` it chooses, independently of the process `W`, the block size `s`, the far-set width `d'`, the closeness
`δ₀` and the number of blocks `N` such that the following holds: if the law of the block-exit positions of `W` is
`(δ, e)`-Prokhorov-close to that of planar Brownian motion started at `x₀ ∈ closedBall 0 ρ` with `δ ≤ δ₀`,
`e ≤ κ / 4`, if `W` reaches the far set within `N` blocks outside an event of probability at most `κ / 8`, and if
the general transfer lemma of the skeleton comparison holds (as the explicit hypothesis `hLP`), then the stopped path
of `W` at the exit from `ball 0 R` satisfies the all-set inequality against Brownian motion with tolerance `κ`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open LatticeProb MatedCRT.StopAtExitCmp

universe u

/-- **Choice of the block parameters for the stopped-path comparison.** -/
theorem exists_blockExit_parameters_allSet_le {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (s d' δ₀ : ℝ) (N : ℕ), 0 < s ∧ 0 < d' ∧ 0 < δ₀ ∧
      ∀ {Ω₁ : Type u} [MeasurableSpace Ω₁] (μ : Measure Ω₁) (W : Ω₁ → ContinuousPath ℂ), Measurable W →
        ∀ x₀ ∈ closedBall (0 : ℂ) ρ, ∀ {δ e : ℝ}, 0 ≤ δ → δ ≤ δ₀ → e ≤ κ / 4 →
        ProkhorovLE (μ.map fun ω => blockExitPositions s (farSet (ball (0 : ℂ) R) d') N (W ω))
          ((planarBrownianMotion x₀).map
            fun b => blockExitPositions s (farSet (ball (0 : ℂ) R) d') N b) δ e →
        μ {ω | ∃ n ≤ N, W ω (blockExitTimes s (farSet (ball (0 : ℂ) R) d') n (W ω)) ∈
            farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 8) →
        ((∀ x y z : ℝ≥0 → ℂ, cmpEDist x z ≤ cmpEDist x y + cmpEDist y z) →
          (∀ x x' : Fin (N + 1) → ℂ, cmpEDist (stepPath N x) (stepPath N x') ≤ edist x x') →
          ∀ {H₁ : Ω₁ → Fin (N + 1) → ℂ} {H₂ : ContinuousPath ℂ → Fin (N + 1) → ℂ}, Measurable H₁ →
          Measurable H₂ → ∀ {δ e a a' : ℝ}, 0 ≤ a → 0 ≤ a' → 0 ≤ δ →
          ProkhorovLE (μ.map H₁) ((planarBrownianMotion x₀).map H₂) δ e →
          ∀ {P₁ : Ω₁ → ℝ≥0 → ℂ} {P₂ : ContinuousPath ℂ → ℝ≥0 → ℂ} {G₁ : Set Ω₁} {G₂ : Set (ContinuousPath ℂ)},
          (∀ ω ∈ G₁, cmpEDist (stepPath N (H₁ ω)) (P₁ ω) < ENNReal.ofReal a) →
          (∀ ω ∈ G₂, cmpEDist (P₂ ω) (stepPath N (H₂ ω)) < ENNReal.ofReal a') →
          ∀ A : Set (ℝ≥0 → ℂ), μ (P₁ ⁻¹' A) ≤
            planarBrownianMotion x₀ {ω | ∃ f ∈ A, cmpEDist (P₂ ω) f < ENNReal.ofReal (a' + δ + a)} +
              ENNReal.ofReal e + μ G₁ᶜ + planarBrownianMotion x₀ G₂ᶜ) →
        ∀ A : Set (ℝ≥0 → ℂ),
          μ {ω | stopAtExit (ball (0 : ℂ) R) (W ω) ∈ A} ≤
            planarBrownianMotion x₀
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ := by
  obtain ⟨T, η, d, C, hη, hd, hBM⟩ := exists_planarBrownianMotion_reach_and_goodStop_compl_le hρ hρR
    (ε := κ / 4) (θ := κ / 32) (by linarith) (by linarith) (ζ := 1 / 2) (by norm_num) (by norm_num) 1
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  set d' : ℝ := d / 2 with hd'def
  have hd' : 0 < d' := by positivity
  set m : ℝ := min (κ / 4) d' with hmdef
  have hm : 0 < m := lt_min (by linarith) hd'
  have hmκ : m ≤ κ / 4 := min_le_left _ _
  have hmd : m ≤ d' := min_le_right _ _
  set s : ℝ := m / 32 with hsdef
  have hs : 0 < s := by positivity
  set K : ℝ := 4 * (R + d' + ρ + 4 * s + 1) with hKdef
  have hK : 0 < K := by positivity
  set r : ℝ := min (1 / 2) (min (s / K) (κ / (32 * (|C| + 1)))) with hrdef
  have hr0 : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hrs : r ≤ s / K := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrC : r ≤ κ / (32 * (|C| + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hars : 4 * ((R + d' + ρ + 4 * s + 1) * r) ≤ s := by
    have : r * K ≤ s := by rwa [le_div_iff₀ hK] at hrs
    nlinarith
  have hCr : C * r ^ 1 ≤ κ / 32 := by
    rw [pow_one]
    calc C * r ≤ |C| * r := mul_le_mul_of_nonneg_right (le_abs_self C) hr0.le
      _ ≤ |C| * (κ / (32 * (|C| + 1))) := by gcongr
      _ = (κ / 32) * (|C| / (|C| + 1)) := by field_simp
      _ ≤ (κ / 32) * 1 := by
        gcongr
        exact (div_le_one (by positivity)).2 (by linarith)
      _ = κ / 32 := mul_one _
  refine ⟨s, d', m / 4, ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊, hs, hd', by positivity, ?_⟩
  intro Ω₁ _ μ W hW x₀ hx₀ δ e hδ0 hδ he hP hreach hLP A
  have hdd : 4 * s + d' ≤ d := by
    have : 4 * s ≤ d' / 8 := by rw [hsdef]; have := hmd; linarith
    have : d' = d / 2 := hd'def
    linarith
  have hr' : 9 * s + δ + 9 * s ≤ min (κ / 4) d' := by
    have : δ ≤ m / 4 := hδ
    rw [← hmdef, hsdef]; linarith
  have key := measure_stopAtExit_le_of_prokhorovLE_of_transferLemma μ (planarBrownianMotion x₀) W
    (fun b => b) hW measurable_id (s := s) hs (U := ball (0 : ℂ) R) (T := T) (η := η) (d := d) (d' := d')
    (ε := κ / 4) (κ := κ) (δ := δ) (e := e) (a := 9 * s) (a' := 9 * s) hη hd' hdd (N := ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊)
    (by linarith) hκ hr' (by linarith) (by linarith) hδ0 hP hLP A
  have hB := hBM (d' := d') hd' x₀ hx₀ s hs r hr0 hr1 hars ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊ (Nat.le_succ _)
  refine le_trans key ?_
  have h1 : ENNReal.ofReal e ≤ ENNReal.ofReal (κ / 4) := ENNReal.ofReal_le_ofReal he
  have h2 : 2 * μ {ω | ∃ n ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊, W ω (blockExitTimes s (farSet (ball (0 : ℂ) R) d') n (W ω)) ∈
      farSet (ball (0 : ℂ) R) d'}ᶜ ≤ ENNReal.ofReal (κ / 4) := by
    calc _ ≤ 2 * ENNReal.ofReal (κ / 8) := by gcongr
      _ = ENNReal.ofReal (κ / 4) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
  have h3 : 2 * planarBrownianMotion x₀
      {ω : ContinuousPath ℂ | (∃ n ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊,
        ω (blockExitTimes s (farSet (ball (0 : ℂ) R) d') n ω) ∈ farSet (ball (0 : ℂ) R) d') ∧
        GoodStop (ball (0 : ℂ) R) T η d (κ / 4) ω}ᶜ ≤
      ENNReal.ofReal (κ / 8) := by
    calc _ ≤ 2 * (ENNReal.ofReal (C * r ^ 1) + ENNReal.ofReal (κ / 32)) := by gcongr
      _ ≤ 2 * (ENNReal.ofReal (κ / 32) + ENNReal.ofReal (κ / 32)) := by
          gcongr
      _ = ENNReal.ofReal (κ / 8) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
  have hsum : ENNReal.ofReal (κ / 4) + ENNReal.ofReal (κ / 4) + ENNReal.ofReal (κ / 8) ≤
      ENNReal.ofReal κ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc _ ≤ planarBrownianMotion x₀
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal (κ / 4) + ENNReal.ofReal (κ / 4) + ENNReal.ofReal (κ / 8) :=
        add_le_add (add_le_add (add_le_add le_rfl h1) h2) h3
    _ = planarBrownianMotion x₀
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        (ENNReal.ofReal (κ / 4) + ENNReal.ofReal (κ / 4) + ENNReal.ofReal (κ / 8)) := by ring
    _ ≤ _ := add_le_add le_rfl hsum

end BlockExit

end MatedCRT
