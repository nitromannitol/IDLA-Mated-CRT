import MatedCRT.FirstPass.Derived.BlockExitSkeletonProkhorovSandwich
import MatedCRT.FirstPass.Derived.BrownianBlockExitReachGoodStopSandwich

/-!
# The stopped-path comparison from block-exit data: block parameters for a sandwiched frozen set

`exists_blockExit_parameters_allSet_le_sandwich` is `exists_blockExit_parameters_allSet_le` for a
block-exit chain frozen on a measurable set `F` with
`farSet (ball 0 R) d₁ ⊆ F ⊆ farSet (ball 0 R) d'` instead of `F = farSet (ball 0 R) d'`. The block
size `s`, the widths `d' < d₁ = d' + 2 s`, the closeness `δ₀` and the number of blocks `N` are
chosen independently of `F` and of the process `W`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open LatticeProb MatedCRT.StopAtExitCmp

universe u

/-- **Choice of the block parameters for the stopped-path comparison, sandwiched frozen set.** The
parameters `s, d', d₁, δ₀, N` do not depend on the frozen set `F`, which ranges over the measurable
sets with `farSet (ball 0 R) d₁ ⊆ F ⊆ farSet (ball 0 R) d'`. -/
theorem exists_blockExit_parameters_allSet_le_sandwich {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ)
    (g : ℝ → ℝ → ℕ) :
    ∃ (s d' d₁ δ₀ : ℝ) (N : ℕ), 0 < s ∧ 0 < d' ∧ d' + 2 * s ≤ d₁ ∧ 0 < δ₀ ∧ g s d' ≤ N ∧
      ∀ {F : Set ℂ}, MeasurableSet F → farSet (ball (0 : ℂ) R) d₁ ⊆ F →
      F ⊆ farSet (ball (0 : ℂ) R) d' →
      (∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ N, b (blockExitTimes s F j b) ∈
          F}ᶜ ≤ ENNReal.ofReal (κ / 16)) ∧
      ∀ {Ω₁ : Type u} [MeasurableSpace Ω₁] (μ : Measure Ω₁) (W : Ω₁ → ContinuousPath ℂ), Measurable W →
        ∀ x₀ ∈ closedBall (0 : ℂ) ρ, ∀ {δ e : ℝ}, 0 ≤ δ → δ ≤ δ₀ → e ≤ κ / 4 →
        ProkhorovLE (μ.map fun ω => blockExitPositions s F N (W ω))
          ((planarBrownianMotion x₀).map
            fun b => blockExitPositions s F N b) δ e →
        μ {ω | ∃ n ≤ N, W ω (blockExitTimes s F n (W ω)) ∈
            F}ᶜ ≤ ENNReal.ofReal (κ / 8) →
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
  obtain ⟨T, η, d, C, hη, hd, hBM⟩ := exists_planarBrownianMotion_reach_and_goodStop_compl_le_sandwich
    hρ hρR (ε := κ / 4) (θ := κ / 32) (by linarith) (by linarith) (ζ := 1 / 2) (by norm_num)
    (by norm_num) 1
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  set d' : ℝ := d / 2 with hd'def
  have hd' : 0 < d' := by positivity
  set m : ℝ := min (κ / 4) d' with hmdef
  have hm : 0 < m := lt_min (by linarith) hd'
  have hmκ : m ≤ κ / 4 := min_le_left _ _
  have hmd : m ≤ d' := min_le_right _ _
  set s : ℝ := m / 32 with hsdef
  have hs : 0 < s := by positivity
  set d₁ : ℝ := d' + 2 * s with hd₁def
  have hd₁ : 0 < d₁ := by positivity
  set K : ℝ := 4 * (R + d₁ + ρ + 4 * s + 1) with hKdef
  have hK : 0 < K := by positivity
  set r : ℝ := min (1 / 2) (min (s / K) (min (κ / (32 * (|C| + 1))) (1 / ((g s d' : ℝ) + 2)))) with hrdef
  have hr0 : 0 < r :=
    lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hrs : r ≤ s / K := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrC : r ≤ κ / (32 * (|C| + 1)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrg : r ≤ 1 / ((g s d' : ℝ) + 2) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hgN : g s d' ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : r ^ (2 + (1 / 2 : ℝ)) ≤ r ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le (by norm_num)
    rw [Real.rpow_one] at h1
    have h2 : r⁻¹ ≤ (r ^ (2 + (1 / 2 : ℝ)))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hr0 _) h1
    have h3 : (g s d' : ℝ) + 2 ≤ r⁻¹ := by
      rw [← one_div, le_div_iff₀ hr0]
      have h4 := (le_div_iff₀ (by positivity : (0 : ℝ) < (g s d' : ℝ) + 2)).1 hrg
      linarith
    rw [Real.rpow_neg hr0.le]
    linarith
  have hars : 4 * ((R + d₁ + ρ + 4 * s + 1) * r) ≤ s := by
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
  refine ⟨s, d', d₁, m / 4, ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊, hs, hd', le_rfl, by positivity, hgN, ?_⟩
  intro F hFm hF₁ hF₂
  have hguard : ∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z
        {b : ContinuousPath ℂ | ∃ j ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊,
          b (blockExitTimes s F j b) ∈ F}ᶜ ≤ ENNReal.ofReal (κ / 16) := by
    intro z hz
    have hB0 := hBM (d₁ := d₁) hd₁ hF₁ z hz s hs r hr0 hr1 hars ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊
      (Nat.le_succ _)
    have hsub : {b : ContinuousPath ℂ | ∃ j ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊,
          b (blockExitTimes s F j b) ∈ F}ᶜ ⊆
        {ω : ContinuousPath ℂ | (∃ n ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊,
          ω (blockExitTimes s F n ω) ∈ F) ∧
          GoodStop (ball (0 : ℂ) R) T η d (κ / 4) ω}ᶜ := fun b hb h => hb h.1
    refine le_trans (le_trans (measure_mono hsub) hB0) ?_
    calc ENNReal.ofReal (C * r ^ 1) + ENNReal.ofReal (κ / 32)
        ≤ ENNReal.ofReal (κ / 32) + ENNReal.ofReal (κ / 32) := by gcongr
      _ = ENNReal.ofReal (κ / 16) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  refine ⟨hguard, ?_⟩
  intro Ω₁ _ μ W hW x₀ hx₀ δ e hδ0 hδ he hP hreach hLP A
  have hd'd : d' ≤ d := by
    have : d' = d / 2 := hd'def
    linarith
  have hdd : 4 * s + d₁ ≤ d := by
    have : 4 * s ≤ d' / 8 := by rw [hsdef]; have := hmd; linarith
    have : d' = d / 2 := hd'def
    have : d₁ = d' + 2 * s := hd₁def
    linarith
  have hr' : 9 * s + δ + 9 * s ≤ min (κ / 4) d' := by
    have : δ ≤ m / 4 := hδ
    rw [← hmdef, hsdef]; linarith
  have key := measure_stopAtExit_le_of_prokhorovLE_of_transferLemma_sandwich μ
    (planarBrownianMotion x₀) W (fun b => b) hW measurable_id (s := s) hs (U := ball (0 : ℂ) R)
    hFm (T := T) (η := η) (d := d) (d₁ := d₁) (d' := d') (ε := κ / 4) (κ := κ) (δ := δ) (e := e)
    (a := 9 * s) (a' := 9 * s) hη hd' hd'd hdd hF₁ hF₂ (N := ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊)
    (by linarith) hκ hr' (by linarith) (by linarith) hδ0 hP hLP A
  have hB := hBM (d₁ := d₁) hd₁ hF₁ x₀ hx₀ s hs r hr0 hr1 hars
    ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊ (Nat.le_succ _)
  refine le_trans key ?_
  have h1 : ENNReal.ofReal e ≤ ENNReal.ofReal (κ / 4) := ENNReal.ofReal_le_ofReal he
  have h2 : 2 * μ {ω | ∃ n ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊, W ω (blockExitTimes s F n (W ω)) ∈
      F}ᶜ ≤ ENNReal.ofReal (κ / 4) := by
    calc _ ≤ 2 * ENNReal.ofReal (κ / 8) := by gcongr
      _ = ENNReal.ofReal (κ / 4) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
  have h3 : 2 * planarBrownianMotion x₀
      {ω : ContinuousPath ℂ | (∃ n ≤ ⌊r ^ (-(2 + (1 / 2 : ℝ)))⌋₊,
        ω (blockExitTimes s F n ω) ∈ F) ∧
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
