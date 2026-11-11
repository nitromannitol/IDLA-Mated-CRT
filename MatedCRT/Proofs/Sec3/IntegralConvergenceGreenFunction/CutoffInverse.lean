import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseUniform

/-!
# Lemma 3.4: cutoff inverse clocks

The approximate clocks `F_n` of the Liouville clock need not diverge, so their right-continuous inverses may not be
defined on all levels. As in the paper's proof of `LBMPathFunctionalMeasurableStep`, the approximate inverse is cut off
at the level `n`: `cutInv C n t = inf {s ≤ n : t < C s}`, with value `n` when this set is empty. The cutoff inverse
agrees with the true clock inverse whenever `t < C n`, and converges to `clockInverse G` locally uniformly when the
clocks converge locally uniformly to a time-change clock `G`.

Terminology: approximate inverse of the Liouville clock (Garban–Rhodes–Vargas, Liouville Brownian motion, Section 2).
-/

namespace MatedCRT

open Filter Topology Set
open scoped NNReal
open _root_.HarmonicBalls

/-- The cutoff inverse of the clock `C` at level `t`, cut off at the level `n`: the infimum of the times `s ≤ n` with
`t < C s`, and `n` when there is no such time. -/
noncomputable def cutInv (C : ℝ≥0 → ℝ) (n t : ℝ≥0) : ℝ≥0 :=
  sInf ({s | s ≤ n ∧ (t : ℝ) < C s} ∪ {n})

/-- When the level `t` lies below the value of a strictly increasing clock at the cutoff `n`, the cutoff inverse is the
clock inverse. -/
theorem cutInv_eq_clockInverse {C : ℝ≥0 → ℝ} {n t : ℝ≥0} (_hC : StrictMono C) (ht : (t : ℝ) < C n) :
    cutInv C n t = clockInverse C t := by
  unfold cutInv clockInverse
  have hBbdd : BddBelow ({s | s ≤ n ∧ (t : ℝ) < C s} ∪ {n}) := OrderBot.bddBelow _
  have hAbdd : BddBelow {s : ℝ≥0 | (t : ℝ) < C s} := OrderBot.bddBelow _
  have hnA : n ∈ {s : ℝ≥0 | (t : ℝ) < C s} := ht
  have hnB : n ∈ ({s | s ≤ n ∧ (t : ℝ) < C s} ∪ {n} : Set ℝ≥0) := Or.inr rfl
  apply le_antisymm
  · apply le_csInf ⟨n, hnA⟩
    intro s hs
    by_cases hsn : s ≤ n
    · exact csInf_le hBbdd (Or.inl ⟨hsn, hs⟩)
    · exact le_trans (csInf_le hBbdd hnB) (le_of_lt (not_le.1 hsn))
  · apply le_csInf ⟨n, hnB⟩
    intro s hs
    rcases hs with ⟨hsn, hs⟩ | hs
    · exact csInf_le hAbdd hs
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact csInf_le hAbdd hnA

/-- When the level `t` reaches the value of the clock at the cutoff, the cutoff inverse is the cutoff `n`. -/
theorem cutInv_eq_of_le {C : ℝ≥0 → ℝ} {n t : ℝ≥0} (hC : Monotone C) (ht : C n ≤ (t : ℝ)) :
    cutInv C n t = n := by
  unfold cutInv
  have hsub : ({s | s ≤ n ∧ (t : ℝ) < C s} ∪ {n} : Set ℝ≥0) = {n} := by
    ext s
    constructor
    · rintro (⟨hsn, hs⟩ | hs)
      · exact absurd (lt_of_lt_of_le hs (hC hsn)) (not_lt.2 ht)
      · exact hs
    · intro hs
      exact Or.inr hs
  rw [hsub, csInf_singleton]

/-- **Locally uniform convergence of the cutoff inverses.** If the clocks `F n` are strictly increasing and converge
uniformly on compact time intervals to a time-change clock `G`, the cutoff inverses at the levels `n` converge
uniformly on compact level intervals to `clockInverse G`. -/
theorem cutInv_tendsto_uniform {F : ℕ → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ} (hG : IsTimeChangeClock G)
    (hF : ∀ n, StrictMono (F n))
    (hconv : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t ≤ T, |F n t - G t| < η)
    (U : ℝ≥0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ u ≤ U,
      |((cutInv (F n) (n : ℝ≥0) u : ℝ≥0) : ℝ) - ((clockInverse G u : ℝ≥0) : ℝ)| < η := by
  -- a level `s₀` where the limit clock exceeds `U + 1`
  obtain ⟨s₀, hs₀⟩ := (hG.tendsto_atTop.eventually_gt_atTop ((U : ℝ) + 1)).exists
  -- eventually the clocks exceed `U` at their own cutoff
  have hbig : ∀ᶠ n : ℕ in atTop, (U : ℝ) < F n (n : ℝ≥0) := by
    filter_upwards [hconv s₀ 1 one_pos, eventually_ge_atTop ⌈s₀⌉₊] with n hn hnn
    have h1 := abs_lt.1 (hn s₀ le_rfl)
    have hsn : s₀ ≤ (n : ℝ≥0) := le_trans (Nat.le_ceil s₀) (by exact_mod_cast hnn)
    have h2 : F n s₀ ≤ F n (n : ℝ≥0) := (hF n).monotone hsn
    linarith [h1.1]
  have hunb : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ≥0, u ≤ U → ∃ s : ℝ≥0, (u : ℝ) < F n s := by
    filter_upwards [hbig] with n hn u hu
    exact ⟨(n : ℝ≥0), lt_of_le_of_lt (by exact_mod_cast hu) hn⟩
  filter_upwards [clockInverse_tendsto_uniform hG hF U hunb hconv η hη, hbig] with n hn hb u hu
  have hu' : (u : ℝ) < F n (n : ℝ≥0) := lt_of_le_of_lt (by exact_mod_cast hu) hb
  rw [cutInv_eq_clockInverse (hF n) hu']
  exact hn u hu

end MatedCRT
