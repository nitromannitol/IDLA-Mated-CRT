import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockJointLimit

/-!
# Lemma 3.4 (item 3): the inverse of a clock sampled at rational times

`ratClockInv L u = inf {q ∈ ℚ≥0 : u < L q}` (in `ℝ≥0∞`) is the inverse of a clock `L` known at rational times. It is
jointly measurable in `(p, u)` whenever `p ↦ L p q` is measurable for each rational `q` (no continuity needed), and for
a continuous strictly increasing unbounded clock `f` with `L = f` on `ℚ≥0` it equals the clock inverse
`clockInverse f u` of Liouville Brownian motion (`Harmonic-Balls-LQG`, `Defs/LBM.lean`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The inverse of a clock sampled at rational times: `ratClockInv L u = inf {q ∈ ℚ≥0 : u < L q}` in `ℝ≥0∞`. -/
noncomputable def ratClockInv (L : ℚ≥0 → ℝ) (u : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (q : ℚ≥0) (_ : (u : ℝ) < L q), (q : ℝ≥0∞)

/-- Density of the rational nonnegative numbers in `ℝ≥0`. -/
lemma exists_nnrat_between {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b :=
  DenseTime.exists_cast_btwn h

/-- **Rational inverse of a clock.** If `f` is continuous and unbounded above, and `L` agrees with `f` at
rational times, then the rational inverse of `L` is the clock inverse `clockInverse f` (the right-continuous inverse
`inf {s | u < f s}` of Berestycki 2015, eq. (2)). -/
theorem ratClockInv_eq_clockInverse {f : ℝ≥0 → ℝ} (hcont : Continuous f)
    (hunb : ∀ M : ℝ, ∃ s : ℝ≥0, M < f s) {L : ℚ≥0 → ℝ} (hL : ∀ q : ℚ≥0, L q = f q) (u : ℝ≥0) :
    ratClockInv L u = (clockInverse f u : ℝ≥0∞) := by
  set S : Set ℝ≥0 := {s | (u : ℝ) < f s} with hS
  have hSne : S.Nonempty := by
    obtain ⟨s, hs⟩ := hunb u
    exact ⟨s, hs⟩
  have hclock : clockInverse f u = sInf S := rfl
  rw [hclock]
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hlt : sInf S < sInf S + ε := lt_add_of_pos_right _ hε
    obtain ⟨s, hsS, hs⟩ := exists_lt_of_csInf_lt hSne hlt
    have hopen : IsOpen {x : ℝ≥0 | (u : ℝ) < f x} := isOpen_lt continuous_const hcont
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen s hsS
    have hδ' : (0 : ℝ≥0) < δ.toNNReal := Real.toNNReal_pos.2 hδ
    have hm : s < min (s + δ.toNNReal) (sInf S + ε) := lt_min (lt_add_of_pos_right _ hδ') hs
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_between hm
    have hq3 : (q : ℝ≥0) < s + δ.toNNReal := lt_of_lt_of_le hq2 (min_le_left _ _)
    have hd : dist (q : ℝ≥0) s < δ := by
      rw [NNReal.dist_eq, abs_lt]
      have h1 : (s : ℝ) < ((q : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 hq1
      have h2 : ((q : ℝ≥0) : ℝ) < (s : ℝ) + δ := by
        have h3 := NNReal.coe_lt_coe.2 hq3
        rw [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at h3
        exact h3
      constructor <;> linarith
    have hqmem : (u : ℝ) < L q := by
      rw [hL q]
      exact hball (Metric.mem_ball.2 hd)
    calc ratClockInv L u ≤ (q : ℝ≥0∞) := iInf₂_le q hqmem
      _ ≤ ((sInf S + ε : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.2 (le_of_lt (lt_of_lt_of_le hq2 (min_le_right _ _)))
      _ = ((sInf S : ℝ≥0) : ℝ≥0∞) + ((ε : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_add _ _
  · refine le_iInf₂ fun q hq => ?_
    have hqS : (q : ℝ≥0) ∈ S := by
      show (u : ℝ) < f (q : ℝ≥0)
      rw [← hL q]
      exact hq
    exact ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow S) hqS)

/-- **Joint measurability of the rational inverse** in the clock and the time: if `p ↦ L p q` is measurable for every
rational `q`, then `(p, u) ↦ ratClockInv (L p) u` is measurable. -/
theorem measurable_ratClockInv {β : Type*} [MeasurableSpace β] {L : β → ℚ≥0 → ℝ}
    (hL : ∀ q : ℚ≥0, Measurable fun p => L p q) :
    Measurable fun x : β × ℝ≥0 => ratClockInv (L x.1) x.2 := by
  unfold ratClockInv
  refine Measurable.iInf fun q => ?_
  have hu : Measurable fun x : β × ℝ≥0 => (x.2 : ℝ) :=
    measurable_snd.coe_nnreal_real
  have hset : MeasurableSet {x : β × ℝ≥0 | (x.2 : ℝ) < L x.1 q} :=
    measurableSet_lt hu ((hL q).comp measurable_fst)
  have hfun : (fun x : β × ℝ≥0 => ⨅ (_ : (x.2 : ℝ) < L x.1 q), (q : ℝ≥0∞)) =
      fun x => if (x.2 : ℝ) < L x.1 q then (q : ℝ≥0∞) else ⊤ := by
    funext x
    by_cases h : (x.2 : ℝ) < L x.1 q
    · rw [iInf_pos h]; simp [h]
    · rw [iInf_neg h]; simp [h]
  rw [hfun]
  exact Measurable.ite hset measurable_const measurable_const

end MatedCRT
