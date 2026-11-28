import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterBase

/-!
# The outer window and the path stopped at a fixed time

Let `x` be a path that stays positive from time `N` on. Then stopping `x` at `N` does not change its
last zero, and, when the window `[ℓ, ℓ + S]` ends before `N`, it does not change the window either
(`pathLastZero_stop`, `outerWindowOfPath_stop`). The event `stoppedWindowEvent N S A` of continuous
paths `z` (read as stopped paths) records that `z N > 0`, that the last zero of `z` is below `N - S`
and that the window of `z` lies in `A`. It is measurable for the Borel σ-algebra of `C(ℝ≥0, ℝ)`
(`measurableSet_stoppedWindowEvent`), depends only on the path up to time `N`, and satisfies
`window_mem_of_stopped` and `stopped_mem_of_window`, the two implications relating it to the event
that the window of the full path lies in `A`.

These are deterministic facts; the probabilistic input is the Markov property at the time `N` and the
Cameron–Martin theorem on `[0, N]` (`ConeAnnulusAreaLawEquivalenceOuterMarkov.lean`,
`ConeAnnulusAreaLawEquivalenceOuterCM.lean`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

/-- Stopping a path that is positive from time `N` on at `N` does not change its last zero. -/
theorem pathLastZero_stop {x : ℝ≥0 → ℝ} {N : ℝ≥0} (hpos : ∀ s : ℝ≥0, N ≤ s → 0 < x s) :
    pathLastZero (fun t => x (min t N)) = pathLastZero x := by
  unfold pathLastZero MatedCRTHarmonic.MatedCRT.lastZeroR
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  by_cases hsN : s.toNNReal ≤ N
  · rw [min_eq_left hsN]
  · have hlt : N ≤ s.toNNReal := (not_le.1 hsN).le
    constructor
    · intro h
      rw [min_eq_right hlt] at h
      exact absurd h (hpos N le_rfl).ne'
    · intro h
      exact absurd h (hpos _ hlt).ne'

/-- If the window of a path positive from time `N` on ends before `N`, stopping at `N` does not change
the window. -/
theorem outerWindowOfPath_stop {x : ℝ≥0 → ℝ} {N : ℝ≥0} {S : ℝ}
    (hpos : ∀ s : ℝ≥0, N ≤ s → 0 < x s) (h : pathLastZero x + S < N) :
    outerWindowOfPath S (fun t => x (min t N)) = outerWindowOfPath S x := by
  funext s
  simp only [outerWindowOfPath, pathLastZero_stop hpos]
  have : (pathLastZero x + min (s : ℝ) S).toNNReal ≤ N := by
    rw [Real.toNNReal_le_iff_le_coe]
    linarith [min_le_right (s : ℝ) S]
  rw [min_eq_left this]

/-- The event, for a path `z` read as stopped at `N`, that `z N > 0`, the last zero of `z` is below
`N - S` and the window of `z` lies in `A`. -/
def stoppedWindowEvent (N : ℝ≥0) (S : ℝ) (A : Set (ℝ≥0 → ℝ)) : Set C(ℝ≥0, ℝ) :=
  {z | 0 < z N ∧ pathLastZero (fun t => z t) + S < N ∧ outerWindowOfPath S (fun t => z t) ∈ A}

theorem measurableSet_stoppedWindowEvent (N : ℝ≥0) (S : ℝ) {A : Set (ℝ≥0 → ℝ)}
    (hA : MeasurableSet A) : MeasurableSet (stoppedWindowEvent N S A) := by
  have h1 : MeasurableSet {z : C(ℝ≥0, ℝ) | 0 < z N} :=
    measurableSet_lt measurable_const (continuous_eval_const N).measurable
  have h2 : MeasurableSet {z : C(ℝ≥0, ℝ) | pathLastZero (fun t => z t) + S < N} :=
    measurableSet_lt (measurable_pathLastZero.add_const S) measurable_const
  have h3 : MeasurableSet {z : C(ℝ≥0, ℝ) | outerWindowOfPath S (fun t => z t) ∈ A} :=
    measurable_outerWindowOfPath S hA
  exact h1.inter (h2.inter h3)

/-- A path positive from time `N` on whose stopped path lies in the event has its window in `A`. -/
theorem window_mem_of_stopped {x : C(ℝ≥0, ℝ)} {N : ℝ≥0} {S : ℝ} {A : Set (ℝ≥0 → ℝ)}
    (hpos : ∀ s : ℝ≥0, N ≤ s → 0 < x s)
    (h : LatticeProb.stopAt (N : ℝ≥0∞) x ∈ stoppedWindowEvent N S A) :
    outerWindowOfPath S (fun t => x t) ∈ A := by
  obtain ⟨_, h2, h3⟩ := h
  have e : (fun t => LatticeProb.stopAt (N : ℝ≥0∞) x t) = fun t => x (min t N) :=
    funext fun t => LatticeProb.stopAt_coe N x t
  rw [e, pathLastZero_stop hpos] at h2
  rw [e, outerWindowOfPath_stop hpos h2] at h3
  exact h3

/-- A path positive from time `N` on whose window ends before `N` and lies in `A` has its stopped
path in the event. -/
theorem stopped_mem_of_window {x : C(ℝ≥0, ℝ)} {N : ℝ≥0} {S : ℝ} {A : Set (ℝ≥0 → ℝ)}
    (hpos : ∀ s : ℝ≥0, N ≤ s → 0 < x s) (hl : pathLastZero (fun t => x t) + S < N)
    (hA : outerWindowOfPath S (fun t => x t) ∈ A) :
    LatticeProb.stopAt (N : ℝ≥0∞) x ∈ stoppedWindowEvent N S A := by
  have e : (fun t => LatticeProb.stopAt (N : ℝ≥0∞) x t) = fun t => x (min t N) :=
    funext fun t => LatticeProb.stopAt_coe N x t
  refine ⟨?_, ?_, ?_⟩
  · rw [LatticeProb.stopAt_coe, min_self]
    exact hpos N le_rfl
  · rw [e, pathLastZero_stop hpos]
    exact hl
  · rw [e, outerWindowOfPath_stop hpos hl]
    exact hA

/-- The path `y` with the drift `v` added up to time `N`: `t ↦ y t + v min(t, N)`. -/
def driftStop (v : ℝ) (N : ℝ≥0) (y : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun t := y t + v * min (t : ℝ) N
  continuous_toFun :=
    y.continuous.add (continuous_const.mul (NNReal.continuous_coe.min continuous_const))

theorem measurable_driftStop (v : ℝ) (N : ℝ≥0) : Measurable (driftStop v N) :=
  LatticeProb.measurable_pathValued_of_eval fun t =>
    ((continuous_eval_const t).measurable).add_const _

/-- Stopping the drifted path at `N` is adding the drift up to `N` to the stopped path. -/
theorem stopAt_driftMap (v : ℝ) (N : ℝ≥0) (w : C(ℝ≥0, ℝ)) :
    LatticeProb.stopAt (N : ℝ≥0∞) (LatticeProb.driftMap v w) =
      driftStop v N (LatticeProb.stopAt (N : ℝ≥0∞) w) := by
  ext t
  show LatticeProb.stopAt (N : ℝ≥0∞) (LatticeProb.driftMap v w) t =
    LatticeProb.stopAt (N : ℝ≥0∞) w t + v * min (t : ℝ) N
  rw [LatticeProb.stopAt_coe, LatticeProb.stopAt_coe, LatticeProb.driftMap_apply, NNReal.coe_min]

/-- The sample path of a process with measurable coordinates and continuous paths, stopped at a fixed
time, is a measurable map into `C(ℝ≥0, ℝ)`. -/
theorem measurable_stopAt_pathMap_const {Ω : Type*} [MeasurableSpace Ω] {b : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) (N : ℝ≥0) :
    Measurable fun ω => LatticeProb.stopAt (N : ℝ≥0∞) (LatticeProb.pathMap b hc ω) :=
  LatticeProb.measurable_pathValued_of_eval fun t => by
    have : (fun ω => LatticeProb.stopAt (N : ℝ≥0∞) (LatticeProb.pathMap b hc ω) t) =
        fun ω => b (min t N) ω := by
      funext ω
      rw [LatticeProb.stopAt_coe]
      rfl
    rw [this]
    exact hm _

end MatedCRT
