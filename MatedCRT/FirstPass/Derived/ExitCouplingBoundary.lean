import MatedCRT.FirstPass.Derived.ExitCouplingGlue
import MatedCRT.FirstPass.S4S6c.GreenTest68
import LatticeProb.Prob.PathLawsStayNear

/-!
# Stopped interpolated walks that stay near their starting vertex

Let `A ⊆ B` be vertex sets.  Along a walk `X`, suppose every vertex visited up to the exit time from
`B` has its embedded point within `r` of a centre `c`.  The linearly interpolated walk of speed `m`,
stopped at its exit time from `A`, then stays in the closed disc of radius `r` about `c` at all times:
the interpolated path at a time in `[0, T]`, with `T` the (integer) exit time, is a convex combination
of two consecutive visited points, each of which lies in the disc (`dist_stoppedInterp_le`).

Consequently, if the walks from `x` and from `y` have the above property outside events of probability
at most `p`, with centres `v x` and `v y`, then the Lévy–Prokhorov edistance of the laws of the two
stopped interpolated paths, for the local uniform metric, is at most `R` as soon as
`T0 (2 r + |v x - v y|) + exp (-T0) < R` and `p + p ≤ R`
(`levyProkhorovEDist_stoppedInterp_le_of_stay_near`).  This is the comparison of the laws near the
boundary in Berestycki–Gwynne (2020), Proposition 6.12, Step 3: no coupling of the two walks is needed.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingBoundary

open MeasureTheory Set LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingGlue
attribute [local instance] LatticeProb.dUnifMetricSpace

/-- If every vertex visited up to the exit time from `A` has its embedded point in the closed disc of
radius `r` about `c`, then the interpolated walk stopped at that exit time stays in the disc. -/
lemma dist_stoppedInterp_le {v : ℤ → ℂ} {m : ℝ≥0} (hm : 0 < m) {A : Set ℤ} {X : ℕ → ℤ} {c : ℂ}
    {r : ℝ} (h : ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime A X → dist (v (X n)) c ≤ r) (t : ℝ≥0) :
    dist (stoppedInterp v m A X t) c ≤ r := by
  set T : ℕ := (vExitTime A X).toNat with hT
  have hTle : ∀ n : ℕ, n ≤ T → dist (v (X n)) c ≤ r := by
    intro n hn
    apply h
    by_cases hv : vExitTime A X = ⊤
    · rw [hv]; exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hv
      have hTk : T = k := by rw [hT, ← hk]; simp
      have hnk : n ≤ k := hTk ▸ hn
      rw [← hk]
      exact_mod_cast hnk
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold stoppedInterp
  simp only [stopPath_apply, interpPathCM_apply, interpPathFn]
  set q : ℝ≥0 := min t ((T : ℝ≥0) / m) with hq
  set s : ℝ := (m : ℝ) * (q : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  have hsT : s ≤ T := by
    have h1 : (q : ℝ) ≤ (T : ℝ) / (m : ℝ) := by
      simp [hq]
    calc s = (m : ℝ) * (q : ℝ) := rfl
      _ ≤ (m : ℝ) * ((T : ℝ) / (m : ℝ)) := mul_le_mul_of_nonneg_left h1 m.coe_nonneg
      _ = T := by field_simp
  set n : ℕ := ⌊s⌋₊ with hn
  have hn0 : (n : ℝ) ≤ s := Nat.floor_le hs0
  have hn1 : s < n + 1 := Nat.lt_floor_add_one s
  have hnT : n ≤ T := by exact_mod_cast hn0.trans hsT
  have ha : v (X n) ∈ Metric.closedBall c r := Metric.mem_closedBall.2 (hTle n hnT)
  unfold linInterp
  rw [← hn]
  by_cases hθ : s - n = 0
  · rw [hθ]
    simpa [Metric.mem_closedBall] using ha
  · have hθpos : 0 < s - n := lt_of_le_of_ne (by linarith) (Ne.symm hθ)
    have hnT' : n + 1 ≤ T := by
      have : (n : ℝ) < T := lt_of_lt_of_le (by linarith) hsT
      exact_mod_cast this
    have hb : v (X (n + 1)) ∈ Metric.closedBall c r := Metric.mem_closedBall.2 (hTle (n + 1) hnT')
    have hmem := (convex_closedBall c r) ha hb (a := 1 - (s - n)) (b := s - n) (by linarith)
      hθpos.le (by ring)
    rw [Metric.mem_closedBall] at hmem
    simpa [Complex.real_smul] using hmem

/-- **Walks that stay near their starting vertex have close laws.**  Let `A ⊆ B`.  If the probability
that, up to the exit time from `B`, the walk from `x` (resp. `y`) visits a vertex whose embedded point is
farther than `r` from `v x` (resp. `v y`) is at most `p`, then the Lévy–Prokhorov edistance of the laws of
the interpolated walks stopped at their exit time from `A` is at most `R`, for the local uniform metric,
as soon as `T0 (2 r + |v x - v y|) + exp (-T0) < R` and `p + p ≤ R`. -/
theorem levyProkhorovEDist_stoppedInterp_le_of_stay_near {mult : ℤ → ℤ → ℕ} (v : ℤ → ℂ)
    {m : ℝ≥0} (hm : 0 < m) {A B : Set ℤ} (hAB : A ⊆ B) {x y : ℤ} {r : ℝ} (T0 p R : ℝ≥0)
    (hR : T0 * (2 * r + dist (v x) (v y)) + Real.exp (-(T0 : ℝ)) < R)
    (hx : srwLaw mult x {X | ∃ n : ℕ, (n : ℕ∞) ≤ vExitTime B X ∧ r < dist (v (X n)) (v x)} ≤ p)
    (hy : srwLaw mult y {X | ∃ n : ℕ, (n : ℕ∞) ≤ vExitTime B X ∧ r < dist (v (X n)) (v y)} ≤ p)
    (hp : p + p ≤ R) :
    levyProkhorovEDist ((srwLaw mult x).map (stoppedInterp v m A))
      ((srwLaw mult y).map (stoppedInterp v m A)) ≤ R := by
  have hmeas := measurable_stoppedInterp v m A
  have : IsProbabilityMeasure ((srwLaw mult x).map (stoppedInterp v m A)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((srwLaw mult y).map (stoppedInterp v m A)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  have hopen : ∀ c : ℂ, IsOpen {f : C(ℝ≥0, ℂ) | ∃ t, r < dist (f t) c} := by
    intro c
    have : {f : C(ℝ≥0, ℂ) | ∃ t, r < dist (f t) c} = ⋃ t : ℝ≥0, {f | r < dist (f t) c} := by
      ext f; simp
    rw [this]
    exact isOpen_iUnion fun t =>
      isOpen_lt continuous_const ((continuous_eval_const t).dist continuous_const)
  have key : ∀ (a : ℤ), srwLaw mult a {X | ∃ n : ℕ, (n : ℕ∞) ≤ vExitTime B X ∧
      r < dist (v (X n)) (v a)} ≤ p →
      (srwLaw mult a).map (stoppedInterp v m A) {f | ∃ t, r < dist (f t) (v a)} ≤ p := by
    intro a ha
    rw [Measure.map_apply hmeas (hopen (v a)).measurableSet]
    refine le_trans (measure_mono ?_) ha
    intro X hX
    by_contra hn
    simp only [mem_preimage, mem_ofPred_eq, not_exists, not_and, not_lt] at hX hn
    obtain ⟨t, ht⟩ := hX
    exact absurd (dist_stoppedInterp_le hm (fun n hnA => hn n
      (hnA.trans (GreenTest68.vExitTime_le_of_subset hAB X))) t) (not_le.2 ht)
  exact levyProkhorovEDist_le_of_stay_near _ _ T0 p R hR (key x hx) (key y hy) hp

end ExitCouplingBoundary
end MatedCRT
