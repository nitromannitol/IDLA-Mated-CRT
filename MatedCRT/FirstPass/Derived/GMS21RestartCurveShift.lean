import MatedCRT.FirstPass.Derived.GMS21AnnulusStoppedCurve
import MatedCRT.FirstPass.Derived.CmpEDistKnots
import MatedCRT.FirstPass.Derived.BlockExitWalkNext

/-!
# Dropping the initial segment of a curve modulo time parametrization

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the walk started near the origin is
followed until it first reaches a vertex outside a small disc `B_δ(0)`; from there the strong Markov property restarts
it at a point where the comparison with Brownian motion is available. Modulo time parametrization the initial segment
costs little: a curve and the same curve with its part before time `T` removed are at distance at most twice the radius
of a disc containing the curve up to time `T + 1`. This file proves that bound, its form for the curves stopped at their
exits from a set `U` that the path does not leave before time `T`, and the geometric input for the interpolated walk:
up to one step after its first vertex outside `B_δ(0)`, the walk stays in `closedBall 0 (δ + 2 L)` when its steps from
`closedBall 0 (δ + L)` have length at most `L`.

## Main results

* `compressShift`: the increasing homeomorphism of `[0, ∞)` that maps `[0, T + 1]` linearly onto `[0, 1]` and is the
  shift by `-T` after `T + 1`.
* `cmpEDist_shift_le`: `cmpEDist F (t ↦ F (t + T)) ≤ 2 r` if `F` stays within `r` of a point up to time `T + 1`.
* `pathExitTime_eq_add_shift`: the exit time of a path that stays in `U` up to time `T` is `T` plus the exit time of
  the shifted path.
* `edist_stoppedExitCurve_shift_le`: the same bound for the curve classes stopped at the exits from `U`.
* `ballExitIndex`, `ballExitIndex_eq_iff`: the first index at which the embedded walk is outside `B_δ(0)`.
* `interpPathCM_mem_closedBall_of_ballExitIndex`: the interpolated walk stays in `closedBall 0 (δ + 2 L)` up to one
  step after that index.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison

section Reparam

/-- The increasing homeomorphism of `[0, ∞)` that maps `[0, T + 1]` linearly onto `[0, 1]` and is `t ↦ t - T` on
`[T + 1, ∞)`. -/
noncomputable def compressShift (T t : ℝ≥0) : ℝ≥0 :=
  if t ≤ T + 1 then t / (T + 1) else t - T

theorem compressShift_of_le {T t : ℝ≥0} (h : t ≤ T + 1) : compressShift T t = t / (T + 1) := by
  simp only [compressShift, h, ↓reduceIte]

theorem compressShift_of_lt {T t : ℝ≥0} (h : T + 1 < t) : compressShift T t = t - T := by
  simp only [compressShift, not_le.2 h, ↓reduceIte]

theorem compressShift_le_one {T t : ℝ≥0} (h : t ≤ T + 1) : compressShift T t ≤ 1 := by
  rw [compressShift_of_le h]
  exact div_le_one_of_le₀ h zero_le

theorem strictMono_compressShift (T : ℝ≥0) : StrictMono (compressShift T) := by
  have hT : (0 : ℝ≥0) < T + 1 := add_pos_of_nonneg_of_pos zero_le one_pos
  intro a b hab
  by_cases hb : b ≤ T + 1
  · rw [compressShift_of_le (hab.le.trans hb), compressShift_of_le hb]
    exact (div_lt_div_iff_of_pos_right hT).2 hab
  · have hb' : T + 1 < b := not_le.1 hb
    rw [compressShift_of_lt hb']
    by_cases ha : a ≤ T + 1
    · rw [compressShift_of_le ha]
      refine (div_le_one_of_le₀ ha zero_le).trans_lt ?_
      rw [lt_tsub_iff_left]
      exact hb'
    · rw [compressShift_of_lt (not_le.1 ha)]
      have hTa : T ≤ a := le_of_lt (lt_of_le_of_lt le_self_add (not_le.1 ha))
      exact tsub_lt_tsub_right_of_le hTa hab

theorem surjective_compressShift (T : ℝ≥0) : Function.Surjective (compressShift T) := by
  have hT : (0 : ℝ≥0) < T + 1 := add_pos_of_nonneg_of_pos zero_le one_pos
  intro y
  by_cases hy : y ≤ 1
  · refine ⟨y * (T + 1), ?_⟩
    have hle : y * (T + 1) ≤ T + 1 := mul_le_of_le_one_left zero_le hy
    rw [compressShift_of_le hle, mul_div_cancel_right₀ y hT.ne']
  · have hy' : 1 < y := not_le.1 hy
    refine ⟨y + T, ?_⟩
    have hlt : T + 1 < y + T := by
      rw [add_comm T 1]
      exact add_lt_add_of_lt_of_le hy' le_rfl
    rw [compressShift_of_lt hlt, add_tsub_cancel_right]

/-- The order isomorphism `compressShift T` of `[0, ∞)`. -/
noncomputable def compressShiftIso (T : ℝ≥0) : ℝ≥0 ≃o ℝ≥0 :=
  (strictMono_compressShift T).orderIsoOfSurjective _ (surjective_compressShift T)

/-- **Dropping an initial segment.** If `F` stays within `r` of `c` up to time `T + 1`, then `F` and the shifted
curve `t ↦ F (t + T)` are at distance at most `2 r` modulo time parametrization. -/
theorem cmpEDist_shift_le (F : ℝ≥0 → ℂ) (T : ℝ≥0) (c : ℂ) {r : ℝ}
    (h : ∀ t ≤ T + 1, dist (F t) c ≤ r) :
    cmpEDist F (fun t => F (t + T)) ≤ ENNReal.ofReal (2 * r) := by
  refine CmpEDistKnots.cmpEDist_le_of_orderIso (compressShiftIso T) fun t => ?_
  show dist (F t) (F (compressShift T t + T)) ≤ 2 * r
  have hr : 0 ≤ r := dist_nonneg.trans (h 0 zero_le)
  by_cases ht : t ≤ T + 1
  · have h1 : compressShift T t + T ≤ T + 1 := by
      have := add_le_add (compressShift_le_one ht) (le_refl T)
      rwa [add_comm (1 : ℝ≥0) T] at this
    calc dist (F t) (F (compressShift T t + T)) ≤ dist (F t) c + dist (F (compressShift T t + T)) c :=
          dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add (h t ht) (h _ h1)
      _ = 2 * r := by ring
  · have hTt : T ≤ t := le_of_lt (lt_of_le_of_lt le_self_add (not_le.1 ht))
    have h1 : compressShift T t + T = t := by
      rw [compressShift_of_lt (not_le.1 ht)]
      exact tsub_add_cancel_of_le hTt
    rw [h1, dist_self]
    positivity

end Reparam

section Exit

/-- **Exit time after a shift.** If `f` stays in `U` up to time `T`, its exit time from `U` is `T` plus the exit time
of the shifted path `t ↦ f (t + T)`. -/
theorem pathExitTime_eq_add_shift {U : Set ℂ} {f : ℝ≥0 → ℂ} {T : ℝ≥0} (h : ∀ t ≤ T, f t ∈ U) :
    pathExitTime U f = T + pathExitTime U (fun t => f (t + T)) := by
  apply le_antisymm
  · have key : pathExitTime U f - T ≤ pathExitTime U (fun t => f (t + T)) := by
      refine le_sInf ?_
      rintro _ ⟨t, rfl, ht⟩
      rw [tsub_le_iff_right]
      have hle : pathExitTime U f ≤ ((t + T : ℝ≥0) : ℝ≥0∞) := sInf_le ⟨t + T, rfl, ht⟩
      rwa [ENNReal.coe_add] at hle
    calc pathExitTime U f ≤ pathExitTime U f - T + T := le_tsub_add
      _ ≤ pathExitTime U (fun t => f (t + T)) + T := add_le_add key le_rfl
      _ = T + pathExitTime U (fun t => f (t + T)) := add_comm _ _
  · refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    have hTt : T ≤ t := by
      by_contra hlt
      exact ht (h t (le_of_lt (not_le.1 hlt)))
    have hle : pathExitTime U (fun s => f (s + T)) ≤ ((t - T : ℝ≥0) : ℝ≥0∞) := by
      refine sInf_le ⟨t - T, rfl, ?_⟩
      show f (t - T + T) ∉ U
      rwa [tsub_add_cancel_of_le hTt]
    calc (T : ℝ≥0∞) + pathExitTime U (fun s => f (s + T)) ≤ T + ((t - T : ℝ≥0) : ℝ≥0∞) :=
          add_le_add le_rfl hle
      _ = t := by rw [← ENNReal.coe_add, add_tsub_cancel_of_le hTt]

/-- **Dropping an initial segment of a stopped curve.** Let `g' = g (· + T)` where the continuous path `g` stays in `U`
up to time `T` and within `r` of `c` up to time `T + 1`. Then the curve classes of `g` and `g'` stopped at their exits
from `U` are at distance at most `2 r`. -/
theorem edist_stoppedExitCurve_shift_le {U : Set ℂ} (g g' : ContinuousPath ℂ) {T : ℝ≥0}
    (hg' : ∀ s, g' s = g (s + T)) (hU : ∀ t ≤ T, g t ∈ U) (c : ℂ) {r : ℝ}
    (hr : ∀ t ≤ T + 1, dist (g t) c ≤ r) :
    edist (stoppedExitCurve U g) (stoppedExitCurve U g') ≤ ENNReal.ofReal (2 * r) := by
  have hg'f : (fun t => g (t + T)) = ⇑g' := funext fun s => (hg' s).symm
  have hE : pathExitTime U ⇑g = T + pathExitTime U ⇑g' := by
    rw [pathExitTime_eq_add_shift hU, hg'f]
  unfold stoppedExitCurve
  rw [(isometryEquiv 2).isometry.edist_eq, ← complex_stoppedRay_eq_normalizedPrefixCurve]
  show cmpEDist (fun t => g (min t (pathExitTime U ⇑g).toNNReal))
    (fun t => g' (min t (pathExitTime U ⇑g').toNNReal)) ≤ ENNReal.ofReal (2 * r)
  by_cases hfin : pathExitTime U ⇑g' = ⊤
  · have hfin' : pathExitTime U ⇑g = ⊤ := by rw [hE, hfin, add_top]
    rw [hfin, hfin']
    refine CmpEDistKnots.cmpEDist_le_of_orderIso (OrderIso.refl ℝ≥0) fun t => ?_
    have h0 : (⊤ : ℝ≥0∞).toNNReal = 0 := rfl
    show dist (g (min t (⊤ : ℝ≥0∞).toNNReal)) (g' (min t (⊤ : ℝ≥0∞).toNNReal)) ≤ 2 * r
    rw [h0, min_eq_right zero_le, hg' 0, zero_add]
    have hT1 : T ≤ T + 1 := le_self_add
    calc dist (g 0) (g T) ≤ dist (g 0) c + dist (g T) c := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add (hr 0 zero_le) (hr T hT1)
      _ = 2 * r := by ring
  · have hT : (pathExitTime U ⇑g).toNNReal = T + (pathExitTime U ⇑g').toNNReal := by
      rw [hE, ENNReal.toNNReal_add ENNReal.coe_ne_top hfin, ENNReal.toNNReal_coe]
    rw [hT]
    generalize (pathExitTime U ⇑g').toNNReal = E
    have hshift : (fun t => g' (min t E)) = fun t => (fun s => g (min s (T + E))) (t + T) := by
      funext t
      show g' (min t E) = g (min (t + T) (T + E))
      rw [hg', add_comm T E, min_add_add_right]
    rw [hshift]
    exact cmpEDist_shift_le _ T c fun t ht => hr _ ((min_le_left _ _).trans ht)

end Exit

section Walk

open Classical in
/-- The first index at which the embedded walk `p ∘ w` is outside the open disc `B_δ(0)` (`⊤` if there is none). -/
noncomputable def ballExitIndex (p : ℤ → ℂ) (δ : ℝ) (w : ℕ → ℤ) : ℕ∞ :=
  if h : ∃ k, p (w k) ∉ ball (0 : ℂ) δ then (Nat.find h : ℕ∞) else ⊤

theorem ballExitIndex_eq_iff (p : ℤ → ℂ) (δ : ℝ) (w : ℕ → ℤ) (k : ℕ) :
    ballExitIndex p δ w = k ↔ p (w k) ∉ ball (0 : ℂ) δ ∧ ∀ j < k, p (w j) ∈ ball (0 : ℂ) δ := by
  classical
  unfold ballExitIndex
  by_cases h : ∃ k, p (w k) ∉ ball (0 : ℂ) δ
  · rw [dite_eq_left h, Nat.cast_inj, Nat.find_eq_iff]
    simp only [not_not]
  · rw [dite_eq_right h]
    simp only [not_exists, not_not] at h
    constructor
    · intro htop
      exact absurd htop (ENat.top_ne_natCast k)
    · intro hk
      exact absurd (h k) hk.1

/-- **The walk up to one step after leaving `B_δ(0)`.** If the walk `w` has consecutive vertices equal or joined by
an edge of `m`, starts with `p (w 0) ∈ B_δ(0)`, first leaves `B_δ(0)` at the index `k`, and every edge from a vertex
of `closedBall 0 (δ + L)` has embedded length at most `L`, then the embedded points `p (w j)`, `j ≤ k + 1`, lie in
`closedBall 0 (δ + 2 L)`. -/
theorem mem_closedBall_of_ballExitIndex {m : ℤ → ℤ → ℕ} {p : ℤ → ℂ} {δ L : ℝ} (hL : 0 ≤ L)
    (hstep : ∀ x y, p x ∈ closedBall (0 : ℂ) (δ + L) → m x y ≠ 0 → dist (p x) (p y) ≤ L)
    {w : ℕ → ℤ} (hw : ∀ n, w (n + 1) = w n ∨ m (w n) (w (n + 1)) ≠ 0)
    {k : ℕ} (hk : ballExitIndex p δ w = k) (h0 : p (w 0) ∈ ball (0 : ℂ) δ) :
    ∀ j ≤ k + 1, p (w j) ∈ closedBall (0 : ℂ) (δ + 2 * L) := by
  rw [ballExitIndex_eq_iff] at hk
  have hstep' : ∀ n, p (w n) ∈ closedBall (0 : ℂ) (δ + L) → dist (p (w n)) (p (w (n + 1))) ≤ L := by
    intro n hn
    rcases hw n with he | he
    · rw [he, dist_self]
      exact hL
    · exact hstep _ _ hn he
  have hkpos : k ≠ 0 := by
    rintro rfl
    exact hk.1 h0
  have hkL : p (w k) ∈ closedBall (0 : ℂ) (δ + L) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos
    have hn : p (w n) ∈ ball (0 : ℂ) δ := hk.2 n (Nat.lt_succ_self n)
    have hn' : p (w n) ∈ closedBall (0 : ℂ) (δ + L) :=
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hn)
    have hd := hstep' n hn'
    rw [mem_ball] at hn
    rw [mem_closedBall]
    linarith [dist_triangle (p (w (n + 1))) (p (w n)) 0, dist_comm (p (w (n + 1))) (p (w n))]
  intro j hj
  rcases Nat.lt_or_ge j k with hjk | hjk
  · exact closedBall_subset_closedBall (by linarith) (ball_subset_closedBall (hk.2 j hjk))
  · rcases (show j = k ∨ j = k + 1 by omega) with rfl | rfl
    · exact closedBall_subset_closedBall (by linarith) hkL
    · have hd := hstep' k hkL
      rw [mem_closedBall] at hkL ⊢
      linarith [dist_triangle (p (w (k + 1))) (p (w k)) 0, dist_comm (p (w (k + 1))) (p (w k))]

/-- The interpolated walk (unit speed) stays in `closedBall 0 r` up to time `k + 1` if its points `p (w j)`,
`j ≤ k + 1`, do. -/
theorem interpPathCM_mem_closedBall {p : ℤ → ℂ} {w : ℕ → ℤ} {k : ℕ} {r : ℝ}
    (hp : ∀ j ≤ k + 1, p (w j) ∈ closedBall (0 : ℂ) r) {t : ℝ≥0} (ht : t ≤ (k : ℝ≥0) + 1) :
    interpPathCM p zero_le_one w t ∈ closedBall (0 : ℂ) r := by
  have htR : (t : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast ht
  obtain ⟨j, hj1, hj2, hjk⟩ : ∃ j : ℕ, (j : ℝ) ≤ t ∧ (t : ℝ) ≤ j + 1 ∧ j ≤ k := by
    rcases le_total ⌊(t : ℝ)⌋₊ k with h | h
    · exact ⟨_, Nat.floor_le (NNReal.coe_nonneg t), (Nat.lt_floor_add_one _).le, h⟩
    · exact ⟨k, (Nat.cast_le.2 h).trans (Nat.floor_le (NNReal.coe_nonneg t)), htR, le_rfl⟩
  have hseg := BlockExit.interpPathCM_mem_segment p zero_le_one w (t := t) (j := j)
    (by rw [one_mul]; exact hj1) (by rw [one_mul]; exact hj2)
  exact (convex_closedBall (0 : ℂ) r).segment_subset (hp j (by omega)) (hp (j + 1) (by omega)) hseg

end Walk

end MatedCRT
