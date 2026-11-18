import MatedCRT.FirstPass.Derived.BlockExitSkeletonStopAtExit
import MatedCRT.FirstPass.Derived.StopAtExitGoodEvent
import MatedCRT.FirstPass.Derived.StopAtExitTimeFormula

/-!
# The block-exit chain on the good event of the stopping map

For an open set `U`, a radius `d' > 0`, the closed set `farSet U d'` of points whose open `d'`-ball
lies outside `U`, and a block mesh `s > 0` with `4 s + d' ≤ d`, a continuous path `ω` in
`GoodStop U T η d ε` whose block chain frozen on `farSet U d'` reaches that set within `N` steps has
the following properties (deterministic, no probability):

* `blockExit_goodStop_facts`: the `N`-th block exit time `σ_N` is at most the rational exit witness
  of the good event, the path is in `farSet U d'` at `σ_N`, and `ω` has left `U` by `σ_N`;
* `cmpEDist_stopAtExit_stoppedAtBlockExit_le_of_goodStop`: `ω` stopped at its exit time from `U` is
  within `ε` (modulo time parametrization) of `ω` stopped at `σ_N`;
* `cmpEDist_stopAtExit_le_of_goodStop_blockExit`: every path `g` within `min ε d'` of the path
  stopped at `σ_N` has `g` stopped at its exit time within `2 ε` of `ω` stopped at its exit time.

The last statement is the stopping-map continuity at the good path `ω ∘ min · σ_N` (in the manner of
the `GoodStop` estimate `cmpEDist_stopAtExit_le_of_goodStop`), at a path that is itself not required to
be in `GoodStop`.
-/

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- The points whose open `r`-ball lies outside `U`. -/
def farSet (U : Set ℂ) (r : ℝ) : Set ℂ := {y | ∀ w, dist w y < r → w ∉ U}

theorem mem_farSet {U : Set ℂ} {r : ℝ} {y : ℂ} : y ∈ farSet U r ↔ ∀ w, dist w y < r → w ∉ U :=
  Iff.rfl

theorem isClosed_farSet (U : Set ℂ) (r : ℝ) : IsClosed (farSet U r) :=
  isClosed_setOf_forall_dist_lt_imp_mem Uᶜ r

/-- A lower bound for the exit time from all exit points. -/
theorem le_pathExitTime_aux {U : Set ℂ} {f : ℝ≥0 → ℂ} {c : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, f t ∉ U → c ≤ t) : c ≤ pathExitTime U f := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  exact h t ht

theorem toNNReal_le_of_le_coe' {a : ℝ≥0∞} {c : ℝ≥0} (h : a ≤ c) : a.toNNReal ≤ c := by
  simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top h

/-- Stopping a path at a time `σ` at which it is outside `U` does not change its exit time from `U`. -/
theorem pathExitTime_comp_min {U : Set ℂ} {f : ℝ≥0 → ℂ} {σ : ℝ≥0} (h : f σ ∉ U) :
    pathExitTime U (fun t => f (min t σ)) = pathExitTime U f := by
  have h1 : pathExitTime U (fun t => f (min t σ)) ≤ σ :=
    exitTime_le_of_not_mem (by show f (min σ σ) ∉ U; rwa [min_self])
  have h2 : pathExitTime U f ≤ σ := exitTime_le_of_not_mem h
  refine le_antisymm (le_pathExitTime_aux fun t ht => ?_) (le_pathExitTime_aux fun t ht => ?_)
  · by_cases hts : t ≤ σ
    · exact exitTime_le_of_not_mem (g := fun t => f (min t σ)) (by
        show f (min t σ) ∉ U
        rwa [min_eq_left hts])
    · exact h1.trans (by exact_mod_cast (not_le.1 hts).le)
  · by_cases hts : t ≤ σ
    · exact exitTime_le_of_not_mem (by
        have : f (min t σ) ∉ U := ht
        rwa [min_eq_left hts] at this)
    · exact h2.trans (by exact_mod_cast (not_le.1 hts).le)

/-- Stopping at a time `σ` at which the path is outside `U` does not change the path stopped at its
exit time from `U`. -/
theorem stopAtExit_comp_min_eq {U : Set ℂ} {f : ℝ≥0 → ℂ} {σ : ℝ≥0} (h : f σ ∉ U) :
    stopAtExit U (fun t => f (min t σ)) = stopAtExit U f := by
  have hpe := pathExitTime_comp_min h
  have h2 : pathExitTime U f ≤ σ := exitTime_le_of_not_mem h
  funext t
  rw [stopAtExit_eq_min_exitTime, stopAtExit_eq_min_exitTime, hpe]
  have hle : (min (t : ℝ≥0∞) (pathExitTime U f)).toNNReal ≤ σ :=
    toNNReal_le_of_le_coe' ((min_le_right _ _).trans h2)
  show f (min (min (t : ℝ≥0∞) (pathExitTime U f)).toNNReal σ) = _
  rw [min_eq_left hle]

theorem dist_min_right_le (a b c : ℝ≥0) : dist (min a c) (min b c) ≤ dist a b := by
  rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
  calc |min (a : ℝ) c - min (b : ℝ) c| ≤ max |(a : ℝ) - b| |(c : ℝ) - c| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = |(a : ℝ) - b| := by simp

/-- **Facts about the block chain on the good event.** Let `0 < s`, `0 < d'`, `4 s + d' ≤ d`, let `ω`
be in `GoodStop U T η d ε`, and suppose the block chain frozen on `farSet U d'` is in `farSet U d'`
at some step `n ≤ N`. Then `ω (σ_N) ∈ farSet U d'`, `ω` has left `U` by `σ_N`, and `σ_N` is at most
a rational exit witness `q`, with `τ < q < τ + η`, `q ≤ T` and the `d`-ball about `ω q` outside `U`.

The index of the block containing `q` has `ω (σ_k)` within `4 s` of `ω q`, so in `farSet U d'`;
hence the first frozen step is at most `k` and `σ_N ≤ σ_k ≤ q`. -/
theorem blockExit_goodStop_facts {s : ℝ} (hs : 0 < s) {U : Set ℂ} {T η : ℝ≥0} {d d' ε : ℝ}
    (hd' : 0 < d') (hdd : 4 * s + d' ≤ d) {N : ℕ} {ω : ContinuousPath ℂ}
    (hgood : GoodStop U T η d ε ω)
    (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') :
    ω (blockExitTimes s (farSet U d') N ω) ∈ farSet U d' ∧
      pathExitTime U ω ≤ ((blockExitTimes s (farSet U d') N ω : ℝ≥0) : ℝ≥0∞) ∧
      ∃ q : ℚ, blockExitTimes s (farSet U d') N ω ≤ ratTime q ∧ pathExitTime U ω < ratTime q ∧
        (ratTime q : ℝ≥0∞) < pathExitTime U ω + η ∧ ratTime q ≤ T := by
  classical
  obtain ⟨⟨q, hq1, hq2, hqT, hout⟩, -, -⟩ := hgood
  obtain ⟨hMN, hM⟩ : Nat.find hF ≤ N ∧
      ω (blockExitTimes s (farSet U d') (Nat.find hF) ω) ∈ farSet U d' := Nat.find_spec hF
  have hσN : blockExitTimes s (farSet U d') N ω = blockExitTimes s (farSet U d') (Nat.find hF) ω :=
    blockExitTimes_eq_of_mem s hM N hMN
  have hωN : ω (blockExitTimes s (farSet U d') N ω) ∈ farSet U d' := by rw [hσN]; exact hM
  have hτσ : pathExitTime U ω ≤ ((blockExitTimes s (farSet U d') N ω : ℝ≥0) : ℝ≥0∞) :=
    exitTime_le_of_not_mem ((mem_farSet.1 hωN) _ (by rw [dist_self]; exact hd'))
  have hσq : blockExitTimes s (farSet U d') N ω ≤ ratTime q := by
    by_cases hq : ratTime q ≤ blockExitTimes s (farSet U d') N ω
    · have hosc : ∀ n < N, ∀ t : ℝ≥0, blockExitTimes s (farSet U d') n ω ≤ t →
          t ≤ blockExitTimes s (farSet U d') (n + 1) ω →
          dist (ω t) (ω (blockExitTimes s (farSet U d') n ω)) ≤ 4 * s := fun n _ t h1 h2 => by
        rw [dist_eq_norm]
        exact norm_sub_le_of_blockExitTimes_le hs (farSet U d') n ω h1 h2
      obtain ⟨k, hkN, hkq, hkd, -⟩ := exists_blockIndex_of_le
        (σ := fun n => blockExitTimes s (farSet U d') n ω) (N := N) (ω := ⇑ω) (by linarith)
        (blockExitTimes_zero s (farSet U d') ω) hosc hq
      have hkF : ω (blockExitTimes s (farSet U d') k ω) ∈ farSet U d' := by
        rw [mem_farSet]
        intro w hw
        refine hout w ?_
        have h1 := dist_triangle w (ω (blockExitTimes s (farSet U d') k ω)) (ω (ratTime q))
        have h2 := dist_comm (ω (blockExitTimes s (farSet U d') k ω)) (ω (ratTime q))
        linarith
      have hMk : Nat.find hF ≤ k := Nat.find_min' hF ⟨hkN, hkF⟩
      have hmono : Monotone fun n => blockExitTimes s (farSet U d') n ω :=
        monotone_nat_of_le_succ fun n => blockExitTimes_le_succ s (farSet U d') n ω
      exact hσN.le.trans ((hmono hMk).trans hkq)
    · exact (not_le.1 hq).le
  exact ⟨hωN, hτσ, q, hσq, hq1, hq2, hqT⟩

/-- **Stopped at the exit time versus stopped at the `N`-th block exit, on the good event.** -/
theorem cmpEDist_stopAtExit_stoppedAtBlockExit_le_of_goodStop {s : ℝ} (hs : 0 < s) {U : Set ℂ}
    {T η : ℝ≥0} {d d' ε : ℝ} (hη : 0 < η) (hd' : 0 < d') (hdd : 4 * s + d' ≤ d) {N : ℕ}
    {ω : ContinuousPath ℂ} (hgood : GoodStop U T η d ε ω)
    (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') :
    cmpEDist (stopAtExit U ω) (fun t => ω (min t (blockExitTimes s (farSet U d') N ω))) ≤
      ENNReal.ofReal ε := by
  obtain ⟨hωN, hτσ, q, hσq, hq1, hq2, hqT⟩ := blockExit_goodStop_facts hs hd' hdd hgood hF
  obtain ⟨-, hmod, -⟩ := hgood
  have hfin : pathExitTime U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτσ
  have hτ' : ((pathExitTime U ω).toNNReal : ℝ≥0∞) = pathExitTime U ω := ENNReal.coe_toNNReal hfin
  have hmodulus := modulus_of_ratTime ω.continuous hη hmod
  have hqτ : ratTime q < (pathExitTime U ω).toNNReal + η := by
    rw [← hτ', ← ENNReal.coe_add] at hq2
    exact ENNReal.coe_lt_coe.1 hq2
  refine cmpEDist_stopAtExit_le_of_forall_dist_le hτσ fun u hu1 hu2 => ?_
  have huT : u ≤ T := hu2.trans (hσq.trans hqT)
  have hτT : (pathExitTime U ω).toNNReal ≤ T := hu1.trans huT
  refine hmodulus u huT _ hτT ?_
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hu1))]
  have h1 := NNReal.coe_lt_coe.2 hqτ
  have h2 := NNReal.coe_le_coe.2 (hu2.trans hσq)
  rw [NNReal.coe_add] at h1
  linarith

/-- **Continuity of the stopping map at the block-exit-stopped good path.** Under the hypotheses of
`blockExit_goodStop_facts`, with `η > 0`, every path `g` within curve distance `min ε d'` of `ω`
stopped at its `N`-th block exit has, stopped at its exit time from `U`, curve distance at most `2 ε`
from `ω` stopped at its exit time from `U`. -/
theorem cmpEDist_stopAtExit_le_of_goodStop_blockExit {s : ℝ} (hs : 0 < s) {U : Set ℂ}
    {T η : ℝ≥0} {d d' ε : ℝ} (hη : 0 < η) (hd' : 0 < d') (hdd : 4 * s + d' ≤ d) {N : ℕ}
    {ω : ContinuousPath ℂ} (hgood : GoodStop U T η d ε ω)
    (hF : ∃ n ≤ N, ω (blockExitTimes s (farSet U d') n ω) ∈ farSet U d') {g : ℝ≥0 → ℂ}
    (hg : cmpEDist g (fun t => ω (min t (blockExitTimes s (farSet U d') N ω))) <
      ENNReal.ofReal (min ε d')) :
    cmpEDist (stopAtExit U g) (stopAtExit U ω) ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨hωN, hτσ, q, hσq, hq1, hq2, hqT⟩ := blockExit_goodStop_facts hs hd' hdd hgood hF
  obtain ⟨-, hmod, htube⟩ := hgood
  have hout : ω (blockExitTimes s (farSet U d') N ω) ∉ U :=
    (mem_farSet.1 hωN) _ (by rw [dist_self]; exact hd')
  have hfin : pathExitTime U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτσ
  have hτ' : ((pathExitTime U ω).toNNReal : ℝ≥0∞) = pathExitTime U ω := ENNReal.coe_toNNReal hfin
  have hτ : pathExitTime U (fun t => ω (min t (blockExitTimes s (farSet U d') N ω))) =
      ((pathExitTime U ω).toNNReal : ℝ≥0∞) := (pathExitTime_comp_min hout).trans hτ'.symm
  have hτσ' : (pathExitTime U ω).toNNReal ≤ blockExitTimes s (farSet U d') N ω :=
    toNNReal_le_of_le_coe' hτσ
  have hmodulus := modulus_of_ratTime ω.continuous hη hmod
  rw [← stopAtExit_comp_min_eq hout]
  refine cmpEDist_stopAtExit_le_of_modulus (τ := (pathExitTime U ω).toNNReal) (s := ratTime q)
    (η := η) (T := T) (d := d') hτ hη ?_ ?_ hqT ?_ ?_ hg
  · intro t ht t' ht' htt'
    exact hmodulus _ ((min_le_right _ _).trans (hσq.trans hqT)) _
      ((min_le_right _ _).trans (hσq.trans hqT)) ((dist_min_right_le _ _ _).trans_lt htt')
  · refine ⟨ENNReal.coe_lt_coe.1 (hτ'.symm ▸ hq1), ?_⟩
    rw [← hτ', ← ENNReal.coe_add] at hq2
    exact ENNReal.coe_lt_coe.1 hq2
  · intro w hw
    have hw' : dist w (ω (min (ratTime q) (blockExitTimes s (farSet U d') N ω))) < d' := hw
    rw [min_eq_right hσq] at hw'
    exact (mem_farSet.1 hωN) w hw'
  · intro t ht w hw
    have htτ : t ≤ (pathExitTime U ω).toNNReal := le_trans le_self_add ht
    have hw' : dist w (ω (min t (blockExitTimes s (farSet U d') N ω))) < d' := hw
    rw [min_eq_left (htτ.trans hτσ')] at hw'
    exact tube_of_ratTime ω.continuous hη hτ'.symm (by simpa using htube) t ht w
      (lt_of_lt_of_le hw' (by linarith))

end BlockExit

end MatedCRT
