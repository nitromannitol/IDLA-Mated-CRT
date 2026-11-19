import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodStop

/-!
# The block-exit chain on the good event, for a frozen set between two far sets

`BlockExitSkeletonGoodStop` compares a path stopped at its exit time from `U` with the path stopped at
its `N`-th block exit when the block chain is frozen on `farSet U d'`.  The same deterministic
statements hold for any closed frozen set `F` lying between two far sets,
`farSet U d₁ ⊆ F ⊆ farSet U d'`, with `4 s + d₁ ≤ d`: the inclusion `F ⊆ farSet U d'` gives that the
path has left `U` (with margin `d'`) as soon as it is frozen, and the inclusion `farSet U d₁ ⊆ F`
gives that the chain is frozen at the block containing the rational exit witness of the good event.
For `F = farSet U d'` (take `d₁ = d'`) these are the statements of `BlockExitSkeletonGoodStop`.

* `blockExit_goodStop_facts_of_sandwich`: the `N`-th block exit time is at most the rational exit
  witness, the path is in `farSet U d'` at that time and has left `U` by then.
* `cmpEDist_stopAtExit_stoppedAtBlockExit_le_of_goodStop_sandwich`: `ω` stopped at its exit time from
  `U` is within `ε` (modulo time parametrization) of `ω` stopped at its `N`-th block exit.
* `cmpEDist_stopAtExit_le_of_goodStop_blockExit_sandwich`: every path `g` within `min ε d'` of `ω`
  stopped at its `N`-th block exit has `g` stopped at its exit time within `2 ε` of `ω` stopped at its
  exit time.
-/

open MeasureTheory Set Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open MatedCRT.StopAtExitCmp

/-- **Facts on the good event for a frozen set between two far sets.** -/
theorem blockExit_goodStop_facts_of_sandwich {s : ℝ} (hs : 0 < s) {U F : Set ℂ} {T η : ℝ≥0}
    {d d₁ d' ε : ℝ} (hd' : 0 < d') (hdd : 4 * s + d₁ ≤ d) (hF₁ : farSet U d₁ ⊆ F)
    (hF₂ : F ⊆ farSet U d') {N : ℕ} {ω : ContinuousPath ℂ}
    (hgood : GoodStop U T η d ε ω) (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) :
    ω (blockExitTimes s F N ω) ∈ farSet U d' ∧
      pathExitTime U ω ≤ ((blockExitTimes s F N ω : ℝ≥0) : ℝ≥0∞) ∧
      ∃ q : ℚ, blockExitTimes s F N ω ≤ ratTime q ∧ pathExitTime U ω < ratTime q ∧
        (ratTime q : ℝ≥0∞) < pathExitTime U ω + η ∧ ratTime q ≤ T := by
  classical
  obtain ⟨⟨q, hq1, hq2, hqT, hout⟩, -, -⟩ := hgood
  obtain ⟨hMN, hM⟩ : Nat.find hF ≤ N ∧ ω (blockExitTimes s F (Nat.find hF) ω) ∈ F :=
    Nat.find_spec hF
  have hσN : blockExitTimes s F N ω = blockExitTimes s F (Nat.find hF) ω :=
    blockExitTimes_eq_of_mem s hM N hMN
  have hωN : ω (blockExitTimes s F N ω) ∈ farSet U d' := by rw [hσN]; exact hF₂ hM
  have hτσ : pathExitTime U ω ≤ ((blockExitTimes s F N ω : ℝ≥0) : ℝ≥0∞) :=
    exitTime_le_of_not_mem ((mem_farSet.1 hωN) _ (by rw [dist_self]; exact hd'))
  have hσq : blockExitTimes s F N ω ≤ ratTime q := by
    by_cases hq : ratTime q ≤ blockExitTimes s F N ω
    · have hosc : ∀ n < N, ∀ t : ℝ≥0, blockExitTimes s F n ω ≤ t →
          t ≤ blockExitTimes s F (n + 1) ω →
          dist (ω t) (ω (blockExitTimes s F n ω)) ≤ 4 * s := fun n _ t h1 h2 => by
        rw [dist_eq_norm]
        exact norm_sub_le_of_blockExitTimes_le hs F n ω h1 h2
      obtain ⟨k, hkN, hkq, hkd, -⟩ := exists_blockIndex_of_le
        (σ := fun n => blockExitTimes s F n ω) (N := N) (ω := ⇑ω) (by linarith)
        (blockExitTimes_zero s F ω) hosc hq
      have hkF : ω (blockExitTimes s F k ω) ∈ F := by
        refine hF₁ ?_
        rw [mem_farSet]
        intro w hw
        refine hout w ?_
        have h1 := dist_triangle w (ω (blockExitTimes s F k ω)) (ω (ratTime q))
        have h2 := dist_comm (ω (blockExitTimes s F k ω)) (ω (ratTime q))
        linarith
      have hMk : Nat.find hF ≤ k := Nat.find_min' hF ⟨hkN, hkF⟩
      have hmono : Monotone fun n => blockExitTimes s F n ω :=
        monotone_nat_of_le_succ fun n => blockExitTimes_le_succ s F n ω
      exact hσN.le.trans ((hmono hMk).trans hkq)
    · exact (not_le.1 hq).le
  exact ⟨hωN, hτσ, q, hσq, hq1, hq2, hqT⟩

/-- **Stopped at the exit time versus stopped at the `N`-th block exit, on the good event**, for a
frozen set between two far sets. -/
theorem cmpEDist_stopAtExit_stoppedAtBlockExit_le_of_goodStop_sandwich {s : ℝ} (hs : 0 < s)
    {U F : Set ℂ} {T η : ℝ≥0} {d d₁ d' ε : ℝ} (hη : 0 < η) (hd' : 0 < d')
    (hdd : 4 * s + d₁ ≤ d) (hF₁ : farSet U d₁ ⊆ F) (hF₂ : F ⊆ farSet U d') {N : ℕ}
    {ω : ContinuousPath ℂ} (hgood : GoodStop U T η d ε ω)
    (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) :
    cmpEDist (stopAtExit U ω) (fun t => ω (min t (blockExitTimes s F N ω))) ≤
      ENNReal.ofReal ε := by
  obtain ⟨hωN, hτσ, q, hσq, hq1, hq2, hqT⟩ :=
    blockExit_goodStop_facts_of_sandwich hs hd' hdd hF₁ hF₂ hgood hF
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

/-- **Continuity of the stopping map at the block-exit-stopped good path**, for a frozen set between
two far sets. -/
theorem cmpEDist_stopAtExit_le_of_goodStop_blockExit_sandwich {s : ℝ} (hs : 0 < s) {U F : Set ℂ}
    {T η : ℝ≥0} {d d₁ d' ε : ℝ} (hη : 0 < η) (hd' : 0 < d') (hd'd : d' ≤ d)
    (hdd : 4 * s + d₁ ≤ d) (hF₁ : farSet U d₁ ⊆ F) (hF₂ : F ⊆ farSet U d') {N : ℕ}
    {ω : ContinuousPath ℂ} (hgood : GoodStop U T η d ε ω)
    (hF : ∃ n ≤ N, ω (blockExitTimes s F n ω) ∈ F) {g : ℝ≥0 → ℂ}
    (hg : cmpEDist g (fun t => ω (min t (blockExitTimes s F N ω))) <
      ENNReal.ofReal (min ε d')) :
    cmpEDist (stopAtExit U g) (stopAtExit U ω) ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨hωN, hτσ, q, hσq, hq1, hq2, hqT⟩ :=
    blockExit_goodStop_facts_of_sandwich hs hd' hdd hF₁ hF₂ hgood hF
  obtain ⟨-, hmod, htube⟩ := hgood
  have hout : ω (blockExitTimes s F N ω) ∉ U :=
    (mem_farSet.1 hωN) _ (by rw [dist_self]; exact hd')
  have hfin : pathExitTime U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτσ
  have hτ' : ((pathExitTime U ω).toNNReal : ℝ≥0∞) = pathExitTime U ω := ENNReal.coe_toNNReal hfin
  have hτ : pathExitTime U (fun t => ω (min t (blockExitTimes s F N ω))) =
      ((pathExitTime U ω).toNNReal : ℝ≥0∞) := (pathExitTime_comp_min hout).trans hτ'.symm
  have hτσ' : (pathExitTime U ω).toNNReal ≤ blockExitTimes s F N ω :=
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
    have hw' : dist w (ω (min (ratTime q) (blockExitTimes s F N ω))) < d' := hw
    rw [min_eq_right hσq] at hw'
    exact (mem_farSet.1 hωN) w hw'
  · intro t ht w hw
    have htτ : t ≤ (pathExitTime U ω).toNNReal := le_trans le_self_add ht
    have hw' : dist w (ω (min t (blockExitTimes s F N ω))) < d' := hw
    rw [min_eq_left (htτ.trans hτσ')] at hw'
    exact tube_of_ratTime ω.continuous hη hτ'.symm (by simpa using htube) t ht w
      (lt_of_lt_of_le hw' (by linarith))

end BlockExit

end MatedCRT
