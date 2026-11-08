import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableTruncated

/-!
# Killed occupation: deterministic continuity of stopped path integrals (PROOF-REPAIRS-G §G4)

Deterministic step behind `TruncatedDetFixedTimeStep` (D1, `FixedTimeReduction.lean`), following the written repair
PROOF-REPAIRS-G §G4 (Lemma 3.4 and the exit functional). All statements are pathwise: no stochastic input and no
quenched invariance principle is used.

Let `w : ℝ≥0 → ℂ` be a continuous limiting path with finite first exit time `τ` from the open disk `B(z, r)`, which
visits the exterior `{x | r < dist x z}` immediately after `τ` (`hext`). For the Liouville Brownian path this clause
is supplied by the outward excursion at the exit time (`BrownianOutwardExcursionAtExitStep`) transported by the
strictly increasing continuous clock; that transport is not formalized here. Let `wn i` converge to `w` locally
uniformly on compact time intervals (`hloc`), and let `σ i` be approximate exit times sandwiched, for every small
`δ > 0`, between the first exits of `wn i` from `B(z, r - δ)` and `B(z, r + δ)` (`hsand`; the discrete exit between
exits from radii `r ∓ o(1)`, G4 step 1). Then, for every bounded continuous `g`, the stopped integrals
`∫_{(0, min T σ_i]} g (wn i t) dt` converge to `∫_{(0, min T τ]} g (w t) dt`.

Proof. (A) `σ i → τ` (`tendsto_approxExit_toReal`): the exit-time continuity of G4, from the exterior visit and the
local uniform convergence. (B) Dominated convergence for the indicator-weighted integrands
(`tendsto_stopped_integral_of_locallyUniform`), using (A), pointwise convergence and the continuity of `g`; the
endpoint `min T τ` is Lebesgue-null.

Terminology: exterior of a disk and first exit time as in Armitage–Gardiner (*Classical Potential Theory*).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- A point `w t` at distance at least `ρ` from `z` bounds the first exit time of the path from `B(z, ρ)` above. -/
lemma pathExitTime_ball_le_of_le_dist {z : ℂ} {ρ : ℝ} {w : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : ρ ≤ dist (w t) z) :
    pathExitTime (ball z ρ) w ≤ (t : ℝ≥0∞) :=
  pathExitTime_le_of_not_mem fun h => (not_lt.2 ht) (mem_ball.1 h)

/-- A path that stays at distance less than `ρ` from `z` up to time `t` has first exit time from `B(z, ρ)` at
least `t`. -/
lemma le_pathExitTime_ball_of_dist_lt {z : ℂ} {ρ : ℝ} {w : ℝ≥0 → ℂ} {t : ℝ≥0}
    (h : ∀ s ≤ t, dist (w s) z < ρ) : (t : ℝ≥0∞) ≤ pathExitTime (ball z ρ) w :=
  le_pathExitTime_of_forall_mem fun s hs => mem_ball.2 (h s hs)

/-- Before a finite first exit time `τ` (real form, `τ = (pathExitTime (ball z r) w).toReal`), the path lies in the
open disk `B(z, r)`. -/
lemma dist_lt_of_lt_toReal_exitTime {z : ℂ} {r : ℝ} {w : ℝ≥0 → ℂ} (hfin : pathExitTime (ball z r) w ≠ ⊤)
    {s : ℝ≥0} (hs : (s : ℝ) < (pathExitTime (ball z r) w).toReal) : dist (w s) z < r := by
  have h1 : ENNReal.ofReal (s : ℝ) < pathExitTime (ball z r) w :=
    (ENNReal.ofReal_lt_iff_lt_toReal s.coe_nonneg hfin).2 hs
  rw [ENNReal.ofReal_coe_nnreal] at h1
  exact mem_ball.1 (mem_of_lt_pathExitTime h1)

/-- **Continuity of the approximate exit times** (PROOF-REPAIRS-G §G4, step 1). Let `wn i → w` locally uniformly on
compact time intervals, let `w` have a finite first exit time from `B(z, r)` and visit the exterior `{r < dist · z}`
immediately after it (`hext`, a frequency statement along `𝓝[>] τ`). If the approximate exit times `σ i` are
sandwiched, for every small `δ`, between the exits of `wn i` from `B(z, r - δ)` and `B(z, r + δ)` (`hsand`), then
`σ i → τ` with `τ = (pathExitTime (ball z r) w).toReal`. -/
theorem tendsto_approxExit_toReal {ι : Type*} {l : Filter ι} {z : ℂ} {r : ℝ} (hr : 0 < r)
    {w : ℝ≥0 → ℂ} (hw : Continuous w) (hfin : pathExitTime (ball z r) w ≠ ⊤)
    (hext : ∃ᶠ s in 𝓝[>] (pathExitTime (ball z r) w).toNNReal, r < dist (w s) z)
    {wn : ι → ℝ≥0 → ℂ} (hloc : ∀ T' : ℝ≥0, TendstoUniformlyOn wn w l (Icc 0 T'))
    {σ : ι → ℝ≥0}
    (hsand : ∀ δ : ℝ, 0 < δ → δ < r → ∀ᶠ i in l,
      pathExitTime (ball z (r - δ)) (wn i) ≤ (σ i : ℝ≥0∞) ∧
        (σ i : ℝ≥0∞) ≤ pathExitTime (ball z (r + δ)) (wn i)) :
    Tendsto (fun i => (σ i : ℝ)) l (𝓝 (pathExitTime (ball z r) w).toReal) := by
  have hτ0 : 0 ≤ (pathExitTime (ball z r) w).toReal := ENNReal.toReal_nonneg
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower bound: `a < τ` gives `a < σ i` eventually
    rcases lt_or_ge a 0 with ha0 | ha0
    · exact Eventually.of_forall fun i => lt_of_lt_of_le ha0 (σ i).coe_nonneg
    · obtain ⟨t', ht'⟩ : ∃ t' : ℝ≥0, (t' : ℝ) = (a + (pathExitTime (ball z r) w).toReal) / 2 :=
        ⟨Real.toNNReal _, Real.coe_toNNReal _ (by linarith)⟩
      have hat' : a < (t' : ℝ) := by rw [ht']; linarith
      have ht'τ : (t' : ℝ) < (pathExitTime (ball z r) w).toReal := by rw [ht']; linarith
      -- the limit path stays in `B(z, r)` on `[0, t']`, with maximal distance `M < r` from `z` attained at `s₀`
      obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (by positivity))
        (hw.dist continuous_const : Continuous fun s => dist (w s) z).continuousOn
      have hs₀τ : (s₀ : ℝ) < (pathExitTime (ball z r) w).toReal :=
        lt_of_le_of_lt (NNReal.coe_le_coe.2 hs₀.2) ht'τ
      obtain ⟨M, hM0, hMr, hMle⟩ : ∃ M : ℝ, 0 ≤ M ∧ M < r ∧ ∀ s ∈ Icc (0 : ℝ≥0) t', dist (w s) z ≤ M :=
        ⟨dist (w s₀) z, dist_nonneg, dist_lt_of_lt_toReal_exitTime hfin hs₀τ,
          fun s hs => isMaxOn_iff.1 hmax s hs⟩
      obtain ⟨δ0, hδ0, hδ0r, hδ0M⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < r ∧ M + 2 * δ0 < r :=
        ⟨(r - M) / 4, by linarith, by linarith, by linarith⟩
      filter_upwards [hsand δ0 hδ0 hδ0r, Metric.tendstoUniformlyOn_iff.1 (hloc t') δ0 hδ0] with i hi hun
      have h1 : (t' : ℝ≥0∞) ≤ pathExitTime (ball z (r - δ0)) (wn i) := by
        apply le_pathExitTime_ball_of_dist_lt
        intro s hs
        have hsI : s ∈ Icc (0 : ℝ≥0) t' := ⟨by positivity, hs⟩
        have h2 : dist (wn i s) (w s) < δ0 := by rw [dist_comm]; exact hun s hsI
        have h3 := hMle s hsI
        have h4 := dist_triangle (wn i s) (w s) z
        linarith
      have h5 : t' ≤ σ i := ENNReal.coe_le_coe.1 (h1.trans hi.1)
      exact lt_of_lt_of_le hat' (NNReal.coe_le_coe.2 h5)
  · -- upper bound: `τ < b` gives `σ i < b` eventually
    have hb0 : 0 ≤ b := le_trans hτ0 hb.le
    have hlt : (pathExitTime (ball z r) w).toNNReal < b.toNNReal :=
      NNReal.coe_lt_coe.1 (by rw [Real.coe_toNNReal b hb0]; exact hb)
    -- an exterior visit `s` of the limit path shortly after `τ`, before `b`
    obtain ⟨s, hs, hsext⟩ := Filter.frequently_iff.1 hext (Ioo_mem_nhdsGT hlt)
    have hsb : (s : ℝ) < b := by
      have := NNReal.coe_lt_coe.2 hs.2
      rwa [Real.coe_toNNReal b hb0] at this
    obtain ⟨δ0, hδ0, hδ0r, hδ0η⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < r ∧ δ0 ≤ (dist (w s) z - r) / 2 :=
      ⟨min ((dist (w s) z - r) / 2) (r / 2), lt_min (by linarith) (by linarith),
        lt_of_le_of_lt (min_le_right _ _) (by linarith), min_le_left _ _⟩
    filter_upwards [hsand δ0 hδ0 hδ0r, Metric.tendstoUniformlyOn_iff.1 (hloc s) ((dist (w s) z - r) / 2)
      (by linarith)] with i hi hun
    have hsx : dist (w s) (wn i s) < (dist (w s) z - r) / 2 := hun s ⟨by positivity, le_rfl⟩
    have hdist : r + δ0 ≤ dist (wn i s) z := by
      have h4 := dist_triangle (w s) (wn i s) z
      linarith
    have h1 : pathExitTime (ball z (r + δ0)) (wn i) ≤ (s : ℝ≥0∞) := pathExitTime_ball_le_of_le_dist hdist
    have h2 : (σ i : ℝ≥0∞) ≤ (s : ℝ≥0∞) := hi.2.trans h1
    exact lt_of_le_of_lt (NNReal.coe_le_coe.2 (ENNReal.coe_le_coe.1 h2)) hsb

/-- **Deterministic stopped-integral continuity** (PROOF-REPAIRS-G §G4; the deterministic part of
`TruncatedDetFixedTimeStep`). Under the hypotheses of `tendsto_approxExit_toReal` (locally uniform path convergence,
finite first exit with immediate exterior visit, spatial sandwich of the approximate exit times), and with `wn i`
continuous, for every bounded continuous `g` and every `T`:
`∫_{(0, min T σ_i]} g (wn i t) dt → ∫_{(0, min T τ]} g (w t) dt`. The integrals are taken only up to the exit
(`Do not integrate a stopped path after its exit`, G4). -/
theorem tendsto_stopped_integral_of_locallyUniform {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    {w : ℝ≥0 → ℂ} (hw : Continuous w) (hfin : pathExitTime (ball z r) w ≠ ⊤)
    (hext : ∃ᶠ s in 𝓝[>] (pathExitTime (ball z r) w).toNNReal, r < dist (w s) z)
    {wn : ι → ℝ≥0 → ℂ} (hwn : ∀ i, Continuous (wn i))
    (hloc : ∀ T' : ℝ≥0, TendstoUniformlyOn wn w l (Icc 0 T'))
    {σ : ι → ℝ≥0}
    (hsand : ∀ δ : ℝ, 0 < δ → δ < r → ∀ᶠ i in l,
      pathExitTime (ball z (r - δ)) (wn i) ≤ (σ i : ℝ≥0∞) ∧
        (σ i : ℝ≥0∞) ≤ pathExitTime (ball z (r + δ)) (wn i))
    {g : ℂ → ℝ} (hg : Continuous g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) (T : ℝ) :
    Tendsto (fun i => ∫ t in Ioc (0 : ℝ) (min T (σ i : ℝ)), g (wn i t.toNNReal)) l
      (𝓝 (∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal), g (w t.toNNReal))) := by
  have hA := tendsto_approxExit_toReal hr hw hfin hext hloc hsand
  have hAi : Tendsto (fun i => min T (σ i : ℝ)) l (𝓝 (min T (pathExitTime (ball z r) w).toReal)) :=
    tendsto_const_nhds.min hA
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have key : Tendsto
      (fun i => ∫ t, (Ioc (0 : ℝ) (min T (σ i : ℝ))).indicator (fun t => g (wn i t.toNNReal)) t) l
      (𝓝 (∫ t, (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal)).indicator
        (fun t => g (w t.toNNReal)) t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (Ioc (0 : ℝ) T).indicator (fun _ => C) t) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun i => ?_
      have hcont : Continuous fun t : ℝ => g (wn i t.toNNReal) :=
        hg.comp ((hwn i).comp continuous_real_toNNReal)
      exact hcont.aestronglyMeasurable.indicator measurableSet_Ioc
    · refine Eventually.of_forall fun i => ae_of_all _ fun t => ?_
      by_cases ht : t ∈ Ioc (0 : ℝ) (min T (σ i : ℝ))
      · have htT : t ∈ Ioc (0 : ℝ) T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem htT, Real.norm_eq_abs]
        exact hgC _
      · rw [Set.indicator_of_notMem ht, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hC) t
    · exact (integrable_indicator_iff measurableSet_Ioc).2
        (integrableOn_const (measure_Ioc_lt_top).ne enorm_ne_top)
    · have hae : ∀ᵐ t : ℝ, t ≠ min T (pathExitTime (ball z r) w).toReal := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hae] with t ht
      rcases le_or_gt t 0 with h0 | h0
      · have hz : ∀ i, (Ioc (0 : ℝ) (min T (σ i : ℝ))).indicator (fun t => g (wn i t.toNNReal)) t = 0 :=
          fun i => Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.2 h0)) _
        have hz0 : (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal)).indicator
            (fun t => g (w t.toNNReal)) t = 0 :=
          Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.2 h0)) _
        simp only [hz, hz0]
        exact tendsto_const_nhds
      rcases lt_or_gt_of_ne ht with htA | htA
      · -- before the endpoint: the stopped integrand is eventually active and converges pointwise
        have hev : ∀ᶠ i in l, t < min T (σ i : ℝ) := (tendsto_order.1 hAi).1 t htA
        have hpt : Tendsto (fun i => g (wn i t.toNNReal)) l (𝓝 (g (w t.toNNReal))) :=
          (hg.tendsto _).comp ((hloc t.toNNReal).tendsto_at ⟨by positivity, le_rfl⟩)
        have hmemA : t ∈ Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal) := ⟨h0, htA.le⟩
        rw [Set.indicator_of_mem hmemA (fun t => g (w t.toNNReal))]
        refine hpt.congr' ?_
        filter_upwards [hev] with i hi
        have hmemi : t ∈ Ioc (0 : ℝ) (min T (σ i : ℝ)) := ⟨h0, hi.le⟩
        exact (Set.indicator_of_mem hmemi (fun t => g (wn i t.toNNReal))).symm
      · -- after the endpoint: the stopped integrand is eventually zero
        have hev : ∀ᶠ i in l, min T (σ i : ℝ) < t := (tendsto_order.1 hAi).2 t htA
        have hz0 : (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal)).indicator
            (fun t => g (w t.toNNReal)) t = 0 :=
          Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 htA)) _
        rw [hz0]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with i hi
        exact (Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hi)) _).symm
  have e1 : ∀ i, (∫ t in Ioc (0 : ℝ) (min T (σ i : ℝ)), g (wn i t.toNNReal)) =
      ∫ t, (Ioc (0 : ℝ) (min T (σ i : ℝ))).indicator (fun t => g (wn i t.toNNReal)) t :=
    fun i => (integral_indicator measurableSet_Ioc).symm
  have e0 : (∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal), g (w t.toNNReal)) =
      ∫ t, (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal)).indicator
        (fun t => g (w t.toNNReal)) t :=
    (integral_indicator measurableSet_Ioc).symm
  simp only [e1, e0]
  exact key

end MatedCRT
