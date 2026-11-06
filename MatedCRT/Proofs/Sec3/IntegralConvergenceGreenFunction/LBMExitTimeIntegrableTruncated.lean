import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkKilledConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedFunctional

/-!
# LBM exit time: the truncated exit functional

Path-level ingredients for `LBMExitTimeIntegrableStep`. For a ball `D` and `n : ℕ` the functional
`w ↦ (min (τ_D w) n).toReal` is bounded by `n`. It is monotone in the ball, increases to the exit time
along shrinking balls for continuous paths, and is continuous within continuous paths at finite regular
exits. Measurability in the Brownian variable comes from the bounded Lipschitz envelopes of `PathEnvelopeOn`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The exit time of a path from `D`, truncated at `n` and read as a real number. -/
noncomputable def truncatedExitFunctional (D : Set ℂ) (n : ℕ) (w : ℝ≥0 → ℂ) : ℝ :=
  (min (pathExitTime D w) (n : ℝ≥0∞)).toReal

theorem truncatedExitFunctional_nonneg (D : Set ℂ) (n : ℕ) (w : ℝ≥0 → ℂ) :
    0 ≤ truncatedExitFunctional D n w :=
  ENNReal.toReal_nonneg

theorem truncatedExitFunctional_le (D : Set ℂ) (n : ℕ) (w : ℝ≥0 → ℂ) :
    truncatedExitFunctional D n w ≤ n := by
  unfold truncatedExitFunctional
  have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top n)
    (min_le_right (pathExitTime D w) (n : ℝ≥0∞))
  simpa using h

theorem abs_truncatedExitFunctional_le (D : Set ℂ) (n : ℕ) (w : ℝ≥0 → ℂ) :
    |truncatedExitFunctional D n w| ≤ n := by
  rw [abs_of_nonneg (truncatedExitFunctional_nonneg D n w)]
  exact truncatedExitFunctional_le D n w

theorem ofReal_truncatedExitFunctional (D : Set ℂ) (n : ℕ) (w : ℝ≥0 → ℂ) :
    ENNReal.ofReal (truncatedExitFunctional D n w) = min (pathExitTime D w) (n : ℝ≥0∞) := by
  unfold truncatedExitFunctional
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))

theorem measurable_truncatedExitFunctional_interpolatedWalk (ε : ℝ) (η : ℝ → ℂ) (m : ℝ)
    (z : ℂ) (r : ℝ) (n : ℕ) :
    Measurable (fun x : ℕ → ℤ =>
      truncatedExitFunctional (ball z r) n (interpolatedWalk ε η m x)) := by
  unfold truncatedExitFunctional
  exact ((measurable_pathExitTime_interpolatedWalk ε η m z r).min measurable_const).ennreal_toReal

theorem pathExitTime_mono_set {U V : Set ℂ} (h : U ⊆ V) (w : ℝ≥0 → ℂ) :
    pathExitTime U w ≤ pathExitTime V w := by
  unfold pathExitTime
  exact sInf_le_sInf fun c ⟨t, hc, ht⟩ => ⟨t, hc, fun hu => ht (h hu)⟩

theorem pathExitTime_le_of_not_mem {U : Set ℂ} {w : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : w t ∉ U) :
    pathExitTime U w ≤ (t : ℝ≥0∞) :=
  sInf_le ⟨t, rfl, ht⟩

theorem le_pathExitTime_of_forall_mem {U : Set ℂ} {w : ℝ≥0 → ℂ} {t : ℝ≥0}
    (h : ∀ s ≤ t, w s ∈ U) : (t : ℝ≥0∞) ≤ pathExitTime U w := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨u, rfl, hu⟩
  rw [ENNReal.coe_le_coe]
  by_contra hlt
  exact hu (h u (le_of_lt (not_le.mp hlt)))

theorem mem_of_lt_pathExitTime {U : Set ℂ} {w : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < pathExitTime U w) : w t ∈ U := by
  by_contra hw
  exact absurd ht (not_lt.mpr (pathExitTime_le_of_not_mem hw))

/-- For a continuous path, the exit times of the balls `B(z, a k)` increase to the exit time of `B(z, r)`
when `a k ↑ r` with `a k < r`. -/
theorem pathExitTime_iSup_ball {z : ℂ} {r : ℝ} (a : ℕ → ℝ)
    (ha_lt : ∀ k, a k < r) (ha_lim : Tendsto a atTop (𝓝 r)) {w : ℝ≥0 → ℂ} (hw : Continuous w) :
    ⨆ k, pathExitTime (ball z (a k)) w = pathExitTime (ball z r) w := by
  apply le_antisymm
  · exact iSup_le fun k => pathExitTime_mono_set (ball_subset_ball (ha_lt k).le) w
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨c', hcc', hc'⟩ := exists_between hc
    refine lt_of_lt_of_le hcc' ?_
    have hfin : c' ≠ ⊤ := ne_top_of_lt hc'
    have ht : ((c'.toNNReal : ℝ≥0) : ℝ≥0∞) = c' := ENNReal.coe_toNNReal hfin
    rw [← ht] at hc' ⊢
    have hmem : ∀ s ≤ c'.toNNReal, w s ∈ ball z r := fun s hs =>
      mem_of_lt_pathExitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) hc')
    have hcont : ContinuousOn (fun s : ℝ≥0 => dist (w s) z) (Icc (0 : ℝ≥0) c'.toNNReal) :=
      (hw.dist continuous_const).continuousOn
    obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := c'.toNNReal)).exists_isMaxOn
      (Set.nonempty_Icc.2 zero_le) hcont
    have hM : dist (w s₀) z < r := mem_ball.1 (hmem s₀ hs₀.2)
    obtain ⟨k, hk⟩ := (ha_lim.eventually (Ioi_mem_nhds hM)).exists
    have hk' : dist (w s₀) z < a k := hk
    have hball : ((c'.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ pathExitTime (ball z (a k)) w := by
      refine le_pathExitTime_of_forall_mem fun s hs => ?_
      rw [mem_ball]
      have h1 : dist (w s) z ≤ dist (w s₀) z := isMaxOn_iff.1 hmax s ⟨zero_le, hs⟩
      exact lt_of_le_of_lt h1 hk'
    exact hball.trans (le_iSup (fun k => pathExitTime (ball z (a k)) w) k)

/-- **Continuity of the truncated exit functional** (within continuous paths) at a finite regular exit. -/
theorem pathFunctionalContinuousWithinAt_truncatedExit (p : ContinuousPath ℂ) (z : ℂ) {r : ℝ}
    (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r) (n : ℕ) :
    PathFunctionalContinuousWithinAt {w | Continuous w} (truncatedExitFunctional (ball z r) n) p := by
  have hτ := tendsto_ball_exitTime_of_localUniformDist
    (l := comap (fun v => localUniformDist v p) (𝓝 0)) p z r hfin hregular (fun v => v) tendsto_comap
  have hne : min (ContinuousPath.exitTime (ball z r) p) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
  have hG : Tendsto (truncatedExitFunctional (ball z r) n)
      (comap (fun v => localUniformDist v p) (𝓝 0))
      (𝓝 (truncatedExitFunctional (ball z r) n p)) := by
    unfold truncatedExitFunctional
    exact (ENNReal.tendsto_toReal hne).comp (hτ.min tendsto_const_nhds)
  intro η hη
  obtain ⟨ρ, hρ, hclose⟩ :=
    ((Metric.nhds_basis_ball.comap _).eventually_iff).1 (Metric.tendsto_nhds.1 hG η hη)
  refine ⟨ρ, hρ, fun v _ hd => ?_⟩
  have hv : v ∈ (fun v => localUniformDist v p) ⁻¹' ball 0 ρ := by
    change dist (localUniformDist v p) 0 < ρ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (localUniformDist_nonneg v p)]
    exact hd
  have h := hclose hv
  rw [Real.dist_eq] at h
  exact h.le

/-- An a.e. limit of the bounded Lipschitz envelopes gives a.e. strong measurability of a functional
which is continuous within continuous paths at a.e. path. -/
theorem aestronglyMeasurable_of_envelopes {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {X : β → ℝ≥0 → ℂ} {G : (ℝ≥0 → ℂ) → ℝ} (hG : ∀ w : ℝ≥0 → ℂ, Continuous w → |G w| ≤ 1)
    (hF : ∀ k : ℕ, AEStronglyMeasurable
      (fun b => pathUpperEnvelopeOn {w | Continuous w} G (k : ℝ) (X b)) μ)
    (hcont : ∀ᵐ b ∂μ, Continuous (X b) ∧
      PathFunctionalContinuousWithinAt {w | Continuous w} G (X b)) :
    AEStronglyMeasurable (fun b => G (X b)) μ := by
  have hlim : ∀ᵐ b ∂μ, Tendsto (fun k : ℕ => pathUpperEnvelopeOn {w | Continuous w} G (k : ℝ) (X b))
      atTop (𝓝 (G (X b))) := by
    filter_upwards [hcont] with b hb
    exact tendsto_pathUpperEnvelopeOn (fun w hw => hG w hw) hb.1 hb.2
  exact aestronglyMeasurable_of_tendsto_ae atTop hF hlim

/-- The same for a functional bounded by `c > 0` on continuous paths: the envelopes are taken of `G / c`. -/
theorem aestronglyMeasurable_of_envelopes_scaled {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {X : β → ℝ≥0 → ℂ} {G : (ℝ≥0 → ℂ) → ℝ} {c : ℝ} (hc : 0 < c)
    (hG : ∀ w : ℝ≥0 → ℂ, Continuous w → |G w| ≤ c)
    (hF : ∀ k : ℕ, AEStronglyMeasurable
      (fun b => pathUpperEnvelopeOn {w | Continuous w} (fun v => G v / c) (k : ℝ) (X b)) μ)
    (hcont : ∀ᵐ b ∂μ, Continuous (X b) ∧
      PathFunctionalContinuousWithinAt {w | Continuous w} G (X b)) :
    AEStronglyMeasurable (fun b => G (X b)) μ := by
  have hc0 : c ≠ 0 := hc.ne'
  have hG' : ∀ w : ℝ≥0 → ℂ, Continuous w → |G w / c| ≤ 1 := fun w hw => by
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    exact hG w hw
  have hcont' : ∀ᵐ b ∂μ, Continuous (X b) ∧
      PathFunctionalContinuousWithinAt {w | Continuous w} (fun v => G v / c) (X b) := by
    filter_upwards [hcont] with b hb
    exact ⟨hb.1, hb.2.div_const c⟩
  have key := aestronglyMeasurable_of_envelopes hG' hF hcont'
  refine (key.const_mul c).congr (Eventually.of_forall fun b => ?_)
  show c * (G (X b) / c) = G (X b)
  field_simp

end MatedCRT
