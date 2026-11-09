import MatedCRT.Defs.Setting

/-!
# FIRST PASS, Lemma 5.3 (three-inputs A7, positive test function)

Deterministic (measure theory and smooth bump functions), no frozen input. If `U ⊆ ℂ` is open with `0 < μ U < ∞`, then
some test function `φ` in `U` (`HarmonicBalls.IsTestFunction`, smooth with compact support in `U`) is nonnegative and
has `∫ φ dμ > 0`. Proof: a countable family of rational balls `ball q r` with `closedBall q (2r) ⊆ U` covers `U`, so one
of them has positive mass; a normalized `ContDiffBump` supported in `ball q (3r/2)` then has positive integral.
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Metric Set Filter Topology

/-- Some rational ball `ball q r` with `closedBall q (2r) ⊆ U` has positive mass when `μ U > 0` (countable cover). -/
theorem exists_good_ball_pos {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hpos : 0 < μ U) :
    ∃ q : ℂ, ∃ r : ℝ, 0 < r ∧ closedBall q (2 * r) ⊆ U ∧ 0 < μ (ball q r) := by
  by_contra hcon
  push Not at hcon
  let G : Set (ℚ × ℚ × ℚ) := {p | 0 < (p.2.2 : ℝ) ∧
    closedBall (⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩ : ℂ) (2 * (p.2.2 : ℝ)) ⊆ U}
  have hG : G.Countable := Set.to_countable G
  have hcover : U ⊆ ⋃ p ∈ G, ball (⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩ : ℂ) (p.2.2 : ℝ) := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by positivity)
    obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show x.re - (r : ℝ) / 2 < x.re + (r : ℝ) / 2 by linarith)
    obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show x.im - (r : ℝ) / 2 < x.im + (r : ℝ) / 2 by linarith)
    set c : ℂ := ⟨(q1 : ℝ), (q2 : ℝ)⟩ with hc
    have hdist : dist x c < (r : ℝ) := by
      rw [dist_eq_norm]
      have h1 := Complex.norm_le_abs_re_add_abs_im (x - c)
      simp only [Complex.sub_re, Complex.sub_im, hc] at h1
      have a1 : |x.re - (q1 : ℝ)| < (r : ℝ) / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      have a2 : |x.im - (q2 : ℝ)| < (r : ℝ) / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      linarith
    refine Set.mem_biUnion (x := (q1, q2, r)) ?_ (by simpa [dist_eq_norm] using hdist)
    refine ⟨hr0, fun y hy => hεU ?_⟩
    rw [mem_ball]
    have hyc : dist y c ≤ 2 * (r : ℝ) := mem_closedBall.1 hy
    have h3 : dist y x ≤ dist y c + dist c x := dist_triangle y c x
    have h4 : dist c x = dist x c := dist_comm _ _
    linarith
  have hnull : μ (⋃ p ∈ G, ball (⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩ : ℂ) (p.2.2 : ℝ)) = 0 := by
    refine (measure_biUnion_null_iff hG).2 fun p hp => ?_
    exact le_antisymm (hcon _ _ hp.1 hp.2) zero_le
  exact hpos.ne' (measure_mono_null hcover hnull)

/-- A nonnegative smooth test function in `U` with positive integral against `μ`, when `0 < μ U < ∞`. -/
theorem exists_test_integral_pos {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hfin : μ U ≠ ⊤) (hpos : 0 < μ U) :
    ∃ φ : ℂ → ℝ, IsTestFunction U φ ∧ 0 ≤ φ ∧ Integrable φ μ ∧ 0 < ∫ x, φ x ∂μ := by
  obtain ⟨q, r, hr, hcl, hball⟩ := exists_good_ball_pos hU hpos
  let b : ContDiffBump q := ⟨r, 3 * r / 2, hr, by linarith⟩
  have hsupp : Function.support (b.normed (volume : Measure ℂ)) = ball q (3 * r / 2) :=
    b.support_normed_eq
  have htsupp : tsupport (b.normed (volume : Measure ℂ)) = closedBall q (3 * r / 2) :=
    b.tsupport_normed_eq
  have hsubU : closedBall q (3 * r / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hcl
  have hcont : Continuous (b.normed (volume : Measure ℂ)) := (b.contDiff_normed (n := ⊤)).continuous
  have hintR : Integrable (b.normed (volume : Measure ℂ)) (μ.restrict U) := by
    have : IsFiniteMeasure (μ.restrict U) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
    exact hcont.integrable_of_hasCompactSupport b.hasCompactSupport_normed
  have hsuppU : Function.support (b.normed (volume : Measure ℂ)) ⊆ U := by
    rw [hsupp]
    exact (ball_subset_closedBall).trans hsubU
  have hint : Integrable (b.normed (volume : Measure ℂ)) μ :=
    (integrableOn_iff_integrable_of_support_subset hsuppU).1 hintR
  refine ⟨b.normed (volume : Measure ℂ), ⟨b.contDiff_normed, b.hasCompactSupport_normed, ?_⟩, ?_, hint, ?_⟩
  · rw [htsupp]
    exact hsubU
  · intro x
    exact b.nonneg_normed x
  · rw [integral_pos_iff_support_of_nonneg (fun x => b.nonneg_normed x) hint, hsupp]
    exact lt_of_lt_of_le hball (measure_mono (ball_subset_ball (by linarith)))

end MatedCRT.S5c
