import MatedCRT.FirstPass.Derived.BrownianGoodStopUniform
import MatedCRT.FirstPass.Derived.BrownianExitRestartBound
import MatedCRT.FirstPass.Derived.BrownianDirectionExcursion

/-!
# The exit-witness clause of the good stopping event, uniformly in the starting point

Clause (a) of `MatedCRT.StopAtExitCmp.GoodStop (ball 0 R) T η d ε f` asks for a rational time `q` in
`(τ, τ + η)`, `q ≤ T`, at which the `d`-ball about `f q` lies outside the disc (`τ` the exit time). For planar
Brownian motion `b` this is a statement about the post-exit increments `δ_t = b (τ + t) - b τ`: if no such rational
time exists then, writing `x = b τ` (`‖x‖ = R`), the inner product `⟪x, δ_t⟫` is at most `R d` at every rational
`t ∈ (0, η)`. By the strong Markov property at the exit time and the rotation invariance of the Brownian law, the
probability of this event does not depend on the exit position and tends to `0` as `d → 0`.

* `MatedCRT.StopAtExitCmp.witnessBad`: the paths violating clause (a).
* `MatedCRT.StopAtExitCmp.postIncr_inner_le_of_mem_witnessBad`: the deterministic reduction.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal
open MatedCRT.ExitRestart

namespace MatedCRT.StopAtExitCmp

/-- The paths violating the exit-witness clause (a) of `GoodStop (ball 0 R) T η d ε`. -/
def witnessBad (R : ℝ) (T η : ℝ≥0) (d : ℝ) : Set (ContinuousPath ℂ) :=
  {b | ¬ ∃ q : ℚ, pathExitTime (ball (0 : ℂ) R) ⇑b < ratTime q ∧
    (ratTime q : ℝ≥0∞) < pathExitTime (ball (0 : ℂ) R) ⇑b + η ∧ ratTime q ≤ T ∧
      ∀ w, dist w (b (ratTime q)) < d → w ∉ ball (0 : ℂ) R}

/-- **Deterministic reduction.** If the exit time of `ball 0 R` is finite, the exit position `x` lies on the circle
of radius `R`, the exit happens by time `T - η`, and clause (a) fails, then `⟪x, δ_t⟫ ≤ R d` for the post-exit
increments `δ_t` at every rational `t ∈ (0, η)`. -/
theorem postIncr_inner_le_of_mem_witnessBad {R : ℝ} {T η : ℝ≥0} {d : ℝ} {b : ContinuousPath ℂ}
    (hfin : ContinuousPath.exitTime (ball (0 : ℂ) R) b ≠ ⊤)
    (hT : exitNN (ball (0 : ℂ) R) b + η ≤ T) (hx : ‖b (exitNN (ball (0 : ℂ) R) b)‖ = R)
    (hb : b ∈ witnessBad R T η d) :
    ∀ q : ℚ, 0 < q → (q : ℝ) < η →
      (b (exitNN (ball (0 : ℂ) R) b)).re * (postIncr (exitNN (ball (0 : ℂ) R)) b (Real.toNNReal q)).re +
        (b (exitNN (ball (0 : ℂ) R) b)).im * (postIncr (exitNN (ball (0 : ℂ) R)) b (Real.toNNReal q)).im
          ≤ R * d := by
  intro q0 hq0 hq0η
  by_contra hlt
  rw [not_le] at hlt
  set τ : ℝ≥0 := exitNN (ball (0 : ℂ) R) b with hτ
  set x : ℂ := b τ with hxdef
  have hpe : pathExitTime (ball (0 : ℂ) R) ⇑b = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  set t0 : ℝ≥0 := Real.toNNReal q0 with ht0
  have ht0real : (t0 : ℝ) = q0 := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  set y : ℂ := b (τ + t0) with hydef
  have hδ : postIncr (exitNN (ball (0 : ℂ) R)) b t0 = y - x := rfl
  rw [hδ] at hlt
  have hR : 0 ≤ R := by rw [← hx]; exact norm_nonneg _
  have hxx : x.re * x.re + x.im * x.im = R * R := by
    have h := Complex.sq_norm x
    rw [hx, Complex.normSq_apply] at h
    nlinarith [h]
  have hcs : x.re * y.re + x.im * y.im ≤ ‖x‖ * ‖y‖ := by
    have := real_inner_le_norm x y
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at this
    linarith
  rw [hx] at hcs
  have hy : R + d < ‖y‖ := by
    simp only [Complex.sub_re, Complex.sub_im] at hlt
    have h1 : R * (R + d) < R * ‖y‖ := by nlinarith [hlt, hxx, hcs]
    exact lt_of_mul_lt_mul_left h1 hR
  have hf : Continuous (b : ℝ≥0 → ℂ) := b.continuous
  have hr : 0 < (‖y‖ - (R + d)) / 2 := by linarith
  have hδη : 0 < (η : ℝ) - q0 := by linarith
  obtain ⟨q', hq1, hq2, hq3⟩ := exists_ratTime_near hf (τ + t0) hr hδη
  have hq2' : (ratTime q' : ℝ) < τ + η := by
    have : ((τ + t0 : ℝ≥0) : ℝ) = τ + q0 := by push_cast; rw [ht0real]
    rw [this] at hq2
    linarith
  have hlt1 : (τ : ℝ≥0) < ratTime q' := lt_of_le_of_lt (le_self_add) hq1
  apply hb
  refine ⟨q', ?_, ?_, ?_, ?_⟩
  · rw [hpe]; exact_mod_cast hlt1
  · rw [hpe]
    have : ratTime q' < τ + η := by exact_mod_cast hq2'
    exact_mod_cast this
  · have : ratTime q' < τ + η := by exact_mod_cast hq2'
    exact (this.trans_le hT).le
  · intro w hw hwU
    rw [mem_ball_zero_iff] at hwU
    have h1 : ‖b (ratTime q')‖ ≤ ‖w‖ + dist w (b (ratTime q')) := by
      rw [dist_comm, dist_eq_norm]; exact norm_le_insert' _ _
    have h2 : ‖y‖ ≤ ‖b (ratTime q')‖ + dist (b (ratTime q')) y := by
      rw [dist_comm, dist_eq_norm]; exact norm_le_insert' _ _
    have h3 : dist (b (ratTime q')) y < (‖y‖ - (R + d)) / 2 := hq3
    linarith

/-- **Tail of the exit time.** The probability that planar Brownian motion from `0` stays in `ball 0 r` up to time
`n` tends to `0` as `n → ∞`. -/
theorem tendsto_planarBrownianMotion_zero_le_exitTime {r : ℝ} :
    Tendsto (fun n : ℕ => planarBrownianMotion (0 : ℂ)
      {b : ContinuousPath ℂ | (n : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) r) b}) atTop (𝓝 0) := by
  have hτm := ContinuousPath.measurable_exitTime (ball (0 : ℂ) r) isOpen_ball
  have hlim := tendsto_measure_iInter_atTop (μ := planarBrownianMotion (0 : ℂ))
    (s := fun n : ℕ => {b : ContinuousPath ℂ | (n : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) r) b})
    (fun n => (measurableSet_le measurable_const hτm).nullMeasurableSet)
    (fun i j hij b (hb : (j : ℝ≥0∞) ≤ _) => (show (i : ℝ≥0∞) ≤ _ from (Nat.cast_le.2 hij).trans hb))
    ⟨0, measure_ne_top _ _⟩
  have h0 : planarBrownianMotion (0 : ℂ) (⋂ n : ℕ,
      {b : ContinuousPath ℂ | (n : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) r) b}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_planarBrownianMotion_exit_any_ball_lt_top (0 : ℂ) (0 : ℂ) r))
    intro b hb hlt
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hlt.ne
    exact absurd (mem_iInter.1 hb n) (not_le.2 hn)
  rw [h0] at hlim
  exact hlim

/-- Uniform tail of the exit time from `ball 0 R` for starting points in `closedBall 0 ρ`. -/
theorem planarBrownianMotion_exitTime_gt_le {z : ℂ} {ρ R : ℝ} (hz : ‖z‖ ≤ ρ) (n : ℕ) :
    planarBrownianMotion z {b : ContinuousPath ℂ | (n : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) R) b} ≤
      planarBrownianMotion (0 : ℂ)
        {b : ContinuousPath ℂ | (n : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) (R + ρ)) b} := by
  rw [planarBrownianMotion_apply_eq_translatePath]
  refine measure_mono fun b (hb : (n : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) R) (translatePath z b)) => ?_
  show (n : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) (R + ρ)) b
  refine le_sInf ?_
  rintro t ⟨s, rfl, hs⟩
  by_contra hlt
  rw [not_le] at hlt
  have hmem := ContinuousPath.mem_of_lt_exitTime (ball (0 : ℂ) R) (translatePath z b) s (hlt.trans hb)
  rw [translatePath_apply, mem_ball_zero_iff] at hmem
  apply hs
  rw [mem_ball_zero_iff]
  calc ‖b s‖ = ‖(b s + z) - z‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖b s + z‖ + ‖z‖ := norm_sub_le _ _
    _ < R + ρ := by linarith

/-- The set of pairs (position, path) with `⟪position, path q⟫ ≤ c` at all rational `q ∈ (0, η)` is measurable. -/
theorem measurableSet_pairBound (η : ℝ≥0) (c : ℝ) :
    MeasurableSet {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
      p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ c} := by
  have hset : {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
      p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ c} =
      ⋂ q : ℚ, {p : ℂ × (ℝ≥0 → ℂ) | 0 < q → (q : ℝ) < η →
        p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ c} := by
    ext p
    simp
  rw [hset]
  refine MeasurableSet.iInter fun q => ?_
  by_cases h : 0 < q ∧ (q : ℝ) < η
  · have hmeas : Measurable fun p : ℂ × (ℝ≥0 → ℂ) =>
        p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im :=
      ((Complex.measurable_re.comp measurable_fst).mul
        (Complex.measurable_re.comp ((measurable_pi_apply _).comp measurable_snd))).add
      ((Complex.measurable_im.comp measurable_fst).mul
        (Complex.measurable_im.comp ((measurable_pi_apply _).comp measurable_snd)))
    have : {p : ℂ × (ℝ≥0 → ℂ) | 0 < q → (q : ℝ) < η →
        p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ c} =
        (fun p : ℂ × (ℝ≥0 → ℂ) =>
          p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im) ⁻¹' Iic c := by
      ext p
      simp [h.1, h.2]
    rw [this]
    exact hmeas measurableSet_Iic
  · have : {p : ℂ × (ℝ≥0 → ℂ) | 0 < q → (q : ℝ) < η →
        p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ c} = univ := by
      ext p
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [this]
    exact MeasurableSet.univ

/-- The section at a point `y` of the circle of radius `R` has `muPlanar`-measure `muPlanar (nonPosBefore η d)`. -/
theorem muPlanar_section_pairBound {R : ℝ} (hR : 0 < R) (η : ℝ≥0) (d : ℝ) {y : ℂ} (hy : ‖y‖ = R) :
    muPlanar (Prod.mk y ⁻¹' {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
      p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ R * d}) =
      muPlanar (nonPosBefore η d) := by
  set n : ℂ := ((R⁻¹ : ℝ) : ℂ) * y with hn
  have hnorm : ‖n‖ = 1 := by
    rw [hn, norm_mul, hy, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR),
      inv_mul_cancel₀ hR.ne']
  rw [← muPlanar_dirNonPos_eq η d hnorm]
  congr 1
  ext δ
  simp only [mem_preimage, mem_ofPred_eq]
  refine forall_congr' fun q => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  have h1 : n.re * (δ (Real.toNNReal q)).re + n.im * (δ (Real.toNNReal q)).im =
      R⁻¹ * (y.re * (δ (Real.toNNReal q)).re + y.im * (δ (Real.toNNReal q)).im) := by
    simp [hn]
    ring
  rw [h1, inv_mul_le_iff₀ hR]

/-- **The exit-witness clause, uniformly in the start.** For `0 ≤ ρ < R` and `θ > 0` there is a horizon `T ≥ 1`
such that for every `η ∈ (0, 1]` there is `d > 0` with: for planar Brownian motion started at every point of
`closedBall 0 ρ`, the clause (a) of `GoodStop (ball 0 R) T η d ε` fails with probability less than `θ`. -/
theorem exists_forall_planarBrownianMotion_witnessBad_lt {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ T : ℝ≥0, 1 ≤ T ∧ ∀ η : ℝ≥0, 0 < η → η ≤ 1 → ∃ d : ℝ, 0 < d ∧
      ∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z (witnessBad R T η d) < ENNReal.ofReal θ := by
  have hR : 0 < R := lt_of_le_of_lt hρ hρR
  have hθ2 : 0 < ENNReal.ofReal (θ / 2) := ENNReal.ofReal_pos.2 (half_pos hθ)
  obtain ⟨n, hn⟩ := ((tendsto_planarBrownianMotion_zero_le_exitTime (r := R + ρ)).eventually
    (gt_mem_nhds hθ2)).exists
  refine ⟨(n : ℝ≥0) + 1, le_add_self, fun η hη hη1 => ?_⟩
  obtain ⟨d, hd, hd0⟩ := (((tendsto_muPlanar_nonPosBefore hη).eventually (gt_mem_nhds hθ2)).and
    self_mem_nhdsWithin).exists
  have hd0' : 0 < d := hd0
  refine ⟨d, hd0', fun z hz => ?_⟩
  have hzn : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.1 hz
  have hzR : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hzn hρR
  have hfin : ∀ᵐ b ∂(planarBrownianMotion z), ContinuousPath.exitTime (ball (0 : ℂ) R) b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top z
      (Metric.isBounded_ball (x := (0 : ℂ)) (r := R))).mono fun _ hb => hb.ne
  have hSae : ∀ᵐ b ∂(planarBrownianMotion z), b (exitNN (ball (0 : ℂ) R) b) ∈ sphere (0 : ℂ) R := by
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero z] with b hb hb0
    have hmem0 : b 0 ∈ ball (0 : ℂ) R := by rw [hb0]; exact hzR
    have := ContinuousPath.coordinate_exitTime_mem_frontier (ball (0 : ℂ) R) isOpen_ball b hmem0 hb
    rwa [frontier_ball (0 : ℂ) hR.ne'] at this
  have hpair := planarBrownianMotion_exit_pair_le isOpen_ball z hfin
    (measurableSet_pairBound η (R * d)) (show IsClosed (sphere (0 : ℂ) R) from isClosed_sphere).measurableSet hSae
    (p := muPlanar (nonPosBefore η d))
    (fun y hy => (muPlanar_section_pairBound hR η d (mem_sphere_zero_iff_norm.1 hy)).le)
  have hnull : planarBrownianMotion z {b : ContinuousPath ℂ | ¬ (ContinuousPath.exitTime (ball (0 : ℂ) R) b ≠ ⊤ ∧
      ‖b (exitNN (ball (0 : ℂ) R) b)‖ = R)} = 0 := by
    refine ae_iff.1 ?_
    filter_upwards [hfin, hSae] with b h1 h2
    exact ⟨h1, mem_sphere_zero_iff_norm.1 h2⟩
  have hsub : witnessBad R ((n : ℝ≥0) + 1) η d ⊆
      {b : ContinuousPath ℂ | (n : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) R) b} ∪
        ({b : ContinuousPath ℂ | (b (exitNN (ball (0 : ℂ) R) b),
            postIncr (exitNN (ball (0 : ℂ) R)) b) ∈ {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
              p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ R * d}} ∪
          {b : ContinuousPath ℂ | ¬ (ContinuousPath.exitTime (ball (0 : ℂ) R) b ≠ ⊤ ∧
            ‖b (exitNN (ball (0 : ℂ) R) b)‖ = R)}) := by
    intro b hb
    by_cases htail : (n : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) R) b
    · exact Or.inl htail
    · refine Or.inr ?_
      by_cases hgood : ContinuousPath.exitTime (ball (0 : ℂ) R) b ≠ ⊤ ∧
          ‖b (exitNN (ball (0 : ℂ) R) b)‖ = R
      · refine Or.inl ?_
        have hle : exitNN (ball (0 : ℂ) R) b ≤ n := by
          have := ENNReal.toNNReal_mono (ENNReal.natCast_ne_top n) (not_lt.1 htail)
          simpa [exitNN] using this
        have hT : exitNN (ball (0 : ℂ) R) b + η ≤ (n : ℝ≥0) + 1 := add_le_add hle hη1
        exact fun q hq0 hqη => postIncr_inner_le_of_mem_witnessBad hgood.1 hT hgood.2 hb q hq0 hqη
      · exact Or.inr hgood
  have hP1 := planarBrownianMotion_exitTime_gt_le (z := z) (ρ := ρ) (R := R) hzn n
  calc planarBrownianMotion z (witnessBad R ((n : ℝ≥0) + 1) η d)
      ≤ planarBrownianMotion z ({b : ContinuousPath ℂ | (n : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) R) b} ∪
        ({b : ContinuousPath ℂ | (b (exitNN (ball (0 : ℂ) R) b),
            postIncr (exitNN (ball (0 : ℂ) R)) b) ∈ {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
              p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ R * d}} ∪
          {b : ContinuousPath ℂ | ¬ (ContinuousPath.exitTime (ball (0 : ℂ) R) b ≠ ⊤ ∧
            ‖b (exitNN (ball (0 : ℂ) R) b)‖ = R)})) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ planarBrownianMotion (0 : ℂ)
          {b : ContinuousPath ℂ | (n : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) (R + ρ)) b} +
        (muPlanar (nonPosBefore η d) + 0) := by
      refine add_le_add hP1 ?_
      refine (measure_union_le _ _).trans (add_le_add hpair ?_)
      exact hnull.le
    _ < ENNReal.ofReal (θ / 2) + (ENNReal.ofReal (θ / 2) + 0) :=
      ENNReal.add_lt_add_of_lt_of_le (by simp) hn
        (add_le_add hd.le le_rfl)
    _ = ENNReal.ofReal θ := by
      rw [add_zero, ← ENNReal.ofReal_add (half_pos hθ).le (half_pos hθ).le, add_halves]

end MatedCRT.StopAtExitCmp
