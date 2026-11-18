import MatedCRT.FirstPass.Derived.BrownianGoodStopExitWitness

/-!
# The inside-ball clause of the good stopping event, uniformly in the starting point

Clause (c) of `MatedCRT.StopAtExitCmp.GoodStop (ball 0 R) T η d ε f` asks that at every rational time `q` with
`q + η / 4 < τ` (`τ` the exit time of `ball 0 R`) the whole `d`-ball about `f q` lies inside `ball 0 R`. For a
continuous path `b` this fails only if the path comes within `d` of the circle of radius `R` at a time
`q ≤ τ - η / 4`. Then `b` has left `ball 0 (R - d)` by time `q`, and the post-exit increments `δ_t` of the exit time
`σ` of `ball 0 (R - d)` satisfy `⟪b σ, δ_t⟫ ≤ (R - d) d` at every rational `t ∈ (0, η / 4)`, because `b (σ + t)` is
still in `ball 0 R`. By the strong Markov property at `σ` and the rotation invariance of the Brownian law, the
probability of this event does not depend on the exit position and tends to `0` as `d → 0`.

* `MatedCRT.StopAtExitCmp.insideBad`: the paths violating clause (c).
* `MatedCRT.StopAtExitCmp.postIncr_inner_le_of_mem_insideBad`: the deterministic reduction.
* `MatedCRT.StopAtExitCmp.exists_forall_planarBrownianMotion_insideBad_lt`: the uniform bound.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal
open MatedCRT.ExitRestart

namespace MatedCRT.StopAtExitCmp

/-- The paths violating the inside-ball clause (c) of `GoodStop (ball 0 R) T η d ε`. -/
def insideBad (R : ℝ) (η : ℝ≥0) (d : ℝ) : Set (ContinuousPath ℂ) :=
  {b | ¬ ∀ q : ℚ, ((ratTime q + η / 4 : ℝ≥0) : ℝ≥0∞) < pathExitTime (ball (0 : ℂ) R) ⇑b →
      ∀ w, dist w (b (ratTime q)) < d → w ∈ ball (0 : ℂ) R}

/-- **Deterministic reduction.** If the exit time `σ` of `ball 0 (R - d)` is finite, the exit position lies on the
circle of radius `R - d`, and clause (c) fails, then `⟪b σ, δ_t⟫ ≤ (R - d) d` for the post-exit increments `δ_t`
at every rational `t ∈ (0, η / 4)`. -/
theorem postIncr_inner_le_of_mem_insideBad {R : ℝ} {η : ℝ≥0} {d : ℝ} {b : ContinuousPath ℂ}
    (hfin : ContinuousPath.exitTime (ball (0 : ℂ) (R - d)) b ≠ ⊤)
    (hx : ‖b (exitNN (ball (0 : ℂ) (R - d)) b)‖ = R - d) (hb : b ∈ insideBad R η d) :
    ∀ q : ℚ, 0 < q → (q : ℝ) < ((η / 4 : ℝ≥0) : ℝ) →
      (b (exitNN (ball (0 : ℂ) (R - d)) b)).re *
          (postIncr (exitNN (ball (0 : ℂ) (R - d))) b (Real.toNNReal q)).re +
        (b (exitNN (ball (0 : ℂ) (R - d)) b)).im *
          (postIncr (exitNN (ball (0 : ℂ) (R - d))) b (Real.toNNReal q)).im ≤ (R - d) * d := by
  intro q0 hq0 hq0η
  have hb' : ¬ ∀ q : ℚ, ((ratTime q + η / 4 : ℝ≥0) : ℝ≥0∞) < pathExitTime (ball (0 : ℂ) R) ⇑b →
      ∀ w, dist w (b (ratTime q)) < d → w ∈ ball (0 : ℂ) R := hb
  push Not at hb'
  obtain ⟨q, hq, w, hw, hwU⟩ := hb'
  set τ : ℝ≥0 := exitNN (ball (0 : ℂ) (R - d)) b with hτ
  set x : ℂ := b τ with hxdef
  have hpe : pathExitTime (ball (0 : ℂ) (R - d)) ⇑b = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hwR : R ≤ ‖w‖ := by rwa [mem_ball_zero_iff, not_lt] at hwU
  have h1 : ‖w‖ ≤ ‖b (ratTime q)‖ + dist w (b (ratTime q)) := by
    rw [dist_eq_norm]; exact norm_le_insert' _ _
  have hnot : b (ratTime q) ∉ ball (0 : ℂ) (R - d) := by
    rw [mem_ball_zero_iff, not_lt]; linarith
  have hτq : τ ≤ ratTime q := by
    have := exitTime_le_of_not_mem hnot
    rw [hpe] at this
    exact_mod_cast this
  set t0 : ℝ≥0 := Real.toNNReal q0 with ht0
  have ht0le : t0 ≤ η / 4 := Real.toNNReal_le_iff_le_coe.2 hq0η.le
  have hsum : τ + t0 ≤ ratTime q + η / 4 := add_le_add hτq ht0le
  have hy : b (τ + t0) ∈ ball (0 : ℂ) R :=
    mem_of_lt_exitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsum) hq)
  set y : ℂ := b (τ + t0) with hydef
  have hδ : postIncr (exitNN (ball (0 : ℂ) (R - d))) b t0 = y - x := rfl
  rw [hδ]
  have hyR : ‖y‖ < R := mem_ball_zero_iff.1 hy
  have hRd : 0 ≤ R - d := by rw [← hx]; exact norm_nonneg _
  have hxx : x.re * x.re + x.im * x.im = (R - d) * (R - d) := by
    have h := Complex.sq_norm x
    rw [hx, Complex.normSq_apply] at h
    nlinarith [h]
  have hcs : x.re * y.re + x.im * y.im ≤ ‖x‖ * ‖y‖ := by
    have := real_inner_le_norm x y
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at this
    linarith
  rw [hx] at hcs
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith [mul_le_mul_of_nonneg_left hyR.le hRd]

/-- **The inside-ball clause, uniformly in the start.** For `0 ≤ ρ < R`, `θ > 0` and `η > 0` there is `d > 0`,
`d < R - ρ`, such that for planar Brownian motion started at every point of `closedBall 0 ρ` the clause (c) of
`GoodStop (ball 0 R) T η d ε` fails with probability less than `θ`. -/
theorem exists_forall_planarBrownianMotion_insideBad_lt {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) {θ : ℝ}
    (hθ : 0 < θ) {η : ℝ≥0} (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ d < R - ρ ∧
      ∀ z ∈ closedBall (0 : ℂ) ρ, planarBrownianMotion z (insideBad R η d) < ENNReal.ofReal θ := by
  have hη4 : 0 < η / 4 := div_pos hη (by norm_num)
  have hθ0 : 0 < ENNReal.ofReal θ := ENNReal.ofReal_pos.2 hθ
  obtain ⟨d, ⟨hd, hdρ⟩, hd0⟩ := ((((tendsto_muPlanar_nonPosBefore hη4).eventually
    (gt_mem_nhds hθ0)).and (eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (sub_pos.2 hρR)))).and self_mem_nhdsWithin).exists
  have hd0' : 0 < d := hd0
  refine ⟨d, hd0', hdρ, fun z hz => ?_⟩
  have hzn : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.1 hz
  have hRd : 0 < R - d := by linarith
  have hzR : z ∈ ball (0 : ℂ) (R - d) := by rw [mem_ball_zero_iff]; linarith
  have hfin : ∀ᵐ b ∂(planarBrownianMotion z), ContinuousPath.exitTime (ball (0 : ℂ) (R - d)) b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top z
      (Metric.isBounded_ball (x := (0 : ℂ)) (r := R - d))).mono fun _ hb => hb.ne
  have hSae : ∀ᵐ b ∂(planarBrownianMotion z),
      b (exitNN (ball (0 : ℂ) (R - d)) b) ∈ sphere (0 : ℂ) (R - d) := by
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero z] with b hb hb0
    have hmem0 : b 0 ∈ ball (0 : ℂ) (R - d) := by rw [hb0]; exact hzR
    have := ContinuousPath.coordinate_exitTime_mem_frontier (ball (0 : ℂ) (R - d)) isOpen_ball b hmem0 hb
    rwa [frontier_ball (0 : ℂ) hRd.ne'] at this
  have hpair := planarBrownianMotion_exit_pair_le isOpen_ball z hfin
    (measurableSet_pairBound (η / 4) ((R - d) * d))
    (show IsClosed (sphere (0 : ℂ) (R - d)) from isClosed_sphere).measurableSet hSae
    (p := muPlanar (nonPosBefore (η / 4) d))
    (fun y hy => (muPlanar_section_pairBound hRd (η / 4) d (mem_sphere_zero_iff_norm.1 hy)).le)
  have hnull : planarBrownianMotion z {b : ContinuousPath ℂ | ¬ (ContinuousPath.exitTime (ball (0 : ℂ) (R - d)) b ≠ ⊤ ∧
      ‖b (exitNN (ball (0 : ℂ) (R - d)) b)‖ = R - d)} = 0 := by
    refine ae_iff.1 ?_
    filter_upwards [hfin, hSae] with b h1 h2
    exact ⟨h1, mem_sphere_zero_iff_norm.1 h2⟩
  have hsub : insideBad R η d ⊆
      ({b : ContinuousPath ℂ | (b (exitNN (ball (0 : ℂ) (R - d)) b),
          postIncr (exitNN (ball (0 : ℂ) (R - d))) b) ∈ {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q →
            (q : ℝ) < ((η / 4 : ℝ≥0) : ℝ) →
              p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ (R - d) * d}} ∪
        {b : ContinuousPath ℂ | ¬ (ContinuousPath.exitTime (ball (0 : ℂ) (R - d)) b ≠ ⊤ ∧
          ‖b (exitNN (ball (0 : ℂ) (R - d)) b)‖ = R - d)}) := by
    intro b hb
    by_cases hgood : ContinuousPath.exitTime (ball (0 : ℂ) (R - d)) b ≠ ⊤ ∧
        ‖b (exitNN (ball (0 : ℂ) (R - d)) b)‖ = R - d
    · exact Or.inl fun q hq0 hqη => postIncr_inner_le_of_mem_insideBad hgood.1 hgood.2 hb q hq0 hqη
    · exact Or.inr hgood
  calc planarBrownianMotion z (insideBad R η d)
      ≤ planarBrownianMotion z
        ({b : ContinuousPath ℂ | (b (exitNN (ball (0 : ℂ) (R - d)) b),
          postIncr (exitNN (ball (0 : ℂ) (R - d))) b) ∈ {p : ℂ × (ℝ≥0 → ℂ) | ∀ q : ℚ, 0 < q →
            (q : ℝ) < ((η / 4 : ℝ≥0) : ℝ) →
              p.1.re * (p.2 (Real.toNNReal q)).re + p.1.im * (p.2 (Real.toNNReal q)).im ≤ (R - d) * d}} ∪
        {b : ContinuousPath ℂ | ¬ (ContinuousPath.exitTime (ball (0 : ℂ) (R - d)) b ≠ ⊤ ∧
          ‖b (exitNN (ball (0 : ℂ) (R - d)) b)‖ = R - d)}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ muPlanar (nonPosBefore (η / 4) d) + 0 := add_le_add hpair hnull.le
    _ < ENNReal.ofReal θ := by rw [add_zero]; exact hd

end MatedCRT.StopAtExitCmp
