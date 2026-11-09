import MatedCRT.FirstPass.S2g.AllDisks

/-! # All-disks candidate: continuity up to the boundary (fp-S2g, q1; CHATGPT-q1-open-steps.md H7, step L1)

For the candidate `allDisksCandidate W t ρ` of `AllDisks.lean`: if `W` is continuous on `closedBall 0 (3/4)` and vanishes on
`sphere 0 (3/4)` (clauses 2 and 4 of the radius-`3/4` obstacle characterization), then the candidate is continuous on
`closedBall 0 ρ` for every `ρ > 0`. The two pieces agree on the sphere `∂B_{3/4}`: `W = 0` there and the centre formula
gives `-t G_{B_ρ}(0,·) = t (2π)⁻¹ log (3/(4ρ))`; at `ρ = 3/4` the Green function vanishes on the sphere. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ContDiff

open Classical in
/-- **H7 step L1 (q1, fp-S2g).** The all-radii candidate is continuous on the closed ball `closedBall 0 ρ`. -/
theorem allDisksCandidate_continuousOn (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole) {W : ℂ → ℝ} {t ρ : ℝ} (hρ : 0 < ρ)
    (hWc : ContinuousOn W (closedBall (0 : ℂ) (3 / 4)))
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), W x = 0) :
    ContinuousOn (allDisksCandidate W t ρ) (closedBall (0 : ℂ) ρ) := by
  have hb : (3 / 4 : ℝ) ≠ 0 := by norm_num
  have hfr : frontier (ball (0 : ℂ) (3 / 4)) = sphere (0 : ℂ) (3 / 4) := frontier_ball _ hb
  have hcl : closure (ball (0 : ℂ) (3 / 4)) = closedBall (0 : ℂ) (3 / 4) := closure_ball _ hb
  unfold allDisksCandidate
  refine ContinuousOn.if (p := fun x => x ∈ ball (0 : ℂ) (3 / 4)) ?_ ?_ ?_
  · -- the two formulas agree on the frontier `sphere 0 (3/4)`
    rintro x ⟨hxρ, hxf⟩
    have hx3 : x ∈ sphere (0 : ℂ) (3 / 4) := by
      rw [← hfr]
      exact hxf
    have hn : ‖x‖ = 3 / 4 := mem_sphere_zero_iff_norm.mp hx3
    have hxρ' : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.mp hxρ
    show W x + t * ((2 * Real.pi)⁻¹ * Real.log (3 / (4 * ρ))) = -t * greenFunction (ball (0 : ℂ) ρ) 0 x
    rw [hsph x hx3, zero_add]
    rcases lt_trichotomy (3 / 4 : ℝ) ρ with hlt | heq | hgt
    · have hxpos : 0 < ‖x‖ := by rw [hn]; norm_num
      have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
      have hxR : ‖x‖ < ρ := by rw [hn]; exact hlt
      rw [hC ρ hρ x hxpos hxR, hn]
      have hl : Real.log (3 / (4 * ρ)) = -Real.log (ρ / (3 / 4)) := by
        rw [← Real.log_inv, inv_div]
        congr 1
        ring
      rw [hl]
      ring
    · rw [← heq]
      have hG0 : greenFunction (ball (0 : ℂ) (3 / 4)) 0 x = 0 :=
        ((hGB (3 / 4) (by norm_num) 0 (mem_ball_self (by norm_num))).2.2.1 x hx3).1
      have h1 : (3 : ℝ) / (4 * (3 / 4)) = 1 := by norm_num
      rw [hG0, h1, Real.log_one]
      ring
    · exact absurd hxρ' (by rw [hn]; linarith)
  · -- the potential part: `W + c` on `closedBall 0 (3/4)`
    rw [Set.ofPred_mem_eq, hcl]
    exact (hWc.mono inter_subset_right).add continuousOn_const
  · -- the Green part: `-t G_{B_ρ}(0,·)` away from the pole
    have hsub : closedBall (0 : ℂ) ρ ∩ closure {a : ℂ | ¬ a ∈ ball (0 : ℂ) (3 / 4)} ⊆ closedBall (0 : ℂ) ρ \ {0} := by
      rintro x ⟨hxρ, hxc⟩
      have h2 : x ∈ (ball (0 : ℂ) (3 / 4))ᶜ :=
        closure_minimal (fun y hy => hy) isOpen_ball.isClosed_compl hxc
      refine ⟨hxρ, fun h0 => h2 ?_⟩
      rw [Set.mem_singleton_iff.mp h0]
      exact mem_ball_self (by norm_num)
    exact continuousOn_const.mul ((hpole ρ hρ).1.mono hsub)

open Classical in
/-- **H7 step L2a (q1, fp-S2g; clause 3 at radius `ρ`).** The all-radii candidate has Laplacian `μ|_A` on `B_ρ`, with the
Laplacian identity of `allDisks_integral_identity` as its distributional content (the candidate is locally integrable on
`B_ρ` by L1). -/
theorem allDisksCandidate_hasLaplacian (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {W : ℂ → ℝ} {t ρ : ℝ} {A : Set ℂ}
    (hρ : 0 < ρ) (hWc : ContinuousOn W (closedBall (0 : ℂ) (3 / 4)))
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), W x = 0)
    (hW : HasLaplacian W (μ.restrict A) 0 (ball (0 : ℂ) (3 / 4)))
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    (hA : A ⊆ ball (0 : ℂ) (1 / 2)) (hAopen : IsOpen A) (hA0 : (0 : ℂ) ∈ A) :
    HasLaplacian (allDisksCandidate W t ρ) (μ.restrict A) 0 (ball (0 : ℂ) ρ) := by
  refine ⟨((allDisksCandidate_continuousOn hC hGB hpole hρ hWc hsph).mono ball_subset_closedBall).locallyIntegrableOn
    measurableSet_ball, ?_⟩
  intro φ hφ
  refine ⟨hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1, integrable_zero_measure, ?_⟩
  rw [allDisks_integral_identity hC hGB hρ hW hlow hobs hA hAopen hA0 hφ]
  simp

open Classical in
/-- **H7 step L2b (q1, fp-S2g; `LaplacianLE` of the candidate).** The candidate is a Laplacian sub-solution `ΔW ≤ μ` on
`B_ρ`, since `μ|_A ≤ μ` and the test functions are nonnegative. -/
theorem allDisksCandidate_laplacianLE (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {W : ℂ → ℝ} {t ρ : ℝ} {A : Set ℂ}
    (hρ : 0 < ρ) (hWc : ContinuousOn W (closedBall (0 : ℂ) (3 / 4)))
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), W x = 0)
    (hW : HasLaplacian W (μ.restrict A) 0 (ball (0 : ℂ) (3 / 4)))
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    (hA : A ⊆ ball (0 : ℂ) (1 / 2)) (hAopen : IsOpen A) (hA0 : (0 : ℂ) ∈ A) :
    LaplacianLE (allDisksCandidate W t ρ) μ (ball (0 : ℂ) ρ) := by
  refine ⟨((allDisksCandidate_continuousOn hC hGB hpole hρ hWc hsph).mono ball_subset_closedBall).locallyIntegrableOn
    measurableSet_ball, ?_⟩
  intro φ hφ hφ0 hφi
  rw [allDisks_integral_identity hC hGB hρ hW hlow hobs hA hAopen hA0 hφ]
  exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => hφ0 x)) hφi

end MatedCRT
