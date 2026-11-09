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

open Classical in
/-- **H7 step L3 (q1, fp-S2g; membership in the supersolutions at radius `ρ`).** The all-radii candidate is continuous
(L1), a Laplacian sub-solution (L2b) and dominates the obstacle `-t G_{B_ρ}(0,·)` off the pole. Off `B_{3/4}` it equals the
obstacle; on `B_{3/4}` the domination is `hlow` rewritten by the centre formula (`log (3/(4‖x‖)) = log (3/(4ρ)) + log (ρ/‖x‖)`),
and on the sphere `‖x‖ = ρ` the Green function of `B_ρ` vanishes (sphere zero of `GreenFunctionBallStmt`). -/
theorem allDisksCandidate_mem_supersolutions (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {W : ℂ → ℝ} {t ρ : ℝ} {A : Set ℂ}
    (hρ : 0 < ρ) (hWc : ContinuousOn W (closedBall (0 : ℂ) (3 / 4)))
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), W x = 0)
    (hW : HasLaplacian W (μ.restrict A) 0 (ball (0 : ℂ) (3 / 4)))
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    (hA : A ⊆ ball (0 : ℂ) (1 / 2)) (hAopen : IsOpen A) (hA0 : (0 : ℂ) ∈ A) :
    allDisksCandidate W t ρ ∈ supersolutions μ ρ 0 t := by
  refine ⟨allDisksCandidate_continuousOn hC hGB hpole hρ hWc hsph,
    allDisksCandidate_laplacianLE hC hGB hpole hρ hWc hsph hW hlow hobs hA hAopen hA0, ?_⟩
  intro x hxρ hx0
  have hxn : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.mp hxρ
  by_cases h3 : x ∈ ball (0 : ℂ) (3 / 4)
  · have hn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have h3n : ‖x‖ < 3 / 4 := mem_ball_zero_iff.mp h3
    have hlw := hlow x (ball_subset_closedBall h3) hx0
    rw [hC (3 / 4) (by norm_num) x hn0 h3n] at hlw
    have hl : Real.log ((3 / 4 : ℝ) / ‖x‖) = Real.log (3 / (4 * ρ)) + Real.log (ρ / ‖x‖) := by
      rw [← Real.log_mul (div_pos (by norm_num) (mul_pos (by norm_num) hρ)).ne' (div_pos hρ hn0).ne']
      congr 1
      field_simp
    rw [hl] at hlw
    simp only [allDisksCandidate, h3, ↓reduceIte]
    rcases lt_or_eq_of_le hxn with hlt | heq
    · rw [hC ρ hρ x hn0 hlt]
      linarith
    · have hG0 : greenFunction (ball (0 : ℂ) ρ) 0 x = 0 :=
        ((hGB ρ hρ 0 (mem_ball_self hρ)).2.2.1 x (mem_sphere_zero_iff_norm.mpr heq)).1
      have hlog : Real.log (ρ / ‖x‖) = 0 := by rw [heq, div_self hρ.ne', Real.log_one]
      rw [hlog, add_zero] at hlw
      rw [hG0, mul_zero]
      linarith
  · simp only [allDisksCandidate, h3, ↓reduceIte, le_refl]

open Classical in
/-- **H7 sphere clause (q1, fp-S2g).** For `A ⊆ B_r` with `r < ρ`, the all-radii candidate vanishes on `∂B_ρ`. Off
`B_{3/4}` it is the obstacle `-t G_{B_ρ}(0,·)`, which vanishes on the sphere. For `ρ < 3/4` the sphere lies in `B_{3/4} \ A`,
where `W = -t G_{B_{3/4}}(0,·)`, so the candidate is `-t G_{B_{3/4}}(0,·) + t (2π)⁻¹ log (3/(4ρ)) = 0`. -/
theorem allDisksCandidate_sphere_eq_zero (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    {W : ℂ → ℝ} {t ρ r : ℝ} {A : Set ℂ} (hρ : 0 < ρ) (hr : r < ρ) (hAr : A ⊆ ball (0 : ℂ) r)
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x) :
    ∀ y ∈ sphere (0 : ℂ) ρ, allDisksCandidate W t ρ y = 0 := by
  intro y hy
  have hyA : y ∉ A := fun h => by
    have h1 : ‖y‖ < r := mem_ball_zero_iff.mp (hAr h)
    have h2 : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    linarith
  by_cases h3 : y ∈ ball (0 : ℂ) (3 / 4)
  · have hn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      linarith
    have hWy : W y = -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 y :=
      le_antisymm (hobs y h3 hyA) (hlow y (ball_subset_closedBall h3) hy0)
    have hG3 := hC (3 / 4) (by norm_num) y (norm_pos_iff.mpr hy0) (mem_ball_zero_iff.mp h3)
    simp only [allDisksCandidate, h3, ↓reduceIte]
    rw [hWy, hG3, hn]
    have hq : (3 / 4 : ℝ) / ρ = 3 / (4 * ρ) := by ring
    rw [hq]
    ring
  · simp only [allDisksCandidate, h3, ↓reduceIte]
    have hG0 : greenFunction (ball (0 : ℂ) ρ) 0 y = 0 :=
      ((hGB ρ hρ 0 (mem_ball_self hρ)).2.2.1 y hy).1
    rw [hG0, mul_zero]

open Classical in
/-- **H7 step L4 (q1, fp-S2g; least-ness at radius `ρ`).** Let `A ⊆ B_r` with `r < ρ`. The all-radii candidate is the least
supersolution at radius `ρ` on `closedBall 0 ρ`: it is a certificate for `certificate_le_supersolution` (zero on `∂B_ρ`, which
lies outside `A`; below the obstacle off `A`, by the centre formula at `3/4` and `hobs`). On `∂B_ρ` with `ρ < 3/4` the value
`W = -t G_{B_{3/4}}(0,·)` (off `A`) makes the candidate `-t G_{B_ρ}(0,·) = 0`. -/
theorem leastSupersolution_eq_allDisksCandidate (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {W : ℂ → ℝ} {t ρ r : ℝ} {A : Set ℂ}
    (hρ : 0 < ρ) (hr : r < ρ) (hAr : A ⊆ ball (0 : ℂ) r)
    (hWc : ContinuousOn W (closedBall (0 : ℂ) (3 / 4)))
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), W x = 0)
    (hW : HasLaplacian W (μ.restrict A) 0 (ball (0 : ℂ) (3 / 4)))
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    (hA : A ⊆ ball (0 : ℂ) (1 / 2)) (hAopen : IsOpen A) (hA0 : (0 : ℂ) ∈ A) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, leastSupersolution μ ρ 0 t x = allDisksCandidate W t ρ x := by
  intro x hx
  have hmem := allDisksCandidate_mem_supersolutions hC hGB hpole hρ hWc hsph hW hlow hobs hA hAopen hA0
  have hAρ : A ⊆ ball (0 : ℂ) ρ := hAr.trans (ball_subset_ball hr.le)
  have hbd := allDisksCandidate_sphere_eq_zero hC hGB hρ hr hAr hlow hobs
  have hcov : ∀ y ∈ ball (0 : ℂ) ρ, y ∉ A → allDisksCandidate W t ρ y ≤ -t * greenFunction (ball (0 : ℂ) ρ) 0 y := by
    intro y hyρ hyA
    have hy0 : y ≠ 0 := fun h => hyA (by rw [h]; exact hA0)
    by_cases h3 : y ∈ ball (0 : ℂ) (3 / 4)
    · rw [allDisksCandidate_eq_of_centre hC hρ h3 hyρ hy0]
      have := hobs y h3 hyA
      linarith
    · simp only [allDisksCandidate, h3, ↓reduceIte, le_refl]
  have hC4 := allDisksCandidate_hasLaplacian hC hGB hpole hρ hWc hsph hW hlow hobs hA hAopen hA0
  have hμ : μ (closedBall (0 : ℂ) ρ) < ⊤ := measure_closedBall_lt_top
  have hle := certificate_le_supersolution hmin hμ hmem hbd hAopen hA0 hAρ hcov hC4
  unfold leastSupersolution
  refine IsLeast.csInf_eq ⟨⟨allDisksCandidate W t ρ, hmem, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hle v hv x hx

/-- **H7 step L5 (q1, fp-S2g; the cluster does not depend on the radius).** If `cluster μ (3/4) 0 t ⊆ B_ρ` and `W` is the
radius-`3/4` least supersolution on `B_{3/4}`, the cluster at radius `ρ` equals the cluster at radius `3/4`: inside
`B_{3/4}` both are `{x ≠ 0 : -t G_{B_{3/4}}(0,x) < W x} ∪ {0}` (the centre formula cancels `-t G_{B_ρ}`), and outside
`B_{3/4}` the candidate is the obstacle, so the radius-`ρ` cluster has no points there. -/
theorem cluster_eq_cluster_three_quarters (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {W : ℂ → ℝ} {t ρ r : ℝ} {A : Set ℂ}
    (hρ : 0 < ρ) (hr : r < ρ) (hAr : A ⊆ ball (0 : ℂ) r)
    (hWc : ContinuousOn W (closedBall (0 : ℂ) (3 / 4)))
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), W x = 0)
    (hW : HasLaplacian W (μ.restrict A) 0 (ball (0 : ℂ) (3 / 4)))
    (hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ W x)
    (hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A → W x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x)
    (hA : A ⊆ ball (0 : ℂ) (1 / 2)) (hAopen : IsOpen A) (hA0 : (0 : ℂ) ∈ A)
    (hWls : ∀ x ∈ ball (0 : ℂ) (3 / 4), leastSupersolution μ (3 / 4) 0 t x = W x)
    (hcl : cluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) ρ) :
    cluster μ ρ 0 t = cluster μ (3 / 4) 0 t := by
  have hLS := leastSupersolution_eq_allDisksCandidate hmin hC hGB hpole hρ hr hAr hWc hsph hW hlow hobs hA hAopen hA0
  ext x
  simp only [cluster, Set.mem_ofPred_eq]
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨fun _ => ⟨mem_ball_self (by norm_num), Or.inl rfl⟩, fun _ => ⟨mem_ball_self hρ, Or.inl rfl⟩⟩
  · constructor
    · rintro ⟨hxρ, hxl⟩
      have hxl' := hxl.resolve_left hx0
      rw [hLS x (ball_subset_closedBall hxρ)] at hxl'
      by_cases h3 : x ∈ ball (0 : ℂ) (3 / 4)
      · rw [allDisksCandidate_eq_of_centre hC hρ h3 hxρ hx0] at hxl'
        refine ⟨h3, Or.inr ?_⟩
        rw [hWls x h3]
        linarith
      · exfalso
        simp only [allDisksCandidate, h3, ↓reduceIte] at hxl'
        exact lt_irrefl _ hxl'
    · rintro ⟨h3, hxl⟩
      have hxl' := hxl.resolve_left hx0
      have hmemc : x ∈ cluster μ (3 / 4) 0 t := by
        simp only [cluster, Set.mem_ofPred_eq]
        exact ⟨h3, Or.inr hxl'⟩
      have hxρ : x ∈ ball (0 : ℂ) ρ := hcl hmemc
      refine ⟨hxρ, Or.inr ?_⟩
      rw [hLS x (ball_subset_closedBall hxρ), allDisksCandidate_eq_of_centre hC hρ h3 hxρ hx0]
      rw [hWls x h3] at hxl'
      linarith

/-- Transfer of `HasLaplacian` along an equality on `B_ρ`: the test integrals of `w` and `w'` agree, since the test functions
vanish off `B_ρ` and the Laplacian of a test function vanishes off its support. -/
theorem hasLaplacian_of_eqOn_ball {w w' : ℂ → ℝ} {μp μn : Measure ℂ} {ρ : ℝ}
    (hw : HasLaplacian w' μp μn (ball (0 : ℂ) ρ)) (hcw : ContinuousOn w (closedBall (0 : ℂ) ρ))
    (h : EqOn w w' (ball (0 : ℂ) ρ)) : HasLaplacian w μp μn (ball (0 : ℂ) ρ) := by
  obtain ⟨-, hid⟩ := hw
  refine ⟨(hcw.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hid φ hφ
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : ℂ) ρ
  · rw [h hx]
  · rw [laplacian_eq_zero_off_tsupport (fun hT => hx (hφ.2.2 hT)), mul_zero, mul_zero]

open Classical in
/-- **H7 obstacle clause at every radius (q1, fp-S2g).** Given the radius-`3/4` data at time `t`: the least supersolution
`v = leastSupersolution μ (3/4) 0 t` is a supersolution, vanishes on `∂B_{3/4}`, has Laplacian `μ|_A` on `B_{3/4}` for
`A = interior (closure (cluster μ (3/4) 0 t))`, and the cluster is open; and `A ⊆ B_r` with `r < ρ`. Then the four clauses of
`SatisfiesObstacleCharacterizationOn` hold at radius `ρ` with the same set `A`. The obstacle inequality off `A` (`hobs`) is
read off the cluster: `cluster ⊆ A` by openness, and `x ∉ cluster` means `v x ≤ -t G_{B_{3/4}}(0,x)`. -/
theorem obstacle_clause_all_radii (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hC : FrozenGreenBallCentre) (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {t r ρ : ℝ}
    (hopen : IsOpen (cluster μ (3 / 4) 0 t))
    (hmem : leastSupersolution μ (3 / 4) 0 t ∈ supersolutions μ (3 / 4) 0 t)
    (hsph : ∀ x ∈ sphere (0 : ℂ) (3 / 4), leastSupersolution μ (3 / 4) 0 t x = 0)
    (hW_lap : HasLaplacian (leastSupersolution μ (3 / 4) 0 t)
      (μ.restrict (interior (closure (cluster μ (3 / 4) 0 t)))) 0 (ball (0 : ℂ) (3 / 4)))
    (hA12 : interior (closure (cluster μ (3 / 4) 0 t)) ⊆ ball (0 : ℂ) (1 / 2))
    (hAr : interior (closure (cluster μ (3 / 4) 0 t)) ⊆ ball (0 : ℂ) r) (hr : r < ρ) :
    interior (closure (cluster μ ρ 0 t)) = interior (closure (cluster μ (3 / 4) 0 t)) ∧
      ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall (0 : ℂ) ρ) ∧
      HasLaplacian (leastSupersolution μ ρ 0 t) (μ.restrict (interior (closure (cluster μ (3 / 4) 0 t))))
        0 (ball (0 : ℂ) ρ) ∧
      ∀ x ∈ sphere (0 : ℂ) ρ, leastSupersolution μ ρ 0 t x = 0 := by
  set A := interior (closure (cluster μ (3 / 4) 0 t)) with hAdef
  have hcA : cluster μ (3 / 4) 0 t ⊆ A := interior_maximal subset_closure hopen
  have h0c : (0 : ℂ) ∈ cluster μ (3 / 4) 0 t := by
    simp only [cluster, Set.mem_ofPred_eq, true_or, and_true]
    exact mem_ball_self (by norm_num)
  have hA0 : (0 : ℂ) ∈ A := hcA h0c
  have hr0 : 0 < r := by
    have h := mem_ball_zero_iff.mp (hAr hA0)
    simpa using h
  have hρ : 0 < ρ := hr0.trans hr
  have hWc : ContinuousOn (leastSupersolution μ (3 / 4) 0 t) (closedBall (0 : ℂ) (3 / 4)) := hmem.1
  have hlow : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 →
      -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x ≤ leastSupersolution μ (3 / 4) 0 t x :=
    fun x hx hx0 => hmem.2.2 x hx hx0
  have hobs : ∀ x ∈ ball (0 : ℂ) (3 / 4), x ∉ A →
      leastSupersolution μ (3 / 4) 0 t x ≤ -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x := by
    intro x hx3 hxA
    by_contra hlt
    have hlt' : -t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x < leastSupersolution μ (3 / 4) 0 t x :=
      not_le.mp hlt
    apply hxA
    apply hcA
    simp only [cluster, Set.mem_ofPred_eq]
    exact ⟨hx3, Or.inr hlt'⟩
  have hLS := leastSupersolution_eq_allDisksCandidate hmin hC hGB hpole hρ hr hAr hWc hsph hW_lap hlow hobs hA12
    isOpen_interior hA0
  have hbd := allDisksCandidate_sphere_eq_zero hC hGB hρ hr hAr hlow hobs
  have hcl : cluster μ (3 / 4) 0 t ⊆ ball (0 : ℂ) ρ := hcA.trans (hAr.trans (ball_subset_ball hr.le))
  have hEq := cluster_eq_cluster_three_quarters hmin hC hGB hpole hρ hr hAr hWc hsph hW_lap hlow hobs hA12
    isOpen_interior hA0 (fun x _ => rfl) hcl
  have hcont : ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall (0 : ℂ) ρ) :=
    (allDisksCandidate_continuousOn hC hGB hpole hρ hWc hsph).congr (fun x hx => hLS x hx)
  refine ⟨by rw [hEq], hcont, ?_, ?_⟩
  · exact hasLaplacian_of_eqOn_ball
      (allDisksCandidate_hasLaplacian hC hGB hpole hρ hWc hsph hW_lap hlow hobs hA12 isOpen_interior hA0) hcont
      (fun x hx => hLS x (ball_subset_closedBall hx))
  · intro x hx
    rw [hLS x (sphere_subset_closedBall hx)]
    exact hbd x hx

end MatedCRT
