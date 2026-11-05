import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExitOscillation
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit

/-!
# Lemma 3.6: the bad-window functional

`exitWindowBad z r d h η w = 1` if, on the window `[τ_{B_{r-d}(z)}(w), τ_{B_r(z)}(w) + h]`,
the path `w` moves farther than `η` from its exit position, and `0` otherwise. Near a
path with a regular exit it vanishes identically for small `d, h`
(`exists_exitWindow_dist_le`); hence its Pasch--Hausdorff envelopes, taken along the
diagonal `d = h = 1/(n+1)`, `k = n`, tend to `0` at almost every rescaled LBM path.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

open Classical in
/-- The indicator that a path moves farther than `η` from its exit position on the exit window. -/
noncomputable def exitWindowBad (z : ℂ) (r d : ℝ) (h : ℝ≥0) (η : ℝ) (w : ℝ≥0 → ℂ) : ℝ :=
  if ∃ s : ℝ≥0, pathExitTime (ball z (r - d)) w ≤ s ∧
      (s : ℝ≥0∞) ≤ pathExitTime (ball z r) w + h ∧
      η < dist (w s) (pathExitPosition (ball z r) w) then 1 else 0

theorem exitWindowBad_nonneg (z : ℂ) (r d : ℝ) (h : ℝ≥0) (η : ℝ) (w : ℝ≥0 → ℂ) :
    0 ≤ exitWindowBad z r d h η w := by
  unfold exitWindowBad
  split_ifs <;> norm_num

theorem abs_exitWindowBad_le_one (z : ℂ) (r d : ℝ) (h : ℝ≥0) (η : ℝ) (w : ℝ≥0 → ℂ) :
    |exitWindowBad z r d h η w| ≤ 1 := by
  unfold exitWindowBad
  split_ifs <;> norm_num

/-- Exit times are monotone in the domain. -/
theorem pathExitTime_mono {U V : Set ℂ} (hUV : U ⊆ V) (w : ℝ≥0 → ℂ) :
    pathExitTime U w ≤ pathExitTime V w := by
  unfold pathExitTime
  exact sInf_le_sInf fun s ⟨t, hs, ht⟩ => ⟨t, hs, fun hU => ht (hUV hU)⟩

/-- A good path (no bad window) satisfies the oscillation bound at every window time. -/
theorem dist_le_of_exitWindowBad_eq_zero {z : ℂ} {r d : ℝ} {h : ℝ≥0} {η : ℝ}
    {w : ℝ≥0 → ℂ} (hw : exitWindowBad z r d h η w = 0) {s : ℝ≥0}
    (hs1 : pathExitTime (ball z (r - d)) w ≤ s)
    (hs2 : (s : ℝ≥0∞) ≤ pathExitTime (ball z r) w + h) :
    dist (w s) (pathExitPosition (ball z r) w) ≤ η := by
  unfold exitWindowBad at hw
  split_ifs at hw with hc
  · norm_num at hw
  · by_contra hlt
    exact hc ⟨s, hs1, hs2, not_le.mp hlt⟩

/-- Shrinking the window can only make the bad event smaller. -/
theorem exitWindowBad_eq_zero_of_le {z : ℂ} {r d d' : ℝ} {h h' : ℝ≥0} {η : ℝ}
    {w : ℝ≥0 → ℂ} (hd : d ≤ d') (hh : h ≤ h') (hw : exitWindowBad z r d' h' η w = 0) :
    exitWindowBad z r d h η w = 0 := by
  unfold exitWindowBad
  rw [ite_eq_right]
  rintro ⟨s, hs1, hs2, hs3⟩
  have h1 : pathExitTime (ball z (r - d')) w ≤ s :=
    (pathExitTime_mono (ball_subset_ball (by linarith)) w).trans hs1
  have h2 : (s : ℝ≥0∞) ≤ pathExitTime (ball z r) w + h' :=
    hs2.trans (by gcongr)
  exact absurd (dist_le_of_exitWindowBad_eq_zero hw h1 h2) (not_le.mpr hs3)

/-- If a bounded functional vanishes on a `ρ`-neighbourhood of `p`, its `k`-th
envelope at `p` is at most `max 0 (1 - k ρ)`. -/
theorem pathUpperEnvelope_le_of_nonpos_near {G : (ℝ≥0 → ℂ) → ℝ} (hG : ∀ w, |G w| ≤ 1)
    {k : ℝ} (hk : 0 ≤ k) {p : ℝ≥0 → ℂ} {ρ : ℝ}
    (hnear : ∀ v, localUniformDist v p < ρ → G v ≤ 0) :
    pathUpperEnvelope G k p ≤ max 0 (1 - k * ρ) := by
  refine ciSup_le fun v => ?_
  have hd := localUniformDist_nonneg v p
  rcases lt_or_ge (localUniformDist v p) ρ with hlt | hge
  · have := hnear v hlt
    have := mul_nonneg hk hd
    exact (by linarith : G v - k * localUniformDist v p ≤ 0).trans (le_max_left _ _)
  · have := (abs_le.mp (hG v)).2
    have := mul_le_mul_of_nonneg_left hge hk
    exact (by linarith : G v - k * localUniformDist v p ≤ 1 - k * ρ).trans (le_max_right _ _)

/-- The diagonal bad-window functional `Φ_n = exitWindowBad z r (1/(n+1)) (1/(n+1)) η`. -/
noncomputable def diagonalBad (z : ℂ) (r η : ℝ) (n : ℕ) : (ℝ≥0 → ℂ) → ℝ :=
  exitWindowBad z r (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)).toNNReal η

/-- At a path with a regular exit, the diagonal envelopes `U_n Φ_n` tend to zero. -/
theorem tendsto_pathUpperEnvelope_diagonalBad (p : ContinuousPath ℂ) (z : ℂ) {r : ℝ}
    (h0 : p 0 ∈ ball z r) (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => pathUpperEnvelope (diagonalBad z r η n) n p) atTop (𝓝 0) := by
  obtain ⟨d₀, hd₀, h₀, hh₀, ρ, hρ, hosc⟩ := exists_exitWindow_dist_le p z h0 hfin hregular hη
  have hzero : ∀ v, localUniformDist v p < ρ → exitWindowBad z r d₀ h₀ η v = 0 := by
    intro v hv
    unfold exitWindowBad
    rw [ite_eq_right]
    rintro ⟨s, hs1, hs2, hs3⟩
    exact absurd (hosc v hv s hs1 hs2) (not_le.mpr hs3)
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ d₀ ∧
      (1 / ((n : ℝ) + 1)).toNNReal ≤ h₀ := by
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hh₀' : (0 : ℝ) < h₀ := hh₀
    filter_upwards [ht.eventually (ge_mem_nhds hd₀), ht.eventually (ge_mem_nhds hh₀')]
      with n h1 h2
    exact ⟨h1, Real.toNNReal_le_iff_le_coe.2 h2⟩
  have hupper : ∀ᶠ n : ℕ in atTop,
      pathUpperEnvelope (diagonalBad z r η n) n p ≤ max 0 (1 - n * ρ) := by
    filter_upwards [hsmall] with n hn
    refine pathUpperEnvelope_le_of_nonpos_near (abs_exitWindowBad_le_one z r _ _ η)
      (Nat.cast_nonneg n) fun v hv => ?_
    exact (exitWindowBad_eq_zero_of_le hn.1 hn.2 (hzero v hv)).le
  have hlower : ∀ n : ℕ, 0 ≤ pathUpperEnvelope (diagonalBad z r η n) n p := fun n =>
    (exitWindowBad_nonneg z r _ _ η p).trans
      (le_pathUpperEnvelope (abs_exitWindowBad_le_one z r _ _ η) (Nat.cast_nonneg n) p)
  have hmax : Tendsto (fun n : ℕ => max 0 (1 - (n : ℝ) * ρ)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ρ)
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 1 / ρ * ρ = 1 := div_mul_cancel₀ 1 hρ.ne'
    have h3 : 1 ≤ (n : ℝ) * ρ := by nlinarith
    rw [max_eq_left (by linarith)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmax
    (Eventually.of_forall hlower) hupper

/-- Almost surely, the expected diagonal envelopes of rescaled LBM tend to zero. -/
theorem MatedCRTEnv.IsValid.ae_tendsto_integral_diagonalBad {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    {y z : ℂ} {r : ℝ} (hr : 0 < r) (hy : y ∈ ball z r) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂S.P, Tendsto (fun n : ℕ => ∫ b, pathUpperEnvelope (diagonalBad z r η n) n
      (rescaledLBMPath (S.clock ω) S.m₀ b) ∂(planarBrownianMotion y)) atTop (𝓝 0) := by
  have hBL : ∀ n : ℕ, IsBoundedLipschitzPathFunctional
      (pathUpperEnvelope (diagonalBad z r η n) n) := fun n =>
    isBoundedLipschitzPathFunctional_pathUpperEnvelope (abs_exitWindowBad_le_one z r _ _ η)
      (Nat.cast_nonneg n)
  have hmeas := ae_all_iff.2 fun n : ℕ => (hX γ hγ hγ2 _ S hS y _ (hBL n)).1
  have hreg := hS.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion
    (hS.m₀_pos hγ hγ2) hy (hexc y z r hy)
  filter_upwards [hmeas, hS.isLQGClock, hreg,
    hS.ae_normalizedLBMExitTime_any_ball_lt_top hγ hγ2 y z r] with ω hm hcω hregω hfinω
  have h0 : (0 : ℝ) = ∫ _b, (0 : ℝ) ∂(planarBrownianMotion y) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1)
    (fun n => Eventually.of_forall fun b => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_pathUpperEnvelope_le_one (abs_exitWindowBad_le_one z r _ _ η) (Nat.cast_nonneg n) _
  · filter_upwards [(hcω y).2, hregω, hfinω, ae_planarBrownianMotion_eval_zero y]
      with b hclock hregb hfinb hstart
    have hregb' : ∃ᶠ t in 𝓝[>] (pathExitTime (ball z r)
        (rescaledLBMPath (S.clock ω) S.m₀ b)).toNNReal,
        rescaledLBMPath (S.clock ω) S.m₀ b t ∉ closedBall z r := by
      rw [← closure_ball z hr.ne']
      exact hregb
    have hI : clockInverse (S.clock ω b) 0 = 0 := by
      have h := clockInverse_clockValue hclock.map_zero hclock.strictMono 0
      simpa only [hclock.map_zero, Real.toNNReal_zero] using h
    have h0b : rescaledLBMPath (S.clock ω) S.m₀ b 0 ∈ ball z r := by
      simpa only [rescaledLBMPath, mul_zero, liouvilleBrownianPath, hI, hstart] using hy
    exact tendsto_pathUpperEnvelope_diagonalBad
      ⟨rescaledLBMPath (S.clock ω) S.m₀ b, continuous_rescaledLBMPath hclock⟩ z h0b hfinb
      hregb' hη

end MatedCRT
