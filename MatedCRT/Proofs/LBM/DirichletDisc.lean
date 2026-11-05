import MatedCRT.Proofs.LBM.DirichletDiscExit
import MatedCRT.Proofs.LBM.DirichletDiscHolder

/-!
# The Brownian solution of the Dirichlet problem on a disc

For boundary data `φ` Hölder continuous on a neighbourhood `cl B_{r+s}(z)` of the closed disc, the function
`u(x) = E_x[φ(𝓑_{τ_{B_r(z)}})]` on `B_r(z)`, `u = φ` elsewhere, is harmonic in `B_r(z)`, continuous on
`cl B_r(z)` and Hölder continuous on `cl B_r(z)` (Kakutani 1944; Mörters-Peres, *Brownian Motion*,
Theorems 3.12 and 3.44; Gilbarg-Trudinger, Lemma 4.2). This is the continuum input used in the proof of
Lemma 3.5 (paper/idla_mated_crt-corrected.tex, "f̄₁ solves Δf̄₁ = 0, f̄₁ = φ on ∂B_r(z)").

The exit distribution is the Poisson integral (`integral_pathExitPosition_eq_discPoissonIntegral`), so `u` is
the Poisson extension of `φ`; its regularity is `DirichletDiscBarrier.lean` and `DirichletDiscHolder.lean`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- The Brownian exit candidate is the Poisson extension of the boundary data. -/
theorem brownianExitCandidate_eq_discPoissonExtension {z : ℂ} {r : ℝ} (hr : 0 < r) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (closedBall z r)) (x : ℂ) :
    (open Classical in if x ∈ ball z r then
      ∫ b : ContinuousPath ℂ, φ (pathExitPosition (ball z r) b) ∂planarBrownianMotion x
      else φ x) = discPoissonExtension φ z r x := by
  by_cases hx : x ∈ ball z r
  · rw [ite_eq_left hx, discPoissonExtension_of_mem hx,
      integral_pathExitPosition_eq_discPoissonIntegral hr hφ hx]
  · rw [ite_eq_right hx, discPoissonExtension_of_notMem hx]

/-- Lowering a Hölder exponent on the sphere: `χ`-Hölder data are `α`-Hölder for `α ≤ χ`. -/
theorem abs_sub_le_rpow_of_holderOnWith {φ : ℂ → ℝ} {z : ℂ} {r s : ℝ} (hs : 0 ≤ s)
    {C χ : ℝ≥0} (hH : HolderOnWith C χ φ (closedBall z (r + s))) {α : ℝ} (hα0 : 0 < α)
    (hαχ : α ≤ χ) :
    ∀ ζ ∈ sphere z r, ∀ ζ' ∈ sphere z r,
      |φ ζ - φ ζ'| ≤ (C * (2 * r) ^ ((χ : ℝ) - α)) * ‖ζ - ζ'‖ ^ α := by
  intro ζ hζ ζ' hζ'
  have hsub : sphere z r ⊆ closedBall z (r + s) :=
    sphere_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have h := hH.dist_le (hsub hζ) (hsub hζ')
  rw [Real.dist_eq, dist_eq_norm] at h
  have hd : ‖ζ - ζ'‖ ≤ 2 * r := by
    have h1 : ‖ζ - z‖ = r := by simpa [dist_eq_norm] using hζ
    have h2 : ‖ζ' - z‖ = r := by simpa [dist_eq_norm] using hζ'
    calc ‖ζ - ζ'‖ = ‖(ζ - z) - (ζ' - z)‖ := by ring_nf
      _ ≤ ‖ζ - z‖ + ‖ζ' - z‖ := norm_sub_le _ _
      _ = 2 * r := by rw [h1, h2]; ring
  have hsplit : ‖ζ - ζ'‖ ^ (χ : ℝ) = ‖ζ - ζ'‖ ^ α * ‖ζ - ζ'‖ ^ ((χ : ℝ) - α) := by
    rw [← Real.rpow_add' (norm_nonneg _) (by linarith), add_sub_cancel]
  have hle : ‖ζ - ζ'‖ ^ ((χ : ℝ) - α) ≤ (2 * r) ^ ((χ : ℝ) - α) :=
    Real.rpow_le_rpow (norm_nonneg _) hd (by linarith)
  calc |φ ζ - φ ζ'| ≤ C * ‖ζ - ζ'‖ ^ (χ : ℝ) := h
    _ = C * (‖ζ - ζ'‖ ^ α * ‖ζ - ζ'‖ ^ ((χ : ℝ) - α)) := by rw [hsplit]
    _ ≤ C * (‖ζ - ζ'‖ ^ α * (2 * r) ^ ((χ : ℝ) - α)) := by
      gcongr
    _ = (C * (2 * r) ^ ((χ : ℝ) - α)) * ‖ζ - ζ'‖ ^ α := by ring

/-- **Brownian solution of the Dirichlet problem on a disc** (Kakutani 1944; Mörters-Peres, Theorems 3.12 and
3.44), with Hölder regularity up to the boundary for Hölder data (Gilbarg-Trudinger, Lemma 4.2). -/
theorem brownianDirichletDisc {z : ℂ} {r : ℝ} (hr : 0 < r) {φ : ℂ → ℝ}
    (hφ : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) :
    let u : ℂ → ℝ := fun x => open Classical in if x ∈ ball z r then
      ∫ b : ContinuousPath ℂ, φ (pathExitPosition (ball z r) b) ∂planarBrownianMotion x else φ x
    HarmonicOnNhd u (ball z r) ∧ ContinuousOn u (closedBall z r) ∧
      IsHolderContinuousOn u (closedBall z r) := by
  intro u
  obtain ⟨s, hs, C, χ, hχ0, hχ1, hH⟩ := hφ
  have hφc' : ContinuousOn φ (closedBall z (r + s)) := hH.continuousOn hχ0
  have hφc : ContinuousOn φ (closedBall z r) :=
    hφc'.mono (closedBall_subset_closedBall (by linarith))
  have hφs : ContinuousOn φ (sphere z r) := hφc.mono sphere_subset_closedBall
  have hu : u = discPoissonExtension φ z r :=
    funext fun x => brownianExitCandidate_eq_discPoissonExtension hr hφc x
  rw [hu]
  set α : ℝ := min (χ : ℝ) (1 / 2) with hαdef
  have hα0 : 0 < α := lt_min (by exact_mod_cast hχ0) (by norm_num)
  have hα1 : α < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hαχ : α ≤ χ := min_le_left _ _
  have hC' : 0 ≤ (C : ℝ) * (2 * r) ^ ((χ : ℝ) - α) := by positivity
  refine ⟨harmonicOnNhd_discPoissonExtension (hφs.circleIntegrable hr.le),
    continuousOn_discPoissonExtension hr hφs, ?_⟩
  obtain ⟨M, hM⟩ := exists_holderOnWith_discPoissonExtension hr hα0 hα1 hC' hφs
    (abs_sub_le_rpow_of_holderOnWith hs.le hH hα0 hαχ)
  refine ⟨M, Real.toNNReal α, Real.toNNReal_pos.2 hα0, ?_, hM⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hα0.le, NNReal.coe_one]
  exact hα1.le

end MatedCRT
