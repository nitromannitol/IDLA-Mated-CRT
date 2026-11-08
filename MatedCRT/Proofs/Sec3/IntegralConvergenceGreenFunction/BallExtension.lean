import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestHolderApprox

/-!
# Lemma 3.4: extension of closed-ball test functions to `ℂ`

The environment-dependent fixed-time step (E-c2-9) approximates a Hölder test function on the ball `B(z, r)` by
a member of a countable family of Hölder functions on the closed ball (`exists_countable_holderWith_approx_ball`).
The deterministic walk-to-LBM convergence needs globally continuous, bounded test functions on `ℂ`. This file
transports the family to `ℂ` by the radial retraction `closedBallRetraction z r : ℂ → cl B(z, r)`, the identity on the
closed ball and the radial projection outside it. The extension `extendClosedBall z r hr G = G ∘ closedBallRetraction` is
continuous and bounded on `ℂ`, and is Hölder on the open ball with the constants of `G`.

Terminology: radial retraction onto the closed disk (Armitage–Gardiner, potential theory of the disk).
-/

namespace MatedCRT

open Metric Set Topology
open scoped NNReal

/-- The radial retraction of `ℂ` onto the closed ball `cl B(z, r)`: the identity on the closed ball, and the radial
projection outside it. The denominator is `max ‖x - z‖ r`, so the formula is continuous across the circle. -/
noncomputable def closedBallRetraction (z : ℂ) (r : ℝ) (x : ℂ) : ℂ :=
  if ‖x - z‖ ≤ r then x else z + ((r / max ‖x - z‖ r : ℝ) : ℂ) * (x - z)

lemma closedBallRetraction_mem {z : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) :
    closedBallRetraction z r x ∈ closedBall z r := by
  rw [mem_closedBall, dist_eq_norm]
  unfold closedBallRetraction
  split_ifs with h
  · exact h
  · have hM : 0 < max ‖x - z‖ r := lt_max_of_lt_right hr
    have hc : (0 : ℝ) ≤ r / max ‖x - z‖ r := div_nonneg hr.le hM.le
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    calc r / max ‖x - z‖ r * ‖x - z‖ ≤ r / max ‖x - z‖ r * max ‖x - z‖ r :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hc
      _ = r := div_mul_cancel₀ r hM.ne'

lemma closedBallRetraction_of_mem {z : ℂ} {r : ℝ} {x : ℂ} (hx : x ∈ closedBall z r) :
    closedBallRetraction z r x = x := by
  have h : ‖x - z‖ ≤ r := by
    rw [← dist_eq_norm]
    exact mem_closedBall.1 hx
  simp only [closedBallRetraction, h, ↓reduceIte]

lemma continuous_closedBallRetraction {z : ℂ} {r : ℝ} (hr : 0 < r) : Continuous (closedBallRetraction z r) := by
  have hmax : Continuous fun x : ℂ => max ‖x - z‖ r :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).max continuous_const
  have hq : Continuous fun x : ℂ => r / max ‖x - z‖ r :=
    continuous_const.div hmax fun x => (lt_max_of_lt_right hr).ne'
  have hg : Continuous fun x : ℂ => z + ((r / max ‖x - z‖ r : ℝ) : ℂ) * (x - z) :=
    continuous_const.add ((Complex.continuous_ofReal.comp hq).mul (continuous_id.sub continuous_const))
  have hf : Continuous fun x : ℂ => ‖x - z‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have key : Continuous fun x : ℂ => if ‖x - z‖ ≤ r then x else z + ((r / max ‖x - z‖ r : ℝ) : ℂ) * (x - z) :=
    Continuous.if_le continuous_id hg hf continuous_const fun x hx => by
      simp only [hx, max_self, div_self hr.ne', Complex.ofReal_one, one_mul, add_sub_cancel]
  exact key

/-- The extension to `ℂ` of a continuous function on the closed ball: `G ∘ closedBallRetraction`. -/
noncomputable def extendClosedBall (z : ℂ) (r : ℝ) (hr : 0 < r) (G : C(closedBall z r, ℝ)) (x : ℂ) : ℝ :=
  G ⟨closedBallRetraction z r x, closedBallRetraction_mem hr x⟩

lemma continuous_extendClosedBall {z : ℂ} {r : ℝ} (hr : 0 < r) (G : C(closedBall z r, ℝ)) :
    Continuous (extendClosedBall z r hr G) :=
  G.continuous.comp ((continuous_closedBallRetraction hr).subtype_mk (closedBallRetraction_mem hr))

lemma extendClosedBall_of_mem {z : ℂ} {r : ℝ} (hr : 0 < r) (G : C(closedBall z r, ℝ)) {x : ℂ}
    (hx : x ∈ closedBall z r) : extendClosedBall z r hr G x = G ⟨x, hx⟩ := by
  simp only [extendClosedBall]
  congr 1
  exact Subtype.ext (closedBallRetraction_of_mem hx)

lemma exists_bound_extendClosedBall {z : ℂ} {r : ℝ} (hr : 0 < r) (G : C(closedBall z r, ℝ)) :
    ∃ M : ℝ, ∀ x, |extendClosedBall z r hr G x| ≤ M := by
  have : CompactSpace (closedBall z r) := isCompact_iff_compactSpace.1 (isCompact_closedBall z r)
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set (closedBall z r))).exists_bound_of_continuousOn
    G.continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  have := hM ⟨closedBallRetraction z r x, closedBallRetraction_mem hr x⟩ (mem_univ _)
  simpa [extendClosedBall, Real.norm_eq_abs] using this

lemma holderOnWith_extendClosedBall {z : ℂ} {r : ℝ} (hr : 0 < r) {C χ : ℝ≥0} (G : C(closedBall z r, ℝ))
    (hG : HolderWith C χ G) : HolderOnWith C χ (extendClosedBall z r hr G) (ball z r) := by
  intro x hx y hy
  rw [extendClosedBall_of_mem hr G (ball_subset_closedBall hx), extendClosedBall_of_mem hr G (ball_subset_closedBall hy)]
  have h := hG ⟨x, ball_subset_closedBall hx⟩ ⟨y, ball_subset_closedBall hy⟩
  rw [Subtype.edist_eq] at h
  exact h

end MatedCRT
