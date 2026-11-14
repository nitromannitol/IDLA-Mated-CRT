import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import LatticeProb.Prob.UniformReparamComparison

/-!
# Uniform comparison of the laws of stopped planar Brownian motion from nearby start points

For start points `y` in the closed disc `closedBall 0 ρ` and `ρ < R`, the law of planar Brownian motion started at
`y` and stopped at its exit time from `B_R(0)` depends continuously on `y`, uniformly over the disc, for the
one-sided Lévy–Prokhorov comparison of curves modulo time parametrization: for all `κ, θ > 0` there is `δ > 0` such
that for `y ∈ closedBall 0 ρ` and `|z - y| < δ`, for every `κ₁` and every set `A` of paths,
`P_z(stop_R b ∈ A^κ₁) ≤ P_y(stop_R b ∈ A^(κ₁ + κ)) + θ` and symmetrically, where `A^κ` is the set of paths at
`cmpEDist`-distance less than `κ` from `A`.

This is the general comparison theorem `LatticeProb.ReparamEDist.exists_forall_measure_thickening_le` applied to the
family `y ↦ stopAtExit (ball 0 R) (b + y)` of translates of one planar Brownian path `b` from `0`: its uniform
distances are `MatedCRT.StopAtExitCmp.stoppedSupDist`, measurable and almost surely continuous in the start point
(`ae_tendsto_stoppedSupDist_ball`). The distance `MatedCRT.cmpEDist` is the library's `reparamEDist`
(`cmpEDist_eq_reparamEDist`, by definition). It is the start-point step of the uniform-start invariance principle
`MatedCRT.GMS21UniformStartInput`.

## Main statements

* `MatedCRT.StopAtExitCmp.cmpEDist_eq_reparamEDist`
* `MatedCRT.StopAtExitCmp.planarBrownianMotion_stopAtExit_thickening`: the event as a translate.
* `MatedCRT.StopAtExitCmp.exists_forall_planarBrownianMotion_stopAtExit_le`: the uniform comparison.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The distance of curves modulo time parametrization of the paper is the library's `reparamEDist`. -/
theorem cmpEDist_eq_reparamEDist (f g : ℝ≥0 → ℂ) :
    cmpEDist f g = LatticeProb.ReparamEDist.reparamEDist f g :=
  rfl

/-- The event that planar Brownian motion from `z`, stopped at its exit time from `U`, lies within curve distance
`κ₁` of `A`, written as the event for the translate by `z` of planar Brownian motion from `0`. -/
theorem planarBrownianMotion_stopAtExit_thickening (U : Set ℂ) (z : ℂ) (κ₁ : ℝ≥0∞) (A : Set (ℝ≥0 → ℂ)) :
    planarBrownianMotion z {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < κ₁} =
      planarBrownianMotion 0
        {b | stopAtExit U ⇑(translatePath z b) ∈ LatticeProb.ReparamEDist.thickening κ₁ A} := by
  rw [planarBrownianMotion_apply_eq_translatePath z]
  rfl

/-- **Uniform comparison of stopped laws in the start point.** Let `0 < ρ < R`. For all `κ, θ > 0` there is
`δ > 0` such that for every start point `y ∈ closedBall 0 ρ`, every `z` with `dist z y < δ`, every `κ₁` and every
set `A` of paths, the laws of planar Brownian motion from `z` and from `y`, each stopped at its exit time from
`B_R(0)`, satisfy the one-sided Lévy–Prokhorov bounds
`P_z(cmpEDist(stop_R b, A) < κ₁) ≤ P_y(cmpEDist(stop_R b, A) < κ₁ + κ) + θ` and the same with `y` and `z`
exchanged. -/
theorem exists_forall_planarBrownianMotion_stopAtExit_le {ρ R : ℝ} (hρR : ρ < R) {κ θ : ℝ≥0∞}
    (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ y ∈ closedBall (0 : ℂ) ρ, ∀ z : ℂ, dist z y < δ → ∀ (κ₁ : ℝ≥0∞) (A : Set (ℝ≥0 → ℂ)),
      planarBrownianMotion z {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁} ≤
          planarBrownianMotion y
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁ + κ} + θ ∧
        planarBrownianMotion y {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁} ≤
          planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁ + κ} + θ := by
  set Y : ℂ → ContinuousPath ℂ → ℝ≥0 → ℂ := fun y b => stopAtExit (ball (0 : ℂ) R) ⇑(translatePath y b)

  have hF : ∀ y z, AEMeasurable (LatticeProb.ReparamEDist.familySupEDist Y y z) (planarBrownianMotion 0) :=
    fun y z => (measurable_stoppedSupDist isOpen_ball y z).aemeasurable
  have hae : ∀ c ∈ closedBall (0 : ℂ) ρ, ∀ u : ℕ → ℂ, Tendsto u atTop (𝓝 c) →
      ∀ᵐ ω ∂planarBrownianMotion 0,
        Tendsto (fun n => LatticeProb.ReparamEDist.familySupEDist Y c (u n) ω) atTop (𝓝 0) :=
    fun c hc u hu => ae_tendsto_stoppedSupDist_ball
      (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hc) hρR)) hu
  obtain ⟨δ, hδ, h⟩ := LatticeProb.ReparamEDist.exists_forall_measure_thickening_le
    (isCompact_closedBall (0 : ℂ) ρ) Y hF hae hκ hθ
  refine ⟨δ, hδ, fun y hy z hz κ₁ A => ?_⟩
  simp only [planarBrownianMotion_stopAtExit_thickening]
  exact h y hy z hz κ₁ A

end MatedCRT.StopAtExitCmp
