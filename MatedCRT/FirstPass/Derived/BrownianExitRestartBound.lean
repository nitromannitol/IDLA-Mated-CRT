import MatedCRT.FirstPass.LPBridge.ExitRestartLimit

/-!
# Events of the exit position and the post-exit increments of planar Brownian motion

For planar Brownian motion `b` started at `x` and the exit time `τ` of an open set `U`, the exit position
`b τ` and the post-exit increments `t ↦ b (τ + t) - b τ` are independent, and the increments have the
centred planar Brownian law `muPlanar` (strong Markov property at the exit time; Mörters–Peres,
*Brownian Motion*, Theorem 2.16, formalised as `MatedCRT.ExitRestart.planar_exit_indepFun`).

This file turns that independence into a bound for events that depend on both: if the exit position lies
in a measurable set `S`, and for every `y ∈ S` the section at `y` of a measurable set `B` has
`muPlanar`-measure at most `p`, then the probability that the pair (exit position, post-exit increments)
lies in `B` is at most `p`.

* `MatedCRT.ExitRestart.planarBrownianMotion_exit_pair_le`: the bound.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.ExitRestart

/-- **Events of the exit position and the post-exit increments.** Let `U` be open and let planar Brownian
motion from `x` leave `U` in finite time almost surely, at a position in the measurable set `S`. If `B` is a
measurable set of pairs (position, path) whose section at every `y ∈ S` has `muPlanar`-measure at most `p`,
then the probability that (exit position, post-exit increments) lies in `B` is at most `p`. -/
theorem planarBrownianMotion_exit_pair_le {U : Set ℂ} (hU : IsOpen U) (x : ℂ)
    (hfin : ∀ᵐ η ∂(planarBrownianMotion x), ContinuousPath.exitTime U η ≠ ⊤)
    {B : Set (ℂ × (ℝ≥0 → ℂ))} (hB : MeasurableSet B) {S : Set ℂ} (hS : MeasurableSet S)
    (hSae : ∀ᵐ η ∂(planarBrownianMotion x), η (exitNN U η) ∈ S) {p : ℝ≥0∞}
    (hp : ∀ y ∈ S, muPlanar (Prod.mk y ⁻¹' B) ≤ p) :
    planarBrownianMotion x {b | (b (exitNN U b), postIncr (exitNN U) b) ∈ B} ≤ p := by
  have hτm : Measurable (exitNN U) := (ContinuousPath.measurable_exitTime U hU).ennreal_toNNReal
  have hX : Measurable (fun b : ContinuousPath ℂ => b (exitNN U b)) := measurable_eval_at hτm
  have hY : Measurable (postIncr (exitNN U)) := measurable_postIncr hτm
  have hind := planar_exit_indepFun hU x hfin
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have hYlaw : (planarBrownianMotion x).map (postIncr (exitNN U)) = muPlanar := by
    refine Measure.ext fun Γ hΓ => ?_
    rw [Measure.map_apply hY hΓ]
    exact planar_postIncr_law hU x hfin hΓ
  have : IsProbabilityMeasure ((planarBrownianMotion x).map fun b : ContinuousPath ℂ => b (exitNN U b)) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have hpair : Measurable fun b : ContinuousPath ℂ => (b (exitNN U b), postIncr (exitNN U) b) :=
    hX.prodMk hY
  have h1 : planarBrownianMotion x {b | (b (exitNN U b), postIncr (exitNN U) b) ∈ B} =
      ∫⁻ y, muPlanar (Prod.mk y ⁻¹' B)
        ∂((planarBrownianMotion x).map fun b : ContinuousPath ℂ => b (exitNN U b)) := by
    have e1 : planarBrownianMotion x {b | (b (exitNN U b), postIncr (exitNN U) b) ∈ B} =
        ((planarBrownianMotion x).map fun b => (b (exitNN U b), postIncr (exitNN U) b)) B :=
      (Measure.map_apply hpair hB).symm
    rw [e1]
    erw [hmap]
    rw [Measure.prod_apply hB, hYlaw]
  rw [h1]
  have hae : ∀ᵐ y ∂((planarBrownianMotion x).map fun b : ContinuousPath ℂ => b (exitNN U b)),
      muPlanar (Prod.mk y ⁻¹' B) ≤ p := by
    have hS' : ∀ᵐ y ∂((planarBrownianMotion x).map fun b : ContinuousPath ℂ => b (exitNN U b)), y ∈ S :=
      (ae_map_iff hX.aemeasurable hS).2 hSae
    filter_upwards [hS'] with y hy using hp y hy
  calc ∫⁻ y, muPlanar (Prod.mk y ⁻¹' B)
        ∂((planarBrownianMotion x).map fun b : ContinuousPath ℂ => b (exitNN U b))
      ≤ ∫⁻ _y, p ∂((planarBrownianMotion x).map fun b : ContinuousPath ℂ => b (exitNN U b)) :=
        lintegral_mono_ae hae
    _ = p := by simp

end MatedCRT.ExitRestart
