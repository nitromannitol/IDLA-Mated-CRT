import MatedCRT.FirstPass.Derived.AdaptedVersionOfLimitInProbability
import MatedCRT.FirstPass.Derived.RevuzOptionalClockInverse
import MatedCRT.FirstPass.Derived.LQGClockApproxAdapted

/-!
# An adapted version of the LQG clock, valid for every start

In the canonical space of continuous planar paths with its natural filtration `pathFiltration`, let
`F` be a raw process which is, for every starting point `z`, the LQG clock of planar Brownian motion
from `z` for the circle averages `hε` of a field (`HarmonicBalls.IsLQGClock`, convergence in
probability, uniformly on compacts, of the approximating clocks along `ε = 2^{-k}`).  No measurability of
`F` is assumed.  Then there is a process `G`, adapted to `pathFiltration`, with `G t = F · t` for all
`t` almost surely under planar Brownian motion from every `z`
(`exists_adapted_version_lqgClock`).  This replaces the false step "the raw clock is additive and
adapted": the raw clock is determined only up to null sets, start by start.
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The canonical filtration at time `t` is contained in the natural `σ`-field `F⁰_t`; together with
`pathFiltration_le_canonicalFiltration` the two coincide. -/
theorem canonicalFiltration_le_pathFiltration (t : ℝ≥0) :
    ContinuousPath.canonicalFiltration (alpha := ℂ) t ≤ pathFiltration t := by
  show ⨆ s : Set.Iic t, MeasurableSpace.comap (ContinuousPath.coordinateProcess (alpha := ℂ) s)
    inferInstance ≤ _
  refine iSup_le fun s => ?_
  exact le_iSup₂_of_le (s : ℝ≥0) s.2 le_rfl

theorem pathFiltration_mono : Monotone pathFiltration := fun _ _ hst =>
  iSup₂_le fun r hr => le_iSup₂_of_le r (hr.trans hst) le_rfl

/-- **An adapted version of the LQG clock valid at every start.**  If, for every `z`, the raw process `F` is
the LQG clock of planar Brownian motion from `z` for circle averages `hε` that are continuous at the dyadic
scales, there is a process `G`, adapted to the natural filtration of the path, such that for every `z`,
planar Brownian motion from `z` has `G t = F · t` for all `t` almost surely. -/
theorem exists_adapted_version_lqgClock {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ z : ℂ, IsLQGClock planarBrownianMotion γ hε z F) :
    ∃ G : ℝ≥0 → ContinuousPath ℂ → ℝ, (∀ t, Measurable[pathFiltration t] (G t)) ∧
      ∀ z : ℂ, ∀ᵐ b ∂planarBrownianMotion z, ∀ t, G t b = F b t := by
  refine AdaptedVersion.exists_adapted_version (X := ℂ) (Ω := ContinuousPath ℂ)
    planarBrownianMotion pathFiltration
    (fun t => (pathFiltration_le_canonicalFiltration t).trans
      ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le t))
    pathFiltration_mono (fun b => b 0) ?_ (fun z => ae_planarBrownianMotion_eval_zero z)
    (fun k t b => lqgClockApprox γ hε (dyadicScale k) b t) ?_ ?_ F (fun z T η hη => hF z T η hη)
  · exact (comap_measurable (fun b : ContinuousPath ℂ => b 0)).mono
      (le_iSup₂_of_le (0 : ℝ≥0) le_rfl le_rfl) le_rfl
  · intro k t
    exact (LQGClockApproxAdapted.measurable_lqgClockApprox_canonicalFiltration γ
      (hcont k).measurable t).mono (canonicalFiltration_le_pathFiltration t) le_rfl
  · intro k b
    exact LQGClockApproxMeasurable.continuous_lqgClockApprox_field (fun _ : Unit => hε) γ
      (dyadicScale k) () (hcont k) b

end MatedCRT
