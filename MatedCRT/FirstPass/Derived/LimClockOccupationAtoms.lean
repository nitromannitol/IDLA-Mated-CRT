import MatedCRT.Proofs.Sec3.KilledOccupation.ClockOccupationMeasure
import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar

/-!
# The occupation measure of the limit clock has no atoms

For planar Brownian motion `B` started at `y`, the expected occupation measure of the limit clock up to the exit time
of `ball z r`,
`m₁(A) = E_y ∫_{[0, σ]} 1_A(B_u) dΦ(u)` (`limClockOccupationMeasure`), gives zero mass to every point `x`
(`limClockOccupationMeasure_planarBrownianMotion_singleton`). If `x ≠ y`, the path almost surely never visits `x`
(`ae_planarBrownianMotion_ne_of_ne`). If `x = y`, the path almost surely visits `y` only at time `0`
(`ae_planarBrownianMotion_ne_self_of_pos`), and the Stieltjes measure `dΦ` of the limit clock gives zero mass to
`{0}`, since `dΦ([0, 0]) = Φ(0) - Φ(0)`. No property of the circle averages `ψ` is needed. This is the point-mass part
of the identification of the occupation measure of Liouville Brownian motion with the Green-weighted chaos measure
(Garban-Rhodes-Vargas, Liouville Brownian motion, Theorem 2.7).
-/

open MeasureTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open _root_.HarmonicBalls

/-- The Stieltjes measure of the limit clock gives zero mass to the time `0`. -/
theorem limClockKernel_singleton_zero (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) : limClockKernel γ ε σ p {0} = 0 := by
  have h : ({0} : Set ℝ≥0) = Iic 0 := by
    ext u
    simp
  rw [h, limClockKernel_Iic, sub_self, ENNReal.ofReal_zero]

/-- **The expected occupation measure of the limit clock has no atoms** for planar Brownian motion: for every family
`ψ` of circle averages and every point `x`, `m₁({x}) = 0`. -/
theorem limClockOccupationMeasure_planarBrownianMotion_singleton (γ : ℝ) (ε : ℕ → ℝ) (z : ℂ) (r : ℝ) (y : ℂ)
    (ψ : UnitDiskCircleIndex → ℝ) (x : ℂ) :
    limClockOccupationMeasure γ ε z r (planarBrownianMotion y) ψ {x} = 0 := by
  rw [limClockOccupationMeasure_apply γ ε z r _ ψ (measurableSet_singleton x)]
  have hae : ∀ᵐ b ∂planarBrownianMotion y, ∀ u : ℝ≥0, 0 < u → b u ≠ x := by
    by_cases hxy : x = y
    · subst hxy
      exact ae_planarBrownianMotion_ne_self_of_pos x
    · exact (ae_planarBrownianMotion_ne_of_ne hxy).mono fun b hb u _ => hb u
  refine (lintegral_congr_ae (hae.mono fun b hb => ?_)).trans lintegral_zero
  have hle : ∀ u : ℝ≥0, ({x} : Set ℂ).indicator 1 (b u) ≤ ({0} : Set ℝ≥0).indicator (1 : ℝ≥0 → ℝ≥0∞) u := by
    intro u
    by_cases hu : u = 0
    · subst hu
      rw [indicator_of_mem (mem_singleton 0)]
      exact indicator_le_self' (fun _ _ => zero_le) _
    · have hbx : b u ∉ ({x} : Set ℂ) := fun h => hb u (pos_iff_ne_zero.2 hu) (mem_singleton_iff.1 h)
      rw [indicator_of_notMem hbx]
      exact zero_le
  refine le_antisymm ?_ zero_le
  calc ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), ({x} : Set ℂ).indicator 1 (b u) ∂limClockKernel γ ε (exitNN z r) (ψ, b)
      ≤ ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), ({0} : Set ℝ≥0).indicator 1 u
          ∂limClockKernel γ ε (exitNN z r) (ψ, b) := lintegral_mono hle
    _ ≤ ∫⁻ u, ({0} : Set ℝ≥0).indicator 1 u ∂limClockKernel γ ε (exitNN z r) (ψ, b) :=
        setLIntegral_le_lintegral _ _
    _ = limClockKernel γ ε (exitNN z r) (ψ, b) {0} := lintegral_indicator_one (measurableSet_singleton 0)
    _ = 0 := limClockKernel_singleton_zero γ ε (exitNN z r) (ψ, b)

end MatedCRT.KilledOccupation
