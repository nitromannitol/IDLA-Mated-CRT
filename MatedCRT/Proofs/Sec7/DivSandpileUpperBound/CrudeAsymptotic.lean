import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! The cell diameter absorbs the path length in the final crude bound. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- If the cell-diameter exponent is greater than the stopping exponent, the
crude path length times the cell diameter tends to zero. -/
theorem tendsto_crude_path_scale {α ω : ℝ} (h : ω < α) :
    Tendsto (fun ε : ℝ => ε ^ (-ω) * ε ^ α * (Real.log ε⁻¹) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hhalf : 0 < (α - ω) / 2 := by linarith
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hhalf
  have hsquare := hlog.mul hlog
  simp only [zero_mul] at hsquare
  apply hsquare.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hpow : ε ^ (-ω) * ε ^ α = (ε ^ ((α - ω) / 2)) * ε ^ ((α - ω) / 2) := by
    rw [← Real.rpow_add hε', ← Real.rpow_add hε']
    congr 1
    ring
  rw [hpow, Real.log_inv]
  ring

/-- The full radius in `crudeUpperBound_event_confinement` tends to zero when
the stopping odometer is bounded by `ε ^ (-ω)`. -/
theorem tendsto_crude_confinement_radius {α ω : ℝ} (hα : 0 < α) (h : ω < α) :
    Tendsto (fun ε : ℝ => ε ^ α + (ε ^ α + ε ^ (-ω) /
      ((Real.log ε⁻¹)⁻¹ ^ 2) * (2 * ε ^ α))) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have ht := hi.rpow_const (Or.inr hα.le)
    simpa [Real.zero_rpow hα.ne'] using ht
  have hq := (tendsto_crude_path_scale h).const_mul 2
  simp only [mul_zero] at hq
  have ht := hp.add (hp.add hq)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [] with ε
  simp only [div_eq_mul_inv, inv_pow, inv_inv]
  ring

end MatedCRT.Sec7
