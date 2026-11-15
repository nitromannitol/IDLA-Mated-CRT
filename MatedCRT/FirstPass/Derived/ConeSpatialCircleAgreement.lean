import MatedCRT.Proofs.Measurability.FieldCircle

/-! # Spatial agreement of cone circle averages -/

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped Distributions
open HarmonicBalls

namespace MatedCRT

/-- At a fixed circle avoiding the origin, a matching distribution and cone
have the same circle average almost surely. -/
theorem ae_cone_circleAvg_eq_fixed {Ω : Type*} [MeasurableSpace Ω]
{P : Measure Ω} {γ : ℝ}
{hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
(hQ : IsQuantumCone γ P hC hcirc) {H : Ω → LQGMetric.DistC}
(hH : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
{r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) :
  ∀ᵐ ω ∂P, LQGMetric.circleAvg (H ω) r z = hcirc ω r z := by
  filter_upwards [hH, CirclePairing.ae_tendsto_circBump_of_isQuantumCone hQ hr hz] with ω hω ht
  have ht' : Tendsto (fun n => Real.circleAverage
      (fun x => H ω (LQGMetric.bumpTest n x)) z r) atTop (𝓝 (hcirc ω r z)) := by
    apply ht.congr
    intro n
    rw [LQGMetric.CircleAvg.circleAverage_pairing]
    exact hω _
  exact ht'.limUnder_eq


/-- The spatial grid interpolation recovers all positive-radius cone circle
averages on one event. -/
theorem ae_cone_gridVersion_eq {Ω : Type*} [MeasurableSpace Ω]
{P : Measure Ω} {γ : ℝ}
{hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
(hQ : IsQuantumCone γ P hC hcirc) : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
  FieldCircle.gridVersion (fun w ω => hcirc ω r w) ω z = hcirc ω r z := by
  filter_upwards [hQ.ae_continuousOn_circle] with ω hc r hr z
  have hf : Continuous fun w => hcirc ω r w := by
    rw [← continuousOn_univ]
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun w _ => ⟨mem_Ioi.2 hr, mem_univ _⟩
  exact FieldCircle.gridVersion_eq hf (fun _ _ _ => rfl) z



end MatedCRT
