import MatedCRT.FirstPass.Derived.LocalMeshEdgeLength
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Convergence in measure of local cell diameters -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- The local maximal cell diameter converges to zero in measure along any mesh sequence tending to zero. -/
theorem maxCellDiam_tendstoInMeasure_zero
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) (R : ℝ) :
    TendstoInMeasure S.P (fun n ω =>
      FirstPass.Derived.maxCellDiam (ε n) (⇑(η' ω)) R) atTop (fun _ => 0) := by
  let D : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    FirstPass.Derived.maxCellDiam (ε n) (⇑(η' ω)) R
  apply tendstoInMeasure_of_ne_top
  intro t ht httop
  let d : ℝ := t.toReal / 2
  have hd : 0 < d := half_pos (ENNReal.toReal_pos ht.ne' httop)
  have hdt : ENNReal.ofReal d < t := by
    calc
      ENNReal.ofReal d < ENNReal.ofReal t.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos ht.ne' httop)).2
          (by dsimp [d]; linarith [ENNReal.toReal_pos ht.ne' httop])
      _ = t := ENNReal.ofReal_toReal httop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (FirstPass.Derived.hdiam_of_isValid hS hae hε0 R d hd) (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  change t ≤ edist (D n ω) 0 at hω
  rw [ENNReal.edist_zero_right] at hω
  exact lt_of_lt_of_le hdt hω

end MatedCRT
end
