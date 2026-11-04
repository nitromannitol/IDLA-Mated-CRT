import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable
import MatedCRT.Proofs.Sec5.LLowerBound.Mass

/-!
# Integrability of rescaled vertex functions

On a bounded region a proper space-filling curve has only finitely many cells.
The measurable representative of the cell index and area parametrization then
give integrability of every rescaled vertex function on that region.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Every rescaled vertex function is almost surely integrable on a bounded
ball, even when its vertex values depend arbitrarily on the environment. -/
theorem MatedCRTEnv.IsValid.ae_integrableOn_rescale_ball
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ε : ℝ} (hS : S.IsValid 𝒮 γ) (hε : 0 < ε)
    (ρ : ℝ) (u : Ω → ℤ → ℝ) :
    ∀ᵐ ω ∂S.P, IntegrableOn (rescale (S.mε ε) ε (S.η ω) (u ω))
      (ball 0 ρ) (S.μ ω) := by
  classical
  obtain ⟨V, hV, hVe⟩ := hS.exists_measurable_vertexOf hε
  filter_upwards [hVe, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hVω harea hp
  have hv : Measurable (fun x => vertexOf ε (S.η ω) x) := by
    have hv' : Measurable (fun x : ℂ => V (ω, x)) :=
      hV.comp (measurable_const.prodMk measurable_id)
    simpa only [hVω] using hv'
  have hf : Measurable (rescale (S.mε ε) ε (S.η ω) (u ω)) := by
    unfold rescale
    exact measurable_const.mul ((measurable_of_countable (u ω)).comp hv)
  have hfin := Tightness.cellVertices_finite harea.1 hp hε
    (show Bornology.IsBounded (ball (0 : ℂ) ρ) from isBounded_ball)
  obtain ⟨C, hC⟩ := (hfin.image (fun a => ‖(S.mε ε)⁻¹ * u ω a‖)).bddAbove
  apply IntegrableOn.of_bound (ball_mass_lt_top_of_proper harea hp 0 ρ) hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  apply hC
  refine ⟨vertexOf ε (S.η ω) x, ?_, rfl⟩
  exact ⟨x, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x, hx⟩

end MatedCRT
