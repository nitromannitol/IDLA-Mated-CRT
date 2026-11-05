import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.PoleSingularity
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-! # Small cells for the barrier near the pole -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Cells meeting a fixed disc have uniformly small Euclidean diameter with
probability tending to one. -/
theorem small_cells_in_probability (𝒮 : SpaceFillingSLEModel)
    (h28 : CellSizeEstimateStmt 𝒮) {γ ρ d : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hd : 0 < d)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ProbTendsToOne S.P fun ε => {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ x ∈ cell ε (S.η ω) k, ∀ y ∈ cell ε (S.η ω) k, dist x y ≤ d} := by
  let e : ℝ := 1 / (2 + γ) ^ 2
  have he0 : 0 < e := by dsimp [e]; positivity
  have he1 : e < 1 := by
    dsimp [e]
    rw [div_lt_one (by positivity)]
    nlinarith
  have hA := HarmonicBalls.PolyHighProb.probTendsToOne (h28 γ hγ hγ2 e ρ he0 he1 hρ hρ1 Ω S hS)
  have hC := probTendsToOne_of_ae (G := {ω | IsAreaParametrized (S.μ ω) (S.η ω)}) hS.isAreaParametrized
  refine (hA.inter hC).mono_ev ?_
  filter_upwards [(tendsto_rpow_nhdsGT_zero he0).eventually (Iio_mem_nhds hd)] with ε hε ω hω
  obtain ⟨hA, hC⟩ := hω
  intro k hk x hx y hy
  have hdiam := (hA k hk).2
  have hexp : 2 / (2 + γ) ^ 2 - e = e := by dsimp [e]; ring
  rw [hexp] at hdiam
  have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) := (isCompact_Icc.image hC.1).isBounded
  exact (dist_le_diam_of_mem hbdd hx hy).trans (hdiam.trans hε.le)

end MatedCRT
