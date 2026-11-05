import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ConeMeasure
import HarmonicBalls.Proofs.Sec5.DenseVolumeGrowth

/-! # Measurable support for cone volume growth -/

namespace MatedCRT

open MeasureTheory Filter Metric Set TopologicalSpace HarmonicBalls

/-- The cone LQG measure belongs almost surely to a measurable set of
locally finite measures satisfying volume growth on a fixed smaller disk. -/
theorem IsConeField.exists_measurable_volumeGrowth_support
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ (∀ᵐ ω ∂P, μ ω ∈ E) ∧
      ∀ ν ∈ E, IsLocallyFiniteMeasure ν ∧ ∃ βm βp, VolumeGrowth ν R βm βp := by
  let A : ℝ := (2 - γ) ^ 2 / 2
  let B : ℝ := (2 + γ) ^ 2 / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound := h27 γ hγ hγ2 (A / 2) (B + 1) (by positivity)
    (by dsimp [A] at *; linarith) (by dsimp [B]; linarith)
    Ω P hC hcirc μ hcone
  have hpoly : PolyHighProb P (ballMassBoundEvent μ R (A / 2) (B + 1)) := by
    refine hbound.mono_of_small (sub_pos.2 hR1) ?_
    intro δ hδ hδR ω hω z hz
    exact hω z (ball_subset_ball (by linarith) hz)
  have hgrowth : ∀ᵐ ω ∂P, VolumeGrowth (μ ω) R (B + 2) (A / 4) :=
    ae_volumeGrowth_of_poly_ballMass (by positivity) (by linarith)
      (by positivity) (by linarith) hpoly
  let : Nonempty (ball (0 : ℂ) R) := ⟨⟨0, by simpa using hR⟩⟩
  let e : ℕ → ball (0 : ℂ) R := denseSeq _
  let E : Set (Measure ℂ) := {ν | IsLocallyFiniteMeasure ν} ∩
    {ν | ∃ N : ℕ, ∀ n ≥ N, ∀ i : ℕ,
      ENNReal.ofReal (dyadicScale n ^ (B + 2)) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ (A / 4))}
  refine ⟨E, measurableSet_isLocallyFiniteMeasure_complex.inter
    (measurableSet_eventually_dyadic_ball_bounds (fun i => (e i : ℂ)) (B + 2) (A / 4)), ?_, ?_⟩
  · filter_upwards [hcone.2.2, hgrowth] with ω hμ hvol
    obtain ⟨_, _, r₀, hr₀, hballs⟩ := hvol
    have hsmall : ∀ᶠ n in atTop, dyadicScale n < r₀ :=
      (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hr₀)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    exact ⟨hμ.isLocallyFiniteMeasure, N, fun n hn i =>
      hballs (dyadicScale n) (dyadicScale_pos n) (hN n hn) (e i) (e i).property⟩
  · intro ν hν
    obtain ⟨N, hN⟩ := hν.2
    exact ⟨hν.1, B + 4, A / 16, by
      convert volumeGrowth_of_dense_dyadic_ball_bounds e (denseRange_denseSeq _)
        (show 0 < B + 2 by positivity) (show 0 < A / 4 by positivity) hN using 1 <;> ring⟩

end MatedCRT
