import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FiniteCellEvents
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMeasurable

/-! Measurable versions of normalized exit-time oscillation events. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric Filter

/-- The normalized exit-time oscillation event on a compact set has an
environment-measurable version. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_exit_oscillation
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D)
    (K : Set ℂ) (hK : IsCompact K) (δ t : ℝ) :
    ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧
        t < |rescale (S.mε ε) ε (S.η ω)
              (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) x -
            rescale (S.mε ε) ε (S.η ω)
              (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) y|) := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  obtain ⟨v, hvm, hv⟩ := hS.exists_envSigma_measurable_normExitTime ε D hD
  let u : Ω → ℤ → ℝ := fun ω a => (S.mε ε)⁻¹ * v ω a
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a :=
    fun a => measurable_const.mul (hvm a)
  have hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty := by
    intro k
    exact ⟨ε * (k - 1), le_rfl, mul_le_mul_of_nonneg_left (by linarith) hε.le⟩
  let A : Set Ω := {ω | ∃ N a b : ℤ,
      (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      t < |u ω a - u ω b| ∧
      ∃ x ∈ K, ∃ y ∈ K, x ∈ cell ε (η ω) a ∧ y ∈ cell ε (η ω) b ∧
        dist x y < δ ∧ (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
        (∀ j ∈ Finset.Ico N b, y ∉ cell ε (η ω) j)}
  refine ⟨A, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    exact measurableSet_bounded_index_oscillation η hηm u hum ε δ t K hK hI
  · filter_upwards [hη, hv, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
      with ω hηω hvω harea hp
    have hfin := Tightness.cellVertices_finite harea.1 hp hε hK.isBounded
    obtain ⟨N, hN⟩ := hfin.bddBelow
    have hbound : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j := by
      refine ⟨N, ?_⟩
      intro j hj x hx hcell
      have hjN : N ≤ j := hN ⟨x, by simpa [hηω] using hcell, hx⟩
      exact (not_lt_of_ge hjN) hj
    have hsel : ∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x) := by
      intro x hx
      rw [hηω]
      exact Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
    have heq := bounded_index_oscillation_iff (η ω) (u ω) ε δ t K hbound hsel
    change (∃ N a b : ℤ, _) ↔ _
    rw [← heq]
    simp only [hηω, u, hvω, rescale]

end MatedCRT
