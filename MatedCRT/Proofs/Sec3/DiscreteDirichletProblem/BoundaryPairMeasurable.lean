import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryCellEvents
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableOscillation

/-! Environment-measurable oscillation events for rescaled discrete functions. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric Filter
open scoped ENNReal

/-- A vertex function with an environment-measurable version has an
    environment-measurable oscillation event on every compact set. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_rescale_boundary_pair
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (F : Ω → ℤ → ℝ)
    (v : Ω → ℤ → ℝ) (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a)
    (hv : ∀ᵐ ω ∂S.P, v ω = F ω)
    (K B : Set ℂ) (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K) (δ t : ℝ) :
    ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ B, dist x y < δ ∧
        t < |rescale (S.mε ε) ε (S.η ω) (F ω) x -
          rescale (S.mε ε) ε (S.η ω) (F ω) y|) := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  let u : Ω → ℤ → ℝ := fun ω a => (S.mε ε)⁻¹ * v ω a
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a :=
    fun a => measurable_const.mul (hvm a)
  have hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty := by
    intro k
    exact ⟨ε * (k - 1), le_rfl, mul_le_mul_of_nonneg_left (by linarith) hε.le⟩
  let A : Set Ω := {ω | ∃ N a b : ℤ,
      (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      t < |u ω a - u ω b| ∧
      ∃ x ∈ K, ∃ y ∈ B, x ∈ cell ε (η ω) a ∧ y ∈ cell ε (η ω) b ∧
        dist x y < δ ∧ (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
        (∀ j ∈ Finset.Ico N b, y ∉ cell ε (η ω) j)}
  refine ⟨A, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    exact BoundaryCell.measurableSet_bounded_index_oscillation η hηm u hum ε δ t K B hK hB hI
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
    have heq := BoundaryCell.bounded_index_oscillation_iff (η ω) (u ω) ε δ t K B hBK hbound hsel
    change (∃ N a b : ℤ, _) ↔ _
    rw [← heq]
    simp only [hηω, u, hvω, rescale]

/-- Boundary-pair oscillations are null measurable when the vertex values
have environment-measurable versions. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_rescale_boundary_pair
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (F : Ω → ℤ → ℝ)
    (v : Ω → ℤ → ℝ) (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a)
    (hv : ∀ᵐ ω ∂S.P, v ω = F ω)
    (K B : Set ℂ) (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K) (δ t : ℝ) :
    NullMeasurableSet {ω | ∃ x ∈ K, ∃ y ∈ B, dist x y < δ ∧
      t < |rescale (S.mε ε) ε (S.η ω) (F ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ω) y|} S.P := by
  obtain ⟨A, hAm, hAe⟩ :=
    hS.exists_envSigma_measurable_rescale_boundary_pair ε hε F v hvm hv K B hK hB hBK δ t
  apply (hS.nullMeasurableSet_of_envSigma hAm).congr
  filter_upwards [hAe] with ω hω
  exact propext hω

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_measurable_rescale_boundary_pair
#print axioms MatedCRT.MatedCRTEnv.IsValid.nullMeasurableSet_rescale_boundary_pair
