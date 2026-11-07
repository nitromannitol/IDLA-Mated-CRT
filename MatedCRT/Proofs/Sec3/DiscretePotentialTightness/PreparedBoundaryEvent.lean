import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedInteriorEvent
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedVertexModuli
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AeTightnessCompactness

/-! Reduction of prepared compactness to the common-event boundary estimate. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The conditional boundary vertex modulus on one event for every
polynomially summable preparation, corrected proof of Lemma 3.1, lines 1129–1140. -/
def PreparedBoundaryVertexModuliStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ e : ℕ → ℝ, IsPolySummableScales e →
  ∀ᵐ ω ∂S.P, ∀ (D : ℕ → Set ℂ),
    (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
    ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
      (∀ n, E ω n ∈ range e) → Tendsto (E ω) atTop (𝓝 0) →
      PreparedTightnessBounds S D E u C ω → ∀ j,
      PreparedHolderBoundary S (D j) E (u j) ω →
      IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u j ω) (closure (D j))

/-- Interior estimates and a common-event boundary modulus yield the prepared
vertex moduli after a deterministic polynomially summable thinning. -/
theorem preparedTightnessVertexModuliStep_of_boundary
    {𝒮 : SpaceFillingSLEModel} (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hboundary : PreparedBoundaryVertexModuliStep 𝒮) : PreparedTightnessVertexModuliStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he he0
  obtain ⟨φ, hφ, hφe⟩ := extraction_forall_of_eventually
    (P := fun n k => 0 < e k ∧ e k < (1 / 2 : ℝ) ^ n) fun n => by
      filter_upwards [he0.eventually (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))] with k hk
      exact ⟨he k, hk⟩
  have hpoly : IsPolySummableScales (e ∘ φ) := isPolySummableScales_of_lt_half_pow hφe
  have hinterior := ae_prepared_interior_vertex_modulus 𝒮 h217 h218 hH hγ hγ2 hρ hρ1 S hS (e ∘ φ) hpoly
  have hboundary' := hboundary γ hγ hγ2 ρ hρ hρ1 Ω S hS (e ∘ φ) hpoly
  let A : Set Ω := {ω | (∀ (ε : ℕ → ℝ), (∀ n, ε n ∈ range (e ∘ φ)) → Tendsto ε atTop (𝓝 0) →
      ∀ (D K : Set ℂ) (u : ℕ → ℤ → ℝ) (C : ℝ),
      IsOpen D → D ⊆ ball 0 ρ → IsCompact K → K ⊆ D → 0 ≤ C →
      (∀ n, ∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
        |matedLaplacian (S.mult (ε n) ω) (u n) a| ≤ C) →
      (∀ n, ∀ a ∈ cellVertices (ε n) (S.η ω) D, |u n a| ≤ C / ε n) →
      IsVertexAsymptoticallyEquicontinuous ε (S.η ω) u K) ∧
    (∀ (D : ℕ → Set ℂ), (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
    ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
      (∀ n, E ω n ∈ range (e ∘ φ)) → Tendsto (E ω) atTop (𝓝 0) →
      PreparedTightnessBounds S D E u C ω → ∀ j,
      PreparedHolderBoundary S (D j) E (u j) ω →
      IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u j ω) (closure (D j)))}
  refine ⟨φ, hφ, A, ?_, ?_⟩
  · filter_upwards [hinterior, hboundary'] with ω hi hb
    exact ⟨hi, hb⟩
  · intro D hD E u C hEm hEr hE0 hum hCm ω hω hb j
    refine ⟨?_, hω.2 D hD E u C (hEr ω) (hE0 ω) hb j⟩
    intro K hK hKD
    exact hω.1 (E ω) (hEr ω) (hE0 ω) (D j) K (u j ω) (C j ω)
      (hD j).2.1 (hD j).1 hK hKD (hb j).1.le (hb j).2.1 (hb j).2.2

end MatedCRT

#print axioms MatedCRT.preparedTightnessVertexModuliStep_of_boundary
