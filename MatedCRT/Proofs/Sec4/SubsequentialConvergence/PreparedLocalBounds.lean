import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedCompactnessReduction
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedPathwiseExtraction

/-! Prepared local odometer compactness from vertex bounds. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The eventual vertex estimates used to apply Lemma 3.1 to the odometer.
They are the application of Lemmas 4.4 and 4.7 in the proof of Lemma 4.6. -/
def OdometerPreparedDataBoundsStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  EquiboundedStmt 𝒮 → DiscreteLaplacianBoundCorrectedStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
    (∀ a ∈ interiorCellVertices (e (φ n)) (S.η ω) (ball 0 ρ),
      |matedLaplacian (S.mult (e (φ n)) ω)
        (matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t) a| ≤ C) ∧
    (∀ a ∈ cellVertices (e (φ n)) (S.η ω) (ball 0 ρ),
      |matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t a| ≤
        C / e (φ n))

/-- Prepared tightness and the vertex estimates give local compactness on one
event for every further subsequence. -/
theorem odometerPreparedLocalCompactnessStep_of_dataBounds
    (𝒮 : SpaceFillingSLEModel) (hdata : OdometerPreparedDataBoundsStep 𝒮) :
    OdometerPreparedLocalCompactnessStep 𝒮 := by
  intro h47 h44 h31 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hbound⟩ := hdata h47 h44 γ hγ hγ' ρ hρ hρ' Ω S hS t ht e he he0
  have hlf := ae_locallyFinite_mult_of_adjacentCells hS hγ hγ' (adjacentCellsMeetAeStep 𝒮)
  have hu : ∀ n a, ∃ v : Ω → ℝ, Measurable[S.envSigma] v ∧
      ∀ᵐ ω ∂S.P, v ω = matedLeastSupersolution (S.mult (e (φ n)) ω)
        (e (φ n)) (S.η ω) ρ t a := by
    intro n a
    apply hS.exists_envSigma_measurable_matedLeastSupersolution hγ hγ' (he _) ρ t ht a
    filter_upwards [hlf] with ω hω
    exact hω (e (φ n)) (he _)
  obtain ⟨ξ, hξ, hlocal⟩ := preparedTightness_pathwise_local_ae 𝒮 h31 hγ hγ' hρ hρ' S hS
    (ball 0 ρ) (Subset.rfl) isOpen_ball (isConnected_ball hρ)
    (e ∘ φ) (fun n => he _) (he0.comp hφ.tendsto_atTop)
    (fun ω n => matedLeastSupersolution (S.mult (e (φ n)) ω) (e (φ n)) (S.η ω) ρ t)
    hu hbound
  refine ⟨φ ∘ ξ, hφ.comp hξ, ?_⟩
  filter_upwards [hlocal] with ω hω
  intro ψ hψ
  obtain ⟨θ, hθ, v, hv, hconv⟩ := hω ψ hψ
  refine ⟨θ, hθ, v, hv, ?_⟩
  intro K hK hKball
  exact hconv K hK hKball

end MatedCRT
