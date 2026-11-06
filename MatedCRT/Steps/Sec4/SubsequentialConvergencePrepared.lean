import MatedCRT.Draft.Section4Prepared
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.Corrected

/-! Prepared-sequence obligations for Lemma 4.6, corrected paper lines 1903–1910
and proof after line 1942. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The deterministic thinning provides relative compactness and Hölder limits
on one event, using the estimates cited in the proof of Lemma 4.6. -/
def OdometerPreparedCompactnessStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  EquiboundedStmt 𝒮 → DiscreteLaplacianBoundCorrectedStmt 𝒮 →
  DiscretePotentialTightnessCorrectedStmt 𝒮 → DiscreteDirichletProblemStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
    OdometerPreparedCompactness S ρ t (e ∘ φ) ω

/-- The measurable selection in Lemma 4.6 for a fixed prepared mesh sequence. -/
def OdometerPreparedSelectionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  (∀ᵐ ω ∂S.P, OdometerPreparedCompactness S ρ t e ω) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ w : ℂ → ℝ,
      ContinuousOn w (closedBall 0 ρ) ∧ IsHolderContinuousOn w (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (e (Φ ω k)) ω)
        w atTop (closedBall 0 ρ)

/-- The two prepared-sequence obligations imply the corrected Lemma 4.6. -/
theorem subsequentialConvergencePrepared_of_steps (𝒮 : SpaceFillingSLEModel)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hc : OdometerPreparedCompactnessStep 𝒮) (hs : OdometerPreparedSelectionStep 𝒮) :
    SubsequentialConvergencePreparedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hcompact⟩ := hc h47 h44 h31 h35 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht e he he0
  refine ⟨φ, hφ, hcompact, ?_⟩
  exact hs γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht (e ∘ φ) (fun n => he _) (he0.comp hφ.tendsto_atTop) hcompact

end MatedCRT
