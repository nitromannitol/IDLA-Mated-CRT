import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4

/-! # Lemma 4.6: local compactness, boundary control and measurable selection -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Local uniform convergence on compact subsets of the ball. -/
def OdometerLocalLimit {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ t : ℝ) (εs : ℕ → ℝ) (ω : Ω) (w : ℂ → ℝ) : Prop :=
  ContinuousOn w (ball 0 ρ) ∧
    ∀ K : Set ℂ, IsCompact K → closure K ⊆ ball 0 ρ →
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (εs n) ω)
        w atTop K

/-- Local compactness simultaneously for positive times and mesh sequences. The almost sure
event here has stronger quantifiers than an event chosen separately for each sequence. -/
def OdometerLocalCompactnessStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  EquiboundedStmt 𝒮 → DiscreteLaplacianBoundStmt 𝒮 →
  DiscretePotentialTightnessStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ,
    (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → ℝ,
      OdometerLocalLimit S ρ t (εs ∘ φ) ω w

/-- The boundary barrier upgrades a local limit to a Hölder continuous uniform limit on the
closed ball, along the same subsequence. -/
def OdometerBoundaryUpgradeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundStmt 𝒮 → DiscreteDirichletProblemStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ,
    (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) → ∀ w : ℂ → ℝ,
    OdometerLocalLimit S ρ t εs ω w →
    ∃ v : ℂ → ℝ, ContinuousOn v (closedBall 0 ρ) ∧
      IsHolderContinuousOn v (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (εs n) ω)
        v atTop (closedBall 0 ρ)

/-- A measurable choice of a convergent subsequence from an almost sure pathwise existence
statement, for each fixed time and deterministic sequence. -/
def OdometerMeasurableSelectionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  (∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → ℝ,
    ContinuousOn w (closedBall 0 ρ) ∧ IsHolderContinuousOn w (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ k)) ω)
        w atTop (closedBall 0 ρ)) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ w : ℂ → ℝ,
      ContinuousOn w (closedBall 0 ρ) ∧ IsHolderContinuousOn w (closedBall 0 ρ) ∧
        TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (Φ ω k)) ω)
          w atTop (closedBall 0 ρ)

/-- Lemma 4.6 from local compactness, the boundary barrier and measurable selection. -/
theorem subsequentialConvergence_of_steps (𝒮 : SpaceFillingSLEModel)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hlocal : OdometerLocalCompactnessStep 𝒮) (hboundary : OdometerBoundaryUpgradeStep 𝒮)
    (hselect : OdometerMeasurableSelectionStep 𝒮) : SubsequentialConvergenceStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS
  have hpath : ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ,
      (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → ℝ,
        ContinuousOn w (closedBall 0 ρ) ∧ IsHolderContinuousOn w (closedBall 0 ρ) ∧
          TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ k)) ω)
            w atTop (closedBall 0 ρ) := by
    filter_upwards [hlocal h47 h44 h31 γ hγ hγ' ρ hρ hρ' Ω S hS,
      hboundary h44 h35 γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hl hb
    intro t ht εs hε hε0
    obtain ⟨φ, hφ, w, hw⟩ := hl t ht εs hε hε0
    obtain ⟨v, hv, hh, hc⟩ := hb t ht (εs ∘ φ) (fun n => hε _) (hε0.comp hφ.tendsto_atTop) w hw
    exact ⟨φ, hφ, v, hv, hh, hc⟩
  refine ⟨hpath, ?_⟩
  intro t ht εs hε hε0
  apply hselect γ hγ hγ' ρ hρ hρ' Ω S hS t ht εs hε hε0
  filter_upwards [hpath] with ω hω
  exact hω t ht εs hε hε0

end MatedCRT
