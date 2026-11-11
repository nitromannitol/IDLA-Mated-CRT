import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Final

/-!
# Lemma 4.6 from the corrected Lemmas 3.1 and 4.4

`subsequentialConvergence_of_steps` (MatedCRT/Steps/Sec4/SubsequentialConvergence.lean) passes the Draft Lemma 4.4
(`DiscreteLaplacianBoundStmt`, false in Lean: `not_discreteLaplacianBoundStmt`) and the Draft Lemma 3.1
(`DiscretePotentialTightnessStmt`, false for non-open `D`) to its steps. This file reroutes Lemma 4.6:

* `OdometerLocalCompactnessCorrectedStep` and `OdometerBoundaryUpgradeCorrectedStep` are the odometer steps with the corrected
  Lemma 3.1 (`DiscretePotentialTightnessCorrectedStmt`) and the corrected Lemma 4.4
  (`DiscreteLaplacianBoundCorrectedStmt`) in place of the Draft ones. The proof of Lemma 4.6
  (paper/idla_mated_crt-corrected.tex, l.1762-1765) uses Lemma 3.1 with `D = B_ρ`, which is open, and the conjunct
  `0 ≤ Δ^ε w̃^ε_t ≤ (deg^ε)⁻¹` on `V^ε(B_ρ) \ V^ε(∂B_ρ)` of Lemma 4.4, which the corrected form keeps.
* `subsequentialConvergence_of_corrected`: **Lemma 4.6** from Lemmas 4.7, 3.1 (corrected) and 3.5 and the steps, with
  the corrected Lemma 4.4 (`discreteLaplacianBoundCorrected`) discharged.
* `subsequentialConvergence_of_inputs`: the same with Lemma 4.7 (`equibounded_of_inputs`) and the corrected Lemma 3.1
  (`discretePotentialTightnessCorrected_of_inputs`) discharged from their cited inputs.

The local compactness step keeps the quantifier order of the Draft Lemma 4.6 (i): one almost sure event for all times
and all deterministic sequences. Lemmas 4.7 and 3.1 give an event for each sequence only, so this step is an
additional input, not a consequence of the cited estimates.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- `OdometerLocalCompactnessStep` with the corrected Lemmas 4.4 and 3.1: local compactness simultaneously for positive
times and mesh sequences. The almost sure event has stronger quantifiers than an event chosen separately for each
sequence. -/
def OdometerLocalCompactnessCorrectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  EquiboundedStmt 𝒮 → DiscreteLaplacianBoundCorrectedStmt 𝒮 →
  DiscretePotentialTightnessCorrectedStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ,
    (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → ℝ,
      OdometerLocalLimit S ρ t (εs ∘ φ) ω w

/-- `OdometerBoundaryUpgradeStep` with the corrected Lemma 4.4: the boundary barrier (Step 3 of the proof of
Lemma 3.5) upgrades a local limit to a Hölder continuous uniform limit on the closed ball, along the same subsequence. -/
def OdometerBoundaryUpgradeCorrectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → DiscreteDirichletProblemStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ,
    (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) → ∀ w : ℂ → ℝ,
    OdometerLocalLimit S ρ t εs ω w →
    ∃ v : ℂ → ℝ, ContinuousOn v (closedBall 0 ρ) ∧
      IsHolderContinuousOn v (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (εs n) ω)
        v atTop (closedBall 0 ρ)

/-- **Lemma 4.6** (lemma:subsequential-convergence, l.1731 of paper/idla_mated_crt-corrected.tex) from Lemma 4.7, the
corrected Lemma 3.1, Lemma 3.5 and the steps. The corrected Lemma 4.4 is discharged; neither the Draft Lemma 4.4 nor
the Draft Lemma 3.1 is used. -/
theorem subsequentialConvergence_of_corrected (𝒮 : SpaceFillingSLEModel)
    (h47 : EquiboundedStmt 𝒮) (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hlocal : OdometerLocalCompactnessCorrectedStep 𝒮)
    (hboundary : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hselect : OdometerMeasurableSelectionStep 𝒮) : SubsequentialConvergenceStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS
  have h44 := discreteLaplacianBoundCorrected 𝒮
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

/-- **Lemma 4.6** from the cited inputs of Lemmas 4.7 and 3.1 (corrected): eq:meps-scaling (`MepsScalingInput`),
Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`) and the corrected Lemma 3.2
(`DiscreteHolderContinuityCorrectedStep`), Lemma 3.5 and the steps. -/
theorem subsequentialConvergence_of_inputs {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hlocal : OdometerLocalCompactnessCorrectedStep 𝒮)
    (hboundary : OdometerBoundaryUpgradeCorrectedStep 𝒮)
    (hselect : OdometerMeasurableSelectionStep 𝒮) : SubsequentialConvergenceStmt 𝒮 :=
  subsequentialConvergence_of_corrected 𝒮 (equibounded_of_inputs h27 h218 hm)
    (discretePotentialTightnessCorrected_of_inputs hm h27 h218 hH) h35 hlocal hboundary hselect

end MatedCRT
