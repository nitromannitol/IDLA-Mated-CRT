import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedDataBounds

/-! The sequence-dependent boundary upgrade in the proof of Lemma 4.6. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- After deterministic preparation, the boundary barrier upgrades every local
limit along every further subsequence on one almost-sure event. This is the
boundary-control obligation in the corrected proof of Lemma 4.6. -/
def OdometerPreparedBoundaryUpgradeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → DiscreteDirichletProblemStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
    ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
    OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
    ∃ v : ℂ → ℝ, ContinuousOn v (closedBall 0 ρ) ∧
      IsHolderContinuousOn v (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t
        (e (φ (ψ n))) ω) v atTop (closedBall 0 ρ)

/-- The earlier, sequence-uniform boundary obligation implies the prepared one. -/
theorem odometerPreparedBoundaryUpgradeStep_of_corrected
    (𝒮 : SpaceFillingSLEModel) (hb : OdometerBoundaryUpgradeCorrectedStep 𝒮) :
    OdometerPreparedBoundaryUpgradeStep 𝒮 := by
  intro h44 h35 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  refine ⟨id, strictMono_id, ?_⟩
  filter_upwards [hb h44 h35 γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hω
  intro ψ hψ w hw
  exact hω t ht (e ∘ id ∘ ψ) (fun n => he _) (he0.comp hψ.tendsto_atTop) w hw

/-- Two deterministic preparations can be composed before invoking local
compactness and the boundary barrier on arbitrary further subsequences. -/
theorem odometerPreparedCompactnessStep_of_prepared_boundary
    (𝒮 : SpaceFillingSLEModel)
    (hl : OdometerPreparedLocalCompactnessStep 𝒮)
    (hb : OdometerPreparedBoundaryUpgradeStep 𝒮) :
    OdometerPreparedCompactnessStep 𝒮 := by
  intro h47 h44 h31 h35 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hboundary⟩ := hb h44 h35 γ hγ hγ' ρ hρ hρ' Ω S hS t ht e he he0
  obtain ⟨θ, hθ, hlocal⟩ := hl h47 h44 h31 γ hγ hγ' ρ hρ hρ' Ω S hS t ht
    (e ∘ φ) (fun n => he _) (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ θ, hφ.comp hθ, ?_⟩
  filter_upwards [hboundary, hlocal] with ω hboundary hlocal
  apply odometerPreparedCompactness_of_holder_subsequences
  intro ψ hψ
  obtain ⟨κ, hκ, w, hw⟩ := hlocal ψ hψ
  obtain ⟨v, hv, hh, hc⟩ := hboundary (θ ∘ ψ ∘ κ)
    (hθ.comp (hψ.comp hκ)) w hw
  exact ⟨κ, hκ, v, hv, hh, hc⟩

/-- Corrected Lemma 4.6 from median scaling and the prepared boundary barrier. -/
theorem subsequentialConvergencePrepared_of_mepsScaling_prepared_boundary
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hb : OdometerPreparedBoundaryUpgradeStep 𝒮) : SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_compactness 𝒮 h47 h44 h31 h35
    (odometerPreparedCompactnessStep_of_prepared_boundary 𝒮
      (odometerPreparedLocalCompactnessStep_of_mepsScaling 𝒮 hm) hb)

end MatedCRT
