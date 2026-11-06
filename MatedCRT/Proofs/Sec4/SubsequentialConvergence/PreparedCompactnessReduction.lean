import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedSelectionFinal

/-! Local compactness and boundary control for prepared odometers. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- If every subsequence has a Hölder continuous uniform limit along a further
subsequence, then every uniform subsequential limit is Hölder continuous. -/
theorem odometerPreparedCompactness_of_holder_subsequences
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ t : ℝ} {e : ℕ → ℝ} {ω : Ω}
    (h : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧
      ∃ w : ℂ → ℝ, ContinuousOn w (closedBall 0 ρ) ∧
        IsHolderContinuousOn w (closedBall 0 ρ) ∧
        TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t
          (e (ψ (θ n))) ω) w atTop (closedBall 0 ρ)) :
    OdometerPreparedCompactness S ρ t e ω := by
  constructor
  · intro ψ hψ
    obtain ⟨θ, hθ, w, hw, _, hconv⟩ := h ψ hψ
    exact ⟨θ, hθ, w, hw, hconv⟩
  · intro ψ hψ w hw
    obtain ⟨θ, hθ, v, _, hv, hconv⟩ := h ψ hψ
    have heq : EqOn w v (closedBall 0 ρ) := by
      intro x hx
      exact tendsto_nhds_unique ((hw.tendsto_at hx).comp hθ.tendsto_atTop)
        (hconv.tendsto_at hx)
    obtain ⟨C, χ, hχ, hχ1, hv⟩ := hv
    refine ⟨C, χ, hχ, hχ1, ?_⟩
    intro x hx y hy
    rw [heq hx, heq hy]
    exact hv x hx y hy

/-- On a prepared mesh sequence every further sequence admits a locally
uniformly convergent subsequence (corrected paper, proof of Lemma 4.6). -/
def OdometerPreparedLocalCompactnessStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  EquiboundedStmt 𝒮 → DiscreteLaplacianBoundCorrectedStmt 𝒮 →
  DiscretePotentialTightnessPreparedStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
    ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
      OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ ∘ θ) ω w

/-- The prepared local compactness and the boundary upgrade yield prepared
compactness, including Hölder regularity of every uniform limit. -/
theorem odometerPreparedCompactnessStep_of_local_boundary
    (𝒮 : SpaceFillingSLEModel)
    (hl : OdometerPreparedLocalCompactnessStep 𝒮)
    (hb : OdometerBoundaryUpgradeCorrectedStep 𝒮) :
    OdometerPreparedCompactnessStep 𝒮 := by
  intro h47 h44 h31 h35 γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hlocal⟩ := hl h47 h44 h31 γ hγ hγ' ρ hρ hρ' Ω S hS t ht e he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hlocal, hb h44 h35 γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hlocal hboundary
  apply odometerPreparedCompactness_of_holder_subsequences
  intro ψ hψ
  obtain ⟨θ, hθ, w, hw⟩ := hlocal ψ hψ
  have hindex : StrictMono (φ ∘ ψ ∘ θ) := hφ.comp (hψ.comp hθ)
  obtain ⟨v, hv, hh, hc⟩ := hboundary t ht (e ∘ φ ∘ ψ ∘ θ)
    (fun n => he _) (he0.comp hindex.tendsto_atTop) w hw
  exact ⟨θ, hθ, v, hv, hh, hc⟩

/-- The corrected Lemma 4.6 follows from prepared local compactness and the
existing boundary upgrade. -/
theorem subsequentialConvergencePrepared_of_local_boundary
    (𝒮 : SpaceFillingSLEModel)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hl : OdometerPreparedLocalCompactnessStep 𝒮)
    (hb : OdometerBoundaryUpgradeCorrectedStep 𝒮) : SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_compactness 𝒮 h47 h44 h31 h35
    (odometerPreparedCompactnessStep_of_local_boundary 𝒮 hl hb)

end MatedCRT
