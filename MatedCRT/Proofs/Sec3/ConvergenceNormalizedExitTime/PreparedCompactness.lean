import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PreparedModulusProbability
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedPathwiseExtraction
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.Prepared
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedBoundaryProof

/-! Prepared subsequential compactness for normalized exit times. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Every dyadic mesh sequence admits a deterministic preparation on which
the rescaled exit times are almost surely subsequentially compact. -/
theorem exit_compactness_dyadic_of_prepared
    (𝒮 : SpaceFillingSLEModel) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r) (hball : ball z r ⊆ ball 0 ρ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ θ : ℕ → ℕ, StrictMono θ → ∃ η : ℕ → ℕ, StrictMono η ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u (closedBall z r') ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (ψ (φ (θ (η k)))))) (ε (ψ (φ (θ (η k))))) (S.η ω)
            (normExitTime (S.mult (ε (ψ (φ (θ (η k))))) ω)
              (interiorCellVertices (ε (ψ (φ (θ (η k))))) (S.η ω) (ball z r))))
          u atTop (closedBall z r') := by
  let e : ℕ → ℝ := ε ∘ ψ
  have he : IsPolySummableScales ε := isPolySummableScales_of_lt_half_pow hε
  have hepos : ∀ n, 0 < e n := fun n => (hε (ψ n)).1
  have hezero : Tendsto e atTop (𝓝 0) := he.tendsto_zero.comp hψ.tendsto_atTop
  have hsize := ae_eventual_exit_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS hball ε he
    (fun _ n => e n) (fun _ n => ⟨ψ n, rfl⟩) (fun _ => hezero)
  obtain ⟨C, hCm, hC, hCa⟩ := hS.exists_measurable_exit_time_bound_of_eventual
    e (fun _ n => n) (fun _ => measurable_const) (fun _ n => hepos n)
    (ball z r) (Or.inl isOpen_ball) isBounded_ball hsize
  have hbounds := hS.ae_exit_bounds_of_eventual_size hγ hγ2 (ball z r) isBounded_ball
    (fun _ n => e n) (fun _ n => hepos n) C hC
    (by filter_upwards [hCa] with ω hω; exact Eventually.of_forall (fun n a _ => hω n a))
  obtain ⟨u, hum, hue⟩ := hS.exists_envSigma_measurable_selected_normExitTime e (ball z r)
    (Or.inl isOpen_ball) (fun _ n => n) (fun _ => measurable_const)
  have hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (u ω n) a| ≤ C) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), |u ω n a| ≤ C / e n) := by
    filter_upwards [hbounds, hue] with ω hb hu
    refine ⟨C ω, zero_lt_one.trans_le (hC ω), ?_⟩
    filter_upwards [hb] with n hn
    have hfun : u ω n = normExitTime (S.mult (e n) ω)
        (interiorCellVertices (e n) (S.η ω) (ball z r)) := funext (hu n)
    rw [hfun]
    exact hn
  obtain ⟨φ, hφ, hcompact⟩ := preparedTightness_pathwise_local 𝒮 h31 hγ hγ2 hρ hρ1
    S hS (ball z r) hball isOpen_ball ((convex_ball z r).isConnected (nonempty_ball.2 hr))
    e hepos hezero u hum hbound
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hcompact, hue] with ω hω hu θ hθ
  obtain ⟨η, hη, v, hv, hvconv⟩ := hω θ hθ
  have hKD : closure (closedBall z r') ⊆ ball z r := by
    rw [isClosed_closedBall.closure_eq]
    exact closedBall_subset_ball hr'
  refine ⟨η, hη, v, hv.mono (subset_closure.trans hKD), ?_⟩
  have hfun : ∀ n, u ω n = normExitTime (S.mult (e n) ω)
      (interiorCellVertices (e n) (S.η ω) (ball z r)) := fun n => funext (hu n)
  simpa only [hfun, e, Function.comp_apply] using hvconv (closedBall z r') (isCompact_closedBall _ _) hKD

/-- The prepared form of Lemma 3.1 yields the interior step of Lemma 3.7. -/
theorem normalizedExitInteriorPreparedStep (𝒮 : SpaceFillingSLEModel) :
    NormalizedExitInteriorPreparedStep 𝒮 := by
  intro h33 h35 h217 h218 h31 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball r' hr'
  apply normalizedExitInterior_of_discrete_modulus 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1
    S hS hr hr' hball
  intro t ht e he
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply mesh_modulus_of_dyadic_prepared_compactness S.P (closedBall z r')
    (isCompact_closedBall _ _) _ t ht ?_ ?_ he
  · intro ε hε δ
    obtain ⟨A, hAm, hAe⟩ := hS.exists_envSigma_measurable_exit_oscillation ε hε
      (ball z r) (Or.inl isOpen_ball) (closedBall z r') (isCompact_closedBall _ _) δ t
    apply (hS.nullMeasurableSet_of_envSigma hAm).congr
    filter_upwards [hAe] with ω hω
    exact propext hω
  · exact exit_compactness_dyadic_of_prepared 𝒮 h218 h217 h31 hγ hγ2 hρ hρ1 S hS hr hr' hball

/-- Lemma 3.7 from its prepared tightness input and the cited estimates. -/
theorem convergenceNormalizedExitTime_of_prepared (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_prepared_steps 𝒮 h33 h35 h217 h218 h31
    (normalizedExitInteriorPreparedStep 𝒮)

/-- Lemma 3.7 with prepared tightness supplied by the discrete estimates. -/
theorem convergenceNormalizedExitTime_of_prepared_estimates (𝒮 : SpaceFillingSLEModel)
    (hm : MepsScalingInput 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_prepared 𝒮 h33 h35 h217 h218
    (discretePotentialTightnessPrepared_of_inputs hm h217 h218 hH)

end MatedCRT

#print axioms MatedCRT.normalizedExitInteriorPreparedStep
#print axioms MatedCRT.convergenceNormalizedExitTime_of_prepared_estimates
