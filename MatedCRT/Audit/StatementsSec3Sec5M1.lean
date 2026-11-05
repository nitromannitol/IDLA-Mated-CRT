import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationTail
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Escape
import MatedCRT.Proofs.Sec1.ScaledClusterExitTime
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfInteriorBoundary
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Main
import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs
import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Audit.Refutations
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DyadicModulus
import MatedCRT.Proofs.Sec5.IDLALowerBound.Final
import MatedCRT.Proofs.IDLA.WalkerLawMeasurable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationGreen

/-! A logical check for the quantifier-order issue in Lemma 5.3.
It does not assert that the actual Green-function estimate has this form. -/
namespace MatedCRT.Audit.StatementsSec3Sec5M1

/-- In a valid environment, the IDLA probability uses the joint law of the walker sequence. -/
theorem five_one_idla_joint_law {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    (E : Set (Ω × (ℕ → ℕ → ℤ))) : S.idlaProb ε E = hS.idlaJointLaw ε E := by
  exact congrArg (fun μ => μ E) (hS.idlaJointMeasure_eq ε)

/-- A fixed occupied set with finite expected exit time avoids the IDLA nonexit fallback almost surely. -/
theorem five_one_fixed_set_exits (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (hmean : expectedExitTime m A a ≠ ⊤) :
    ∀ᵐ x ∂srwLaw m a, ∃ b, firstExitSite A x = some b := by
  classical
  filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean] with x hx
  by_cases h : ∃ n, x n ∉ A
  · exact ⟨x (Nat.find h), by simp [firstExitSite, h]⟩
  · exact False.elim (hx (by simp [vExitTime, h]))

/-- The counterexample applies to the exact Draft, conditional on the scaling input. -/
theorem three_one_draft_refuted {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) : ¬ DiscretePotentialTightnessStmt 𝒮 :=
  MatedCRT.Audit.Refutations.not_discretePotentialTightnessStmt hm hγ hγ2 hS

/-- The newer 3.7 reduction uses the almost-sure tightness step, not Draft 3.1. -/
theorem three_seven_latest_reduction (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hAe : DiscretePotentialTightnessAeStep 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_statements 𝒮 h33 h35 h217 h218 hAe

/-- A witness chosen separately for each positive time need not be uniform in time. -/
theorem time_dependent_witness_not_uniform :
    (∀ t : ℝ, 0 < t → ∃ s : ℝ, 0 < s ∧ s < t) ∧
      ¬ (∃ s : ℝ, 0 < s ∧ ∀ t : ℝ, 0 < t → s < t) := by
  constructor
  · intro t ht
    exact ⟨t / 2, by linarith, by linarith⟩
  · rintro ⟨s, hs, h⟩
    have := h (s / 2) (by linarith)
    linarith

/-- The relaxed form of Lemma 5.2 really supplies the Draft statement. -/
theorem relaxed_five_two_implies_draft (𝒮 : SpaceFillingSLEModel)
    (h : GeneralIDLALowerBoundRelaxedStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_relaxed 𝒮 h

/-- The available Lemma 3.1 reduction concludes its corrected form. -/
theorem three_one_corrected_reduction {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_boundedExitTime hm h217 h218 h32

/-- The Lemma 3.3 reduction uses the almost-sure corrected tightness step. -/
theorem three_three_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessAeStep 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hi : GreenKernelInteriorStep 𝒮) (hb : GreenKernelBoundaryStep 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_steps 𝒮 h210 h34 h214 h28 h31 h213 hi hb

/-- The available Lemma 3.6 reduction concludes the Draft with two open steps. -/
theorem three_six_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hp : HarmonicPathExitStep 𝒮) (hc : HarmonicExitCellStep 𝒮) :
    ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_of_steps 𝒮 h211 h28 hp hc

/-- The available Lemma 3.7 reduction consumes the Draft Lemma 3.1. -/
theorem three_seven_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hi : NormalizedExitInteriorStep 𝒮)
    (hb : DiscreteExitBoundaryStep 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_interior_discrete_boundary 𝒮 h33 h29 h219 h35 h31 h28 h217 hi hb

/-- Proposition 5.1 retains the stopped and discrete inner-cluster steps. -/
theorem five_one_draft_reduction (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h53 : MeanValueInequalityStmt 𝒮)
    (h54 : LLowerBoundStmt 𝒮) (hi : DiscreteClusterInnerBoundStep 𝒮)
    (hs : IDLALowerBoundStoppedStep 𝒮) : IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28 h53 h54 hi hs

/-- The strict-gap reduction of Proposition 5.1 concludes the exact Draft conditionally. -/
theorem five_one_strict_gap_reduction (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hlow : MeanValueSurplusLowerStep 𝒮)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) (hSM : StoppedMeanValueInequalityStep 𝒮)
    (hSL : StoppedLLowerBoundStep 𝒮) : IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_final_of_strictGap 𝒮 h27 h28 h29 h215 h216 h218 h41 h23 h24 h33 h217 h44
    hfam hμ hlow hgap hSM hSL

/-- Lemma 5.4 is reduced to three explicitly stated hypotheses. -/
theorem five_four_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  lLowerBound_of_inputs 𝒮 h215 h216 h29

/-- Lemma 3.5 uses the corrected tightness statement. -/
theorem three_five_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hl : DirichletLimitStep 𝒮) (hi : DirichletInteriorStep 𝒮) (hb : DirichletBoundaryStep 𝒮) :
    DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_steps 𝒮 hGP h36 h34 h31 h213 h219 h28 hl hi hb

/-- Lemma 5.2 has a reduction with two hypotheses. -/
theorem five_two_draft_reduction (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28

/-- Lemma 5.3 uses a surplus step and corrected Lemma 4.4. -/
theorem five_three_draft_reduction (𝒮 : SpaceFillingSLEModel)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hs : MeanValueSurplusStep 𝒮) : MeanValueInequalityStmt 𝒮 :=
  meanValueInequality_of_surplus 𝒮 h44 h213 h41 h33 h218 hs

/-- A pointwise measurable random function on a domain has a pointwise measurable extension. -/
theorem three_four_measurable_extension {Ω : Type} [MeasurableSpace Ω]
    (D : Set ℂ) (f : Ω → D → ℝ)
    (hf : ∀ x : D, Measurable (fun ω => f ω x)) :
    ∃ g : Ω → ℂ → ℝ, (∀ x, Measurable (fun ω => g ω x)) ∧
      ∀ ω x (hx : x ∈ D), g ω x = f ω ⟨x, hx⟩ := by
  classical
  let g : Ω → ℂ → ℝ := fun ω x => if hx : x ∈ D then f ω ⟨x, hx⟩ else 0
  refine ⟨g, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ D
    · simpa [g, hx] using hf ⟨x, hx⟩
    · simp [g, hx]
  · intro ω x hx
    simp [g, hx]

/-- The discrete Green sum in Lemma 3.4 depends only on test-function values on the ball. -/
theorem three_four_sum_ext (m : ℤ → ℤ → ℕ) {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hη : Continuous η) (z : ℂ) (r : ℝ) (a : ℤ)
    (f g : ℂ → ℝ) (hfg : ∀ x ∈ Metric.ball z r, f x = g x) :
    (∑' x : cellVertices ε η (Metric.ball z r),
      greenFn m (interiorCellVertices ε η (Metric.ball z r)) a x * f (vertexPoint ε η x)) =
    (∑' x : cellVertices ε η (Metric.ball z r),
      greenFn m (interiorCellVertices ε η (Metric.ball z r)) a x * g (vertexPoint ε η x)) := by
  apply tsum_congr
  intro x
  by_cases hx : (x : ℤ) ∈ interiorCellVertices ε η (Metric.ball z r)
  · rw [hfg _ (vertexPoint_mem_ball_of_mem_interior hε hη hx)]
  · simp [Sec7.greenFn_eq_zero_of_not_mem_right m a hx]

/-- On the finite first-step event, the Green quotient in Lemma 5.4 has its finite-sum interpretation. -/
theorem five_four_green_quotient_semantics {m : ℤ → ℤ → ℕ} {A : Set ℤ} {a : ℤ}
    (hA : A.Finite) (ha : a ∈ A)
    (hfirst : ∀ b, ∀ x ∈ A,
      mLaplacian m (fun y => greenFn m A y b) x = -(if x = b then 1 else 0)) :
    0 < greenFn m A a a ∧
      (∑' b : A, greenFn m A b a) / greenFn m A a a =
        (∑ b ∈ hA.toFinset, greenFn m A b a) / greenFn m A a a := by
  refine ⟨greenFn_diag_pos_of_firstStep ha hfirst, ?_⟩
  exact congrArg (fun x : ℝ => x / greenFn m A a a)
    (tsum_subtype_eq_toFinset_sum hA (fun b => greenFn m A b a))

/-- Under finite local mass and a positive contained time, the cluster exit time is positive and finite. -/
theorem cluster_exit_time_bounded {μ : MeasureTheory.Measure ℂ} {Λ : ℝ → Set ℂ} {ρ : ℝ}
    (hΛ : HarmonicBalls.SatisfiesHarmonicBallConditions μ Λ 0)
    (hfin : μ (Metric.ball 0 (ρ / 3)) ≠ ⊤)
    (hsmall : ∃ s, 0 < s ∧ Λ s ⊆ Metric.ball 0 (ρ / 3)) :
    0 < clusterExitTime Λ ρ ∧
      clusterExitTime Λ ρ ≤ (μ (Metric.ball 0 (ρ / 3))).toReal := by
  refine ⟨(Sec1.clusterExitTime_spec hΛ hfin hsmall).2.1, ?_⟩
  unfold clusterExitTime
  apply csSup_le
  · obtain ⟨s, hs, hsub⟩ := hsmall
    exact ⟨s, hs, hsub⟩
  · intro t ht
    have hmass : μ (Λ t) ≤ μ (Metric.ball 0 (ρ / 3)) := MeasureTheory.measure_mono ht.2
    rw [hΛ.measure_eq t ht.1] at hmass
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hmass

#print axioms cluster_exit_time_bounded
#print axioms five_one_idla_joint_law
#print axioms five_one_fixed_set_exits
#print axioms three_one_draft_refuted
#print axioms three_seven_latest_reduction
#print axioms five_four_green_quotient_semantics
#print axioms three_four_sum_ext
#print axioms three_four_measurable_extension
#print axioms three_five_draft_reduction
#print axioms five_two_draft_reduction
#print axioms five_three_draft_reduction
#print axioms three_one_corrected_reduction
#print axioms three_three_draft_reduction
#print axioms three_six_draft_reduction
#print axioms three_seven_draft_reduction
#print axioms five_one_draft_reduction
#print axioms five_one_strict_gap_reduction
#print axioms five_four_draft_reduction
#print axioms time_dependent_witness_not_uniform
#print axioms relaxed_five_two_implies_draft

end MatedCRT.Audit.StatementsSec3Sec5M1
