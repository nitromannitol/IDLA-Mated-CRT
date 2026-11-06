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
import MatedCRT.Proofs.IDLA.Monotone
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationGreen
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.InteriorStep
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit
import MatedCRT.Steps.Sec2.VolumeGrowthHalf
import MatedCRT.Steps.Sec6.ChanceOfBeingAbsorbed

/-! A logical check for the quantifier-order issue in Lemma 5.3.
It does not assert that the actual Green-function estimate has this form. -/
namespace MatedCRT.Audit.StatementsSec3Sec5M1

open scoped ENNReal

/-- Two polynomially high probability events can be combined into one, and recovered from it. -/
theorem three_two_poly_high_prob_conjunction {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (E F : ℝ → Set Ω) :
    (HarmonicBalls.PolyHighProb P E ∧ HarmonicBalls.PolyHighProb P F) ↔
      HarmonicBalls.PolyHighProb P (fun ε => E ε ∩ F ε) := by
  constructor
  · rintro ⟨hE, hF⟩
    exact polyHighProb_of_inter hE hF (fun _ => Set.Subset.rfl)
  · intro h
    exact ⟨polyHighProb_mono_of_subset h (fun _ => Set.inter_subset_left),
      polyHighProb_mono_of_subset h (fun _ => Set.inter_subset_right)⟩

/-- In a valid environment, bounded domains meet only finitely many positive-mesh cells. -/
theorem three_two_bounded_domain_cell_vertices_finite {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (ρ : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ D : Set ℂ, D ⊆ Metric.ball 0 ρ →
      (cellVertices ε (S.η ω) D).Finite := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hη hp
  intro ε hε D hD
  refine (cellVertices_finite_of_isCompact hη.1 hp hε
    (isCompact_closedBall 0 ρ)).subset ?_
  rintro a ⟨z, hz, hzD⟩
  exact ⟨z, hz, Metric.ball_subset_closedBall (hD hzD)⟩

/-- A nonempty domain meets a positive-mesh cell in a valid environment. -/
theorem three_two_nonempty_domain_cell_vertices {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ D : Set ℂ, D.Nonempty →
      (cellVertices ε (S.η ω) D).Nonempty := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hη hp
  intro ε hε D ⟨z, hz⟩
  exact ⟨vertexOf ε (S.η ω) z, z,
    Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε z, hz⟩

/-- The indexed real supremum over finitely many vertices is their attained maximum. -/
theorem three_two_vertex_supremum_is_maximum {V : Set ℤ} (hV : V.Finite)
    (hne : V.Nonempty) (f : ℤ → ℝ) :
    ∃ a : V, (⨆ b : V, |f b|) = |f a| ∧ ∀ b : V, |f b| ≤ |f a| := by
  classical
  let _ : Fintype V := hV.fintype
  let _ : Nonempty V := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨a, ha⟩ := Finite.ciSup_mem (fun b : V => |f b|)
  change |f a| = ⨆ b : V, |f b| at ha
  refine ⟨a, ha.symm, fun b => ?_⟩
  rw [ha]
  exact le_ciSup (Set.finite_range (fun b : V => |f b|)).bddAbove b

/-- A pointwise bound is equivalent to a bounded real supremum bound on a nonempty set. -/
theorem three_three_pointwise_bound_iff_supremum {α : Type} (O : Set α)
    (hne : O.Nonempty) (u : α → ℝ) (δ : ℝ) :
    (∀ x ∈ O, u x ≤ δ) ↔
      BddAbove (Set.range fun x : O => u x) ∧ (⨆ x : O, u x) ≤ δ := by
  let _ : Nonempty O := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  constructor
  · intro h
    refine ⟨⟨δ, ?_⟩, ciSup_le fun x => h x x.property⟩
    rintro _ ⟨x, rfl⟩
    exact h x x.property
  · rintro ⟨hb, hs⟩ x hx
    exact (le_ciSup hb ⟨x, hx⟩).trans hs

/-- Probability convergence for all sufficiently small tolerances extends to every tolerance. -/
theorem three_three_small_tolerances_suffice {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (O : Set ℂ) (u : ℝ → Ω → ℂ → ℝ)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (h : ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ProbTendsToOne P (fun ε => {ω | ∀ x ∈ O, u ε ω x ≤ δ})) :
    ∀ δ : ℝ, 0 < δ → ProbTendsToOne P (fun ε => {ω | ∀ x ∈ O, u ε ω x ≤ δ}) := by
  intro δ hδ
  have hsmall : 0 < min δ (δ₀ / 2) := lt_min hδ (half_pos hδ₀)
  apply (h _ hsmall ((min_le_right _ _).trans_lt (half_lt_self hδ₀))).mono'
  intro ε ω hω x hx
  exact (hω x hx).trans (min_le_left _ _)

/-- The chosen vertex is the least cell vertex containing the point, at every positive mesh. -/
theorem three_three_vertexOf_is_least {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ x : ℂ,
      x ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) x) ∧
      ∀ k : ℤ, x ∈ cell ε (S.η ω) k →
        ε * (vertexOf ε (S.η ω) x : ℝ) ≤ ε * (k : ℝ) := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hη hp
  intro ε hε x
  refine ⟨Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε x, ?_⟩
  have hfinite : {k : ℤ | x ∈ cell ε (S.η ω) k}.Finite :=
    (Tightness.cellVertices_finite hη.1 hp hε (Bornology.isBounded_singleton (x := x))).subset
      (fun _ hk => ⟨x, hk, rfl⟩)
  intro k hk
  have hle : vertexOf ε (S.η ω) x ≤ k := csInf_le hfinite.bddBelow hk
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hε.le

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

/-- The current final Lemma 3.3 reduction concludes the exact Draft under its five inputs. -/
theorem three_three_final_reduction (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hAe : DiscretePotentialTightnessAeStep 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_final 𝒮 h210 h34 h214 h28 hAe

/-- The omitted empty test set is vacuous even though its infimum distance is zero. -/
theorem three_three_empty_test_set {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (y : ℂ) (P : ℝ → Ω → ℂ → Prop) :
    Metric.infDist y (∅ : Set ℂ) = 0 ∧
      ProbTendsToOne μ (fun ε => {ω | ∀ x ∈ (∅ : Set ℂ), P ε ω x}) := by
  simp [Metric.infDist_empty, ProbTendsToOne]

/-- Finite locally finite domains with consecutive edges have finite expected visit counts. -/
theorem three_three_green_visit_integral_ne_top {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hA : A.Finite) (a b : ℤ) :
    (∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a) ≠ ⊤ := by
  obtain ⟨v, -, hvΔ, hv0⟩ := exists_nonneg_laplacian_eq hcons hlf hA
    (fun c => -(if c = b then (1 : ℝ) else 0)) fun c _ => by split_ifs <;> norm_num
  have hdeg : ∀ c, mdeg m c ≠ 0 := fun c => mdeg_ne_zero_of_ne_zero hlf (hcons c)
  have hv : ∀ c ∈ A, v c = (if c = b then 1 else 0) +
      ((mdeg m c : ℝ))⁻¹ * ∑ d ∈ nbrs hlf c, (m c d : ℝ) * v d :=
    fun c hc => (WalkPotential.mLaplacian_eq_neg_iff hlf (hdeg c) v _).1 (hvΔ c hc)
  have hup := WalkPotential.lintegral_visitsUpTo_le hlf hcons b hv0 hv
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (?_ : _ ≤ ENNReal.ofReal (v a))
  rw [WalkPotential.lintegral_visitsBeforeExit_eq_iSup]
  exact iSup_le fun n => hup n a

/-- The number of visits to a domain before exit is its exit time. -/
theorem visitCount_self_eq_exitTime (A : Set ℤ) (x : ℕ → ℤ) :
    ConstantOrderDiv.visitCount A A x = (vExitTime A x : ℝ≥0∞) := by
  classical
  unfold ConstantOrderDiv.visitCount
  have heq : ∀ n : ℕ, ((n : ℕ∞) < vExitTime A x ∧ x n ∈ A) ↔
      (n : ℕ∞) < vExitTime A x := fun _ => ⟨And.left, fun h => ⟨h, mem_of_lt_vExitTime h⟩⟩
  simp_rw [heq]
  cases hτ : vExitTime A x with
  | top => simp [ENNReal.tsum_one]
  | coe k =>
    simp only [Nat.cast_lt]
    rw [tsum_eq_sum (s := Finset.range k)]
    · rw [Finset.sum_congr rfl fun n hn => ite_eq_left (Finset.mem_range.mp hn)]
      simp
    · intro n hn
      exact ite_eq_right (fun h => hn (Finset.mem_range.mpr h))

/-- On finite locally finite domains with consecutive edges, the expected exit time is finite. -/
theorem finite_expectedExitTime {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hA : A.Finite) (a : ℤ) : expectedExitTime m A a ≠ ⊤ := by
  classical
  let _ : Fintype A := hA.fintype
  have heq : expectedExitTime m A a = ∑' b : A,
      ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a := by
    unfold expectedExitTime
    rw [← MeasureTheory.lintegral_tsum (fun b : A => (ConstantOrderDiv.measurable_visitsBeforeExit A b).aemeasurable)]
    exact MeasureTheory.lintegral_congr fun x => by
      rw [ConstantOrderDiv.tsum_visitsBeforeExit, visitCount_self_eq_exitTime]
  rw [heq, tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun b _ => three_three_green_visit_integral_ne_top hlf hcons hA a b

/-- A walker exits any finite occupied set almost surely under the graph assumptions. -/
theorem five_one_finite_set_exits {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hA : A.Finite) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, ∃ b, firstExitSite A x = some b :=
  five_one_fixed_set_exits m A a (finite_expectedExitTime hlf hcons hA a)

/-- A walk exits every finite set simultaneously, almost surely. -/
theorem five_one_all_finite_sets_exit {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, ∀ A : Set ℤ, A.Finite → ∃ b, firstExitSite A x = some b := by
  classical
  have h : ∀ᵐ x ∂srwLaw m a, ∀ A : Finset ℤ,
      ∃ b, firstExitSite (A : Set ℤ) x = some b := by
    apply MeasureTheory.ae_all_iff.mpr
    intro A
    exact five_one_finite_set_exits hlf hcons A.finite_toSet a
  filter_upwards [h] with x hx A hA
  simpa only [Set.Finite.coe_toFinset] using hx hA.toFinset

/-- Every walker in the sequence exits every finite set, almost surely. -/
theorem five_one_all_walkers_exit_finite_sets {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ) :
    ∀ᵐ xs ∂walkerSequenceLaw m a, ∀ i : ℕ, ∀ A : Set ℤ,
      A.Finite → ∃ b, firstExitSite A (xs i) = some b := by
  apply MeasureTheory.ae_all_iff.mpr
  intro i
  let j : Fin (i + 1) := ⟨i, Nat.lt_succ_self i⟩
  have hp : ∀ᵐ ys ∂walkersLaw m (fun _ : Fin (i + 1) => a),
      ∀ A : Set ℤ, A.Finite → ∃ b, firstExitSite A (ys j) = some b := by
    have hmap : (walkersLaw m (fun _ : Fin (i + 1) => a)).map
        (fun ys : Fin (i + 1) → ℕ → ℤ => ys j) = srwLaw m a :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin (i + 1) => srwLaw m a) j).map_eq
    have he : ∀ᵐ x ∂(walkersLaw m (fun _ : Fin (i + 1) => a)).map
        (fun ys : Fin (i + 1) → ℕ → ℤ => ys j),
        ∀ A : Set ℤ, A.Finite → ∃ b, firstExitSite A x = some b := by
      rw [hmap]
      exact five_one_all_finite_sets_exit hlf hcons a
    exact MeasureTheory.ae_of_ae_map (measurable_pi_apply j).aemeasurable he
  rw [← walkerSequenceLaw_map_fin m a (i + 1)] at hp
  exact MeasureTheory.ae_of_ae_map (measurable_restrictFin (i + 1)).aemeasurable hp

/-- For every release, the current stopped and unrestricted aggregates are exited almost surely. -/
theorem five_one_current_aggregates_exit {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ)
    (Θ : Set ℤ) :
    ∀ᵐ xs ∂walkerSequenceLaw m a, ∀ n : ℕ,
      (∃ b, firstExitSite (idlaCluster xs n) (xs n) = some b) ∧
      (∃ b, firstExitSite (stoppedIDLACluster Θ xs n) (xs n) = some b) := by
  filter_upwards [five_one_all_walkers_exit_finite_sets hlf hcons a] with xs hx n
  constructor
  · exact hx n (idlaCluster xs n)
      (foldl_idlaStep_card Set.univ (List.ofFn fun i : Fin n => xs i) (∅, []) Set.finite_empty).1
  · exact hx n (stoppedIDLACluster Θ xs n)
      (foldl_idlaStep_card Θ (List.ofFn fun i : Fin n => xs i) (∅, []) Set.finite_empty).1

/-- The event that all walkers leave all finite sets is measurable. -/
theorem five_one_measurable_all_walkers_exit :
    MeasurableSet {xs : ℕ → ℕ → ℤ | ∀ i : ℕ, ∀ A : Finset ℤ,
      ∃ b, firstExitSite (A : Set ℤ) (xs i) = some b} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun A =>
    MeasurableSet.iUnion fun b =>
      (Absorption.measurableSet_firstExitSite_eq (A : Set ℤ) (some b)).preimage (measurable_pi_apply i)

/-- Under the joint law, every walker exits every finite set almost surely. -/
theorem five_one_joint_all_walkers_exit {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ ε : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hε : 0 < ε) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ p ∂hS.idlaJointLaw ε, ∀ i : ℕ, ∀ A : Set ℤ,
      A.Finite → ∃ b, firstExitSite A (p.2 i) = some b := by
  have hlf := hS.ae_isLocallyFiniteMult hγ0 hγ2 (adjacentCellsMeetAeStep 𝒮)
  have h : ∀ᵐ p ∂hS.idlaJointLaw ε, ∀ i : ℕ, ∀ A : Finset ℤ,
      ∃ b, firstExitSite (A : Set ℤ) (p.2 i) = some b := by
    unfold MatedCRTEnv.IsValid.idlaJointLaw
    apply MeasureTheory.Measure.ae_compProd_of_ae_ae
      (five_one_measurable_all_walkers_exit.preimage measurable_snd)
    filter_upwards [hlf] with ω hω
    filter_upwards [five_one_all_walkers_exit_finite_sets (hω ε hε)
      (S.mult_succ_ne_zero hε.le ω) 0] with xs hxs i A
    exact hxs i A A.finite_toSet
  filter_upwards [h] with p hp i A hA
  simpa only [Set.Finite.coe_toFinset] using hp i hA.toFinset

/-- The current unrestricted and environment-stopped aggregates are exited under the joint law. -/
theorem five_one_joint_current_aggregates_exit {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ ε : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hε : 0 < ε) (hS : S.IsValid 𝒮 γ)
    (Θ : Ω → Set ℤ) :
    ∀ᵐ p ∂hS.idlaJointLaw ε, ∀ n : ℕ,
      (∃ b, firstExitSite (idlaCluster p.2 n) (p.2 n) = some b) ∧
      (∃ b, firstExitSite (stoppedIDLACluster (Θ p.1) p.2 n) (p.2 n) = some b) := by
  filter_upwards [five_one_joint_all_walkers_exit hγ0 hγ2 hε hS] with p hp n
  constructor
  · exact hp n (idlaCluster p.2 n)
      (foldl_idlaStep_card Set.univ (List.ofFn fun i : Fin n => p.2 i) (∅, []) Set.finite_empty).1
  · exact hp n (stoppedIDLACluster (Θ p.1) p.2 n)
      (foldl_idlaStep_card (Θ p.1) (List.ofFn fun i : Fin n => p.2 i) (∅, []) Set.finite_empty).1

/-- Abstractly, an exponent chosen after a positive constant need not be uniform in that constant.
This is a quantifier counterexample, not a counterexample to the Hölder estimate. -/
theorem three_two_constant_dependent_exponent_not_uniform :
    (∀ C : ℝ, 0 < C → ∃ ξ : ℝ, 0 < ξ ∧ ξ * C ≤ 1) ∧
      ¬ (∃ ξ : ℝ, 0 < ξ ∧ ∀ C : ℝ, 0 < C → ξ * C ≤ 1) := by
  constructor
  · intro C hC
    refine ⟨(2 * C)⁻¹, inv_pos.mpr (by positivity), ?_⟩
    have hc : C ≠ 0 := ne_of_gt hC
    have heq : (2 * C)⁻¹ * C = (1 / 2 : ℝ) := by field_simp
    rw [heq]
    norm_num
  · rintro ⟨ξ, hξ, h⟩
    have hc : 0 < 2 / ξ := by positivity
    have heq : ξ * (2 / ξ) = (2 : ℝ) := by field_simp
    have hh := h (2 / ξ) hc
    rw [heq] at hh
    norm_num at hh

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

/-- A measurable almost-surely positive surplus has a strictly positive measurable version. -/
theorem five_two_positive_surplus_version {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (𝓕 : MeasurableSpace Ω) (s : Ω → ℝ)
    (hs : @Measurable Ω ℝ 𝓕 _ s)
    (hpos : ∀ᵐ ω ∂μ, 0 < s ω) :
    ∃ t : Ω → ℝ, @Measurable Ω ℝ 𝓕 _ t ∧ (∀ ω, 0 < t ω) ∧ t =ᵐ[μ] s := by
  classical
  let t : Ω → ℝ := fun ω => if 0 < s ω then s ω else 1
  refine ⟨t, ?_, ?_, ?_⟩
  · let : MeasurableSpace Ω := 𝓕
    exact Measurable.ite (measurableSet_lt measurable_const hs) hs measurable_const
  · intro ω
    by_cases h : 0 < s ω <;> simp [t, *]
  · filter_upwards [hpos] with ω hω
    simp [t, hω]

/-- Null-set changes to events preserve convergence of their probabilities to one. -/
theorem five_two_probTendsToOne_congr {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (E F : ℝ → Set Ω)
    (h : ∀ᵐ ω ∂μ, ∀ ε, ω ∈ E ε ↔ ω ∈ F ε) :
    ProbTendsToOne μ E ↔ ProbTendsToOne μ F := by
  have heq : ∀ ε, μ (E ε)ᶜ = μ (F ε)ᶜ := by
    intro ε
    apply MeasureTheory.measure_congr
    filter_upwards [h] with ω hω
    exact propext (not_congr (hω ε))
  unfold ProbTendsToOne
  simp_rw [heq]

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

/-- Interior cells of a proper domain have positive marked-point distance from its frontier. -/
theorem three_two_interior_distance_pos {ε : ℝ} {η : ℝ → ℂ} {D : Set ℂ} {a : ℤ}
    (hε : 0 ≤ ε) (hD : D ≠ Set.univ)
    (ha : a ∈ interiorCellVertices ε η D) :
    0 < Metric.infDist (vertexPoint ε η a) (frontier D) := by
  have hnonempty : D.Nonempty := by
    obtain ⟨x, _, hx⟩ := ha.1
    exact ⟨x, hx⟩
  have hfrontier : (frontier D).Nonempty := nonempty_frontier_iff.mpr ⟨hnonempty, hD⟩
  apply (isClosed_frontier.notMem_iff_infDist_pos hfrontier).1
  intro hmem
  exact ha.2 ⟨vertexPoint ε η a, Sec7.vertexPoint_mem_cell hε a, hmem⟩

/-- At positive boundary distance, the multiplied and quotient Hölder bounds agree. -/
theorem three_two_holder_quotient_iff (L A u d ξ : ℝ) (hu : 0 ≤ u) (hd : 0 < d) :
    L * d ^ ξ ≤ A * u ^ ξ ↔ L ≤ A * (u / d) ^ ξ := by
  rw [Real.div_rpow hu (le_of_lt hd), ← mul_div_assoc,
    le_div_iff₀ (Real.rpow_pos_of_pos hd ξ)]

/-- A boundary cell can have its marked point outside the closed ball at every positive mesh. -/
theorem three_five_boundary_cell_marked_point (ε : ℝ) (hε : 0 < ε) :
    let η : ℝ → ℂ := fun t => ((1 + t : ℝ) : ℂ)
    (1 : ℤ) ∈ cellVertices ε η (Metric.sphere 0 1) ∧
      vertexPoint ε η 1 ∉ Metric.closedBall 0 1 := by
  dsimp only
  constructor
  · refine ⟨(1 : ℂ), ?_, ?_⟩
    · refine ⟨0, ?_, ?_⟩
      · simp [hε.le]
      · norm_num
    · norm_num [Metric.mem_sphere, dist_zero_right]
  · simp only [vertexPoint, Int.cast_one, mul_one, Metric.mem_closedBall, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith : 0 < 1 + ε)]
    linarith

/-- Closed-ball Hölder data alone do not determine the value at that marked point. -/
theorem three_five_boundary_extensions_differ (ε : ℝ) (hε : 0 < ε) :
    let η : ℝ → ℂ := fun t => ((1 + t : ℝ) : ℂ)
    ∃ f g : ℂ → ℝ,
      IsHolderContinuousOn f (Metric.closedBall 0 1) ∧
      IsHolderContinuousOn g (Metric.closedBall 0 1) ∧
      (∀ x ∈ Metric.closedBall 0 1, f x = g x) ∧
      f (vertexPoint ε η 1) ≠ g (vertexPoint ε η 1) := by
  classical
  dsimp only
  refine ⟨fun _ => 0, fun x => if x ∈ Metric.closedBall 0 1 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, 1, by norm_num, le_rfl, ?_⟩
    intro x hx y hy
    simp
  · refine ⟨0, 1, by norm_num, le_rfl, ?_⟩
    intro x hx y hy
    simp [hx, hy]
  · intro x hx
    simp [hx]
  · have h := (three_five_boundary_cell_marked_point ε hε).2
    change (0 : ℝ) ≠ (if vertexPoint ε (fun t => ((1 + t : ℝ) : ℂ)) 1 ∈
      Metric.closedBall 0 1 then 0 else 1)
    rw [ite_eq_right h]
    norm_num

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
#print axioms five_one_joint_current_aggregates_exit
#print axioms five_one_idla_joint_law
#print axioms five_one_fixed_set_exits
#print axioms three_one_draft_refuted
#print axioms three_seven_latest_reduction
#print axioms three_three_final_reduction
#print axioms three_three_empty_test_set
#print axioms three_three_green_visit_integral_ne_top
#print axioms finite_expectedExitTime
#print axioms five_one_finite_set_exits
#print axioms five_four_green_quotient_semantics
#print axioms three_four_sum_ext
#print axioms three_four_measurable_extension
#print axioms three_two_poly_high_prob_conjunction
#print axioms three_two_bounded_domain_cell_vertices_finite
#print axioms three_two_nonempty_domain_cell_vertices
#print axioms three_two_vertex_supremum_is_maximum
#print axioms three_three_pointwise_bound_iff_supremum
#print axioms three_three_small_tolerances_suffice
#print axioms three_three_vertexOf_is_least
#print axioms three_two_interior_distance_pos
#print axioms three_two_holder_quotient_iff
#print axioms three_five_boundary_cell_marked_point
#print axioms three_five_boundary_extensions_differ
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
#print axioms five_two_positive_surplus_version
#print axioms five_two_probTendsToOne_congr

end MatedCRT.Audit.StatementsSec3Sec5M1
