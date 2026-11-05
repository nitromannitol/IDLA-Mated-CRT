import MatedCRT.Proofs.Sec5.MeanValueInequality.NormalizedStep
import MatedCRT.Proofs.Sec5.MeanValueInequality.GreenReversibility
import MatedCRT.Proofs.Sec5.MeanValueInequality.ExitTimeMonotonicity
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Statements
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.Sec5.LLowerBound.ApplyKernel
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LogPotentialMeasurable
import MatedCRT.Proofs.Measurability.GoodScale
import MatedCRT.Proofs.Sec6.IterativeBound.OfSteps

/-!
# `MeanValueSurplusStep` from the surplus lower bound

The event of `MeanValueSurplusStep` (Lemma 5.3, corrected.tex 2067-2140) splits into
* the finite-graph data (symmetry, local finiteness, `εk ∼ ε(k+1)`, finiteness of `V^ε(B_ρ) \ V^ε(∂B_ρ)`,
  `Λ^ε_t ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)`, `0 ∈ Λ^ε_t`, the first-step equations of the Green's functions and
  `Δ^ε w̃^ε_t = (deg^ε)⁻¹` on `Λ^ε_t`): almost surely, for small `ε`, from Lemma 4.4 (corrected), the regularity of
  the mated-CRT map (`ae_isRegularMatedMap`) and the smallness of cells (`probTendsToOne_small_cells`);
* the bound `sup_{Λ^ε_t} q^ε_{Λ^ε_t} ≤ C₁ ε⁻¹` (line 2137): from Lemma 2.18, the monotonicity of normalized exit
  times and the finiteness of `𝓜(B_{ρ'})` (Lemma 2.17); `C₁` is `σ(h, η)`-measurable through
  `LQGMeasureFieldMeasurableStep`;
* the lower bound `v^ε_t > C ε⁻¹` on `{a ∈ Λ^ε_t : dist(η(a), ∂ cl Λ^ε_t) > δ}` (lines 2128-2134), which is the
  remaining `MeanValueSurplusLowerStep`.
-/

open HarmonicBalls

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MeanValueSurplus

variable {Ω : Type} [MeasurableSpace Ω]

/-- An almost sure property and an event of probability tending to one which together imply `E ε` (for small `ε`)
give `P[(E ε)ᶜ] → 0`. -/
theorem probTendsToOne_of_ae_of_probTendsToOne {P : Measure Ω} {p : Ω → Prop} {H E : ℝ → Set Ω}
    (hp : ∀ᵐ ω ∂P, p ω) (hH : ProbTendsToOne P H)
    (hE : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, p ω → ω ∈ H ε → ω ∈ E ε) : ProbTendsToOne P E := by
  have h0 : P {ω | ¬ p ω} = 0 := ae_iff.1 hp
  unfold ProbTendsToOne at hH ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hH
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hE] with ε hε
  calc P (E ε)ᶜ ≤ P ({ω | ¬ p ω} ∪ (H ε)ᶜ) := by
        apply measure_mono
        intro ω hω
        by_cases h1 : p ω
        · exact Or.inr fun h2 => hω (hε ω h1 h2)
        · exact Or.inl h1
    _ ≤ P {ω | ¬ p ω} + P (H ε)ᶜ := measure_union_le _ _
    _ = P (H ε)ᶜ := by rw [h0, zero_add]

/-- On `F`, an event `E₁` of probability tending to one and an event `E₂` of probability tending to one give every
event `E ⊇ E₁ ∩ E₂` (for small `ε`). -/
theorem tendsToOneOn_of_inter {P : Measure Ω} {F : Set Ω} {E₁ E₂ E : ℝ → Set Ω}
    (h₁ : TendsToOneOn P F E₁) (h₂ : ProbTendsToOne P E₂)
    (hE : ∀ᶠ ε in 𝓝[>] (0 : ℝ), E₁ ε ∩ E₂ ε ⊆ E ε) : TendsToOneOn P F E := by
  unfold TendsToOneOn at h₁ ⊢
  unfold ProbTendsToOne at h₂
  have hsum := h₁.add h₂
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hE] with ε hε
  calc P (F ∩ (E ε)ᶜ) ≤ P ((F ∩ (E₁ ε)ᶜ) ∪ (E₂ ε)ᶜ) := by
        apply measure_mono
        rintro ω ⟨hF, hω⟩
        by_cases h1 : ω ∈ E₁ ε
        · exact Or.inr fun h2 => hω (hε ⟨h1, h2⟩)
        · exact Or.inl ⟨hF, h1⟩
    _ ≤ _ := measure_union_le _ _

end MeanValueSurplus

/-- `ν ↦ 𝓜_ν(B_ρ(0))` is measurable (eq:largest-exit-time-rv, line 884): the supremum over `z ∈ B_ρ(0)` is a
supremum over a dense sequence (`AnnulusEventCountable.iSup_setLIntegral_logKernel_eq_dense`). -/
theorem measurable_largestExitTimeRV_ball_measure (ρ : ℝ) :
    Measurable fun ν : Measure ℂ => largestExitTimeRV ν (ball 0 ρ) := by
  obtain ⟨w, hw⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hrep (ν : Measure ℂ) : largestExitTimeRV ν (ball 0 ρ) =
      ⨆ i : ℕ, ⨆ (_ : w i ∈ ball (0 : ℂ) ρ),
        ∫⁻ u in ball (0 : ℂ) ρ, AnnulusEventCountable.logKernel 1 (w i) u ∂ν := by
    unfold largestExitTimeRV
    have h := AnnulusEventCountable.iSup_setLIntegral_logKernel_eq_dense
      (m := ν) (V := ball 0 ρ) (r := 1) isOpen_ball zero_lt_one hw
    simpa only [AnnulusEventCountable.logKernel, norm_sub_rev] using h
  simp_rw [hrep]
  refine Measurable.iSup fun i => Measurable.iSup fun _ => ?_
  rw [show (fun ν : Measure ℂ => ∫⁻ u in ball (0 : ℂ) ρ,
      AnnulusEventCountable.logKernel 1 (w i) u ∂ν) =
      (fun ν => ∫⁻ u, (ball (0 : ℂ) ρ).indicator
        (AnnulusEventCountable.logKernel 1 (w i)) u ∂ν) by
    funext ν
    exact (lintegral_indicator isOpen_ball.measurableSet _).symm]
  exact Measure.measurable_lintegral
    ((AnnulusEventCountable.measurable_logKernel 1 (w i)).indicator isOpen_ball.measurableSet)

/-- If `η` is continuous with `η(0) = 0` and the cells meeting `B_ρ` have diameter at most `ρ/2`, then
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
theorem zero_mem_ballInterior_of_small_cells {ε ρ : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hη0 : η 0 = 0)
    (hε : 0 ≤ ε) (hρ : 0 < ρ)
    (hsmall : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ ρ / 2) :
    (0 : ℤ) ∈ ballInterior ε η ρ := by
  have h0mem : (0 : ℂ) ∈ cell ε η 0 := by
    unfold cell
    refine ⟨0, ⟨?_, ?_⟩, hη0⟩
    · simp [hε]
    · simp
  have hbdd : Bornology.IsBounded (cell ε η 0) := by
    unfold cell
    exact (isCompact_Icc.image hη).isBounded
  have hV : (0 : ℤ) ∈ cellVertices ε η (ball 0 ρ) := ⟨0, h0mem, mem_ball_self hρ⟩
  have hdiam := hsmall 0 hV
  show (0 : ℤ) ∈ cellVertices ε η (ball 0 ρ) \ cellVertices ε η (frontier (ball 0 ρ))
  refine ⟨hV, ?_⟩
  rintro ⟨z, hz, hzf⟩
  rw [frontier_ball (0 : ℂ) hρ.ne', mem_sphere] at hzf
  have h1 : dist z 0 ≤ diam (cell ε η 0) := dist_le_diam_of_mem hbdd hz h0mem
  linarith

/-- The finite-graph data and the exit-time bound in the event of `MeanValueSurplusStep`. -/
def SurplusFrameEvent (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (ρ t C : ℝ) : Prop :=
  FiniteReversibleGreenData m (matedDiscreteCluster m ε η ρ t) ∧ (∀ a, m a (a + 1) ≠ 0) ∧
  (ballInterior ε η ρ).Finite ∧ matedDiscreteCluster m ε η ρ t ⊆ ballInterior ε η ρ ∧
  (0 : ℤ) ∈ matedDiscreteCluster m ε η ρ t ∧
  (∀ b, ∀ a ∈ ballInterior ε η ρ,
    mLaplacian m (fun x => greenFn m (ballInterior ε η ρ) x b) a = -(if a = b then 1 else 0)) ∧
  (∀ a ∈ matedDiscreteCluster m ε η ρ t,
    mLaplacian m (matedLeastSupersolution m ε η ρ t) a = (mdeg m a : ℝ)⁻¹) ∧
  ∀ a ∈ matedDiscreteCluster m ε η ρ t, normExitTime m (matedDiscreteCluster m ε η ρ t) a ≤ C / ε

/-- **The finite-graph data and the exit-time bound** of the proof of Lemma 5.3 (corrected.tex 2067-2140): for a
`σ(h, η)`-measurable `C₁ > 0`, with probability tending to one, the finite-graph data hold and
`q^ε_{Λ^ε_t} ≤ C₁ ε⁻¹` on `Λ^ε_t` (line 2137, from Lemma 2.18 and Lemma 2.17). -/
theorem exists_surplusFrame {𝒮 : SpaceFillingSLEModel} (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {t : ℝ} (ht : 0 < t) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 0 < C ω) ∧
      ProbTendsToOne S.P fun ε => {ω | SurplusFrameEvent (S.mult ε ω) ε (S.η ω) ρ t (C ω)} := by
  obtain ⟨α, hα, h218α⟩ := h218 γ hγ hγ2
  obtain ⟨C₀, hC₀, h218C⟩ := h218α ρ hρ hρ1
  have hH₁ := IterativeBound.probTendsToOne_of_polyHighProb (h218C Ω S hS)
  have hH₂ := hS.probTendsToOne_small_cells ρ (ρ / 2) (half_pos hρ)
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := by linarith
  obtain ⟨q, -, h217q⟩ := h217 γ hγ hγ2
  have hfin := (h217q ρ' hρ'0 hρ'1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  obtain ⟨μ', hμ'm, hμ'ae⟩ := hμ γ hγ hγ2 Ω S hS
  have hμ'e : Measurable[S.envSigma] μ' :=
    hμ'm.mono (show S.fieldSigma ≤ S.envSigma from le_sup_left) le_rfl
  let M : Ω → ℝ := fun ω => (largestExitTimeRV (μ' ω) (ball 0 ρ')).toReal
  have hMm : Measurable[S.envSigma] M :=
    ((measurable_largestExitTimeRV_ball_measure ρ').comp hμ'e).ennreal_toReal
  refine ⟨fun ω => C₀ * M ω + 1, (hMm.const_mul C₀).add_const 1,
    fun ω => add_pos_of_nonneg_of_pos (mul_nonneg hC₀.le ENNReal.toReal_nonneg) one_pos, ?_⟩
  have hεα : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ α < ρ' - ρ := by
    have h3 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ α)) :=
      ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hα.ne'] at h3
    exact h3.eventually (gt_mem_nhds (by linarith))
  have hreg := ae_isRegularMatedMap (adjacentCellsMeetAeStep 𝒮) hγ hγ2 hS
  refine MeanValueSurplus.probTendsToOne_of_ae_of_probTendsToOne
    (hreg.and (hS.isAreaParametrized.and (hμ'ae.and (hfin.and (h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS)))))
    (IterativeBound.probTendsToOne_inter hH₁ hH₂) ?_
  filter_upwards [hεα, Ioo_mem_nhdsGT ht] with ε hεα' hεt
  rintro ω ⟨hregω, harea, hμeq, hfinω, h44ω⟩ ⟨hq, hsmall⟩
  have hε : 0 < ε := hεt.1
  have hd := hregω ε hε
  obtain ⟨hlap, -, -, h0⟩ := h44ω t ε ht hε
  have hB : (ballInterior ε (S.η ω) ρ).Finite := hd.finite_ballInterior
  have hAB := matedDiscreteCluster_subset_ballInterior (m := S.mult ε ω) (η := S.η ω) (ρ := ρ) hε ht
  have hA := hB.subset hAB
  have hlf := hd.locallyFinite
  have h0B : (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ :=
    zero_mem_ballInterior_of_small_cells harea.1 harea.2.1 hε.le hρ hsmall
  have hfirstA := fun b => greenFn_laplacian_fst hlf hd.succ hA b
  have hfirstB := fun b => greenFn_laplacian_fst hlf hd.succ hB b
  refine ⟨finiteReversibleGreenData_of_consecutive hd.symm hlf hd.succ hA, hd.succ, hB, hAB,
    h0 ((one_lt_div hε).2 hεt.2) h0B, hfirstB, fun a ha => hlap a ha, fun a ha => ?_⟩
  have hMle : largestExitTimeRV (S.μ ω) (ball 0 ρ') ≤
      ⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D :=
    le_iSup₂_of_le (ball 0 ρ') Subset.rfl le_rfl
  have hM : largestExitTimeRV (S.μ ω) (ball 0 ρ') < ⊤ := hMle.trans_lt hfinω
  have hqa := hq.2 (ball 0 ρ) Subset.rfl a (ballInterior_subset_cellVertices_ball (hAB ha))
  have hle := normExitTime_le_of_ambient_bound hε hC₀ hεα' hlf hd.succ hA hB hAB hfirstA hfirstB hM
    (hqa.1.trans hqa.2)
  have hMω : M ω = (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal := by simp only [M, hμeq]
  have hMnn : 0 ≤ M ω := ENNReal.toReal_nonneg
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  calc normExitTime (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) a
      ≤ C₀ * ε⁻¹ * M ω := by rw [hMω]; exact hle
    _ ≤ (C₀ * M ω + 1) / ε := by
      rw [div_eq_mul_inv]
      nlinarith

/-- **Step (the surplus lower bound in the proof of Lemma 5.3, corrected.tex 2128-2134).** There is a
`σ(h, η)`-measurable `C > 0` such that, on `{t < T}`, with probability tending to one,
`v^ε_t(a) = w̃^ε_t(a) + (t ε⁻¹) g^ε_{B_ρ}(0, a) ≥ C ε⁻¹` for all `a ∈ Λ^ε_t` with
`dist(η(a), ∂ cl Λ^ε_t) > δ`. The paper derives it from the uniform convergence of `v̄^ε_t` (Theorem 4.1 and
Lemma 3.3); the cited results of Lemma 5.3 are available as premises. -/
def MeanValueSurplusLowerStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
        c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
          t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}

/-- `MeanValueSurplusStep` from the surplus lower bound, Lemma 2.17 and the `σ(h)`-measurability of `μ_h`. -/
theorem meanValueSurplusStep_of_lower {𝒮 : SpaceFillingSLEModel} (h217 : BoundedExitTimeRVStmt)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hlow : MeanValueSurplusLowerStep 𝒮) :
    MeanValueSurplusStep 𝒮 := by
  intro h44 h213 h41 h33 h218 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, hc, hcpos, hlowE⟩ :=
    hlow h44 h213 h41 h33 h218 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨C, hC, hCpos, hframe⟩ := exists_surplusFrame h44 h218 h217 hμ hγ hγ2 hρ hρ1 hS ht
  refine ⟨c, C, hc, hC, hcpos, hCpos, MeanValueSurplus.tendsToOneOn_of_inter hlowE hframe ?_⟩
  filter_upwards [] with ε
  rintro ω ⟨h1, hfr, hcons, hB, hAB, h0, hfB, hlap, hq⟩
  exact ⟨hfr, hcons, hB, hAB, h0, hfB, hlap, fun a ha => ⟨h1 a ha.1 ha.2, hq a ha.1⟩⟩

/-- **Lemma 5.3** from its cited inputs (Lemmas 4.4 (corrected), 2.13, 3.3, 2.18, Theorem 4.1), Lemma 2.17,
`LQGMeasureFieldMeasurableStep` and the surplus lower bound `MeanValueSurplusLowerStep`. -/
theorem meanValueInequality_of_lower (𝒮 : SpaceFillingSLEModel)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hlow : MeanValueSurplusLowerStep 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  meanValueInequality_of_surplus 𝒮 h44 h213 h41 h33 h218 (meanValueSurplusStep_of_lower h217 hμ hlow)

end MatedCRT
