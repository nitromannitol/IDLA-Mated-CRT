import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.Proofs.Sec5.StoppedLLowerBound

/-!
# Lemma 5.3 on `V^ε(Λ_t)` (E-c1-5): reduction to the stopped surplus lower bound

`StoppedMeanValueInequalityStep` (Proofs/Sec5/IDLALowerBound/Stopped.lean) is the mean value inequality of Lemma 5.3
with the discrete cluster `Λ^ε_t` replaced by the vertex set `A = V^ε(Λ_t)` of the cells meeting the harmonic ball.
The proof of Lemma 5.3 (corrected.tex 2067-2140) splits into the same three parts as in
`MeanValueSurplus` (Proofs/Sec5/MeanValueInequality/SurplusSteps.lean):

* the finite-graph data on `A` (symmetry, local finiteness, finiteness of `A`, first-step equations): on `{t < T}`,
  `Λ_t ⊆ B_{ρ/3}`, so with cells of diameter `≤ ρ/2` one has `A ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)`, a finite set;
* the bound `sup_A q^ε_A ≤ C₁ ε⁻¹` on the normalized exit time: from Lemma 2.18, monotonicity of normalized exit times
  in the domain and Lemma 2.17, with a `σ(h, η)`-measurable `C₁` (`exists_stoppedSurplusFrame`);
* the lower bound `u^ε_t(a) = (t ε⁻¹) g^ε_A(a, 0) - q^ε_A(a) ≥ c ε⁻¹` on `{a ∈ A : dist(η(a), ∂ Ā) > δ}`
  (`StoppedMeanValueSurplusLowerStep`).

Then `(1 + c/C₁) q^ε_A ≤ (t ε⁻¹) g^ε_A(·, 0)` on the `δ`-interior and reversibility of the Green function gives the
stated inequality (`stoppedMeanValueInequality_of_surplusLower`).

The stopped surplus `u^ε_t` is the discrete analogue of `t G_{Λ_t}(0, ·) - ∫_{Λ_t} G_{Λ_t}(·, y) dμ_h(y)`, which equals
the continuum odometer `t G_{B_ρ}(0, ·) + w̄_t` on `Λ_t` (both have Laplacian `μ_h|_{Λ_t} - t δ_0` on `Λ_t` and vanish on
`∂Λ_t`). Its lower bound therefore rests on the strict obstacle gap in the interior of `Λ_t`
(eq:strictly-above-in-interior, `HarmonicBallStrictObstacleGapStep`) and on the convergence of the rescaled Green
function and Green potential of the random domain `V^ε(Λ_t)`; it is not in the paper (E-c1-5).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Step (the stopped surplus lower bound; Lemma 5.3 on `V^ε(Λ_t)`, not in the paper, E-c1-5).** There is a
`σ(h, η)`-measurable `c > 0` such that, on `{t < T}`, with probability tending to one, for `A = V^ε(Λ_t)`,
`c ε⁻¹ + q^ε_A(a) ≤ (t ε⁻¹) g^ε_A(a, 0)` for all `a ∈ A` with `dist(η(a), ∂ Ā) > δ`. The cited results available to
the proof of Lemma 5.3 (Lemmas 4.4 (corrected), 2.13, 3.3, 2.18, Theorem 4.1) and Lemma 3.4 are premises. -/
def StoppedMeanValueSurplusLowerStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        c ω / ε + normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a ≤
          t / ε * greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a 0}

namespace StoppedMeanValue

/-- On `F`, an event `E₁` of probability tending to one and an event `E₂` of probability tending to one give every
event `E ⊇ F ∩ E₁ ∩ E₂` (for small `ε`). -/
theorem tendsToOneOn_of_inter_on {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}
    {E₁ E₂ E : ℝ → Set Ω} (h₁ : TendsToOneOn P F E₁) (h₂ : ProbTendsToOne P E₂)
    (hE : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ∩ E₁ ε ∩ E₂ ε ⊆ E ε) : TendsToOneOn P F E := by
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
        · exact Or.inr fun h2 => hω (hε ⟨⟨hF, h1⟩, h2⟩)
        · exact Or.inl ⟨hF, h1⟩
    _ ≤ _ := measure_union_le _ _

end StoppedMeanValue

/-- **The finite-graph data and the exit-time bound on `V^ε(Λ_t)`**: for a `σ(h, η)`-measurable `C₁ > 0`, with
probability tending to one, on `{t < T}` the finite-graph data hold on `A = V^ε(Λ_t)` and `q^ε_A ≤ C₁ ε⁻¹` on `A`
(Lemma 2.18, monotonicity of normalized exit times, Lemma 2.17). -/
theorem exists_stoppedSurplusFrame {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) {t : ℝ} (ht : 0 < t) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 0 < C ω) ∧
      ProbTendsToOne S.P fun ε => {ω | t < clusterExitTime (Λ ω) ρ →
        FiniteReversibleGreenData (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) ∧
        ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a ≤ C ω / ε} := by
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
  have hmono : ∀ᵐ ω ∂S.P, MonotoneOn (Λ ω) (Ioi 0) := hΛ.mono fun ω h => h.2.1.monotoneOn
  refine MeanValueSurplus.probTendsToOne_of_ae_of_probTendsToOne
    (hreg.and (hS.isAreaParametrized.and (hμ'ae.and (hfin.and hmono))))
    (IterativeBound.probTendsToOne_inter hH₁ hH₂) ?_
  filter_upwards [hεα, self_mem_nhdsWithin] with ε hεα' hε
  have hε : 0 < ε := hε
  rintro ω ⟨hregω, harea, hμeq, hfinω, hmonoω⟩ ⟨hq, hsmall⟩ hT
  have hd := hregω ε hε
  have hB : (ballInterior ε (S.η ω) ρ).Finite := hd.finite_ballInterior
  have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
    IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hmonoω ht hT
  have hAB : cellVertices ε (S.η ω) (Λ ω t) ⊆ ballInterior ε (S.η ω) ρ := by
    intro a ha
    refine StoppedLLowerBound.mem_ballInterior_of_cell_subset ?_
      (StoppedLLowerBound.cell_subset_ball_of_mem_cellVertices harea.1 hΛt (half_pos hρ).le
        (by linarith) hsmall ha)
    obtain ⟨y, hy⟩ := ha
    exact ⟨y, hy.1⟩
  have hA := hB.subset hAB
  have hlf := hd.locallyFinite
  have hfirstA := fun b => greenFn_laplacian_fst hlf hd.succ hA b
  have hfirstB := fun b => greenFn_laplacian_fst hlf hd.succ hB b
  refine ⟨finiteReversibleGreenData_of_consecutive hd.symm hlf hd.succ hA, fun a ha => ?_⟩
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
  calc normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a
      ≤ C₀ * ε⁻¹ * M ω := by rw [hMω]; exact hle
    _ ≤ (C₀ * M ω + 1) / ε := by
      rw [div_eq_mul_inv]
      nlinarith

open StoppedMeanValue in
/-- **Lemma 5.3 on `V^ε(Λ_t)`** (`StoppedMeanValueInequalityStep`, E-c1-5) from the cited inputs of Lemma 5.3,
Lemmas 3.4 and 2.17, `LQGMeasureFieldMeasurableStep` and the stopped surplus lower bound, with `𝔰 = c / C₁`. -/
theorem stoppedMeanValueInequality_of_surplusLower (𝒮 : SpaceFillingSLEModel)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮)
    (hlow : StoppedMeanValueSurplusLowerStep 𝒮) : StoppedMeanValueInequalityStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, hc, hcpos, hlowE⟩ :=
    hlow h44 h213 h41 h33 h218 h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨C, hC, hCpos, hframe⟩ := exists_stoppedSurplusFrame h218 h217 hμ hγ hγ2 hρ hρ1 hS hΛ ht
  refine ⟨fun ω => c ω / C ω, hc.div hC, fun ω => div_pos (hcpos ω) (hCpos ω), ?_⟩
  refine tendsToOneOn_of_inter_on hlowE hframe ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  rintro ω ⟨⟨hT, hlowω⟩, hfr⟩
  obtain ⟨⟨hsymm, hlf, hfinite, hdeg, hfirst⟩, hq⟩ := hfr hT
  intro a ha hdist
  apply meanValue_of_normalized_of_firstStep hsymm hlf hfinite hdeg hfirst a (t / ε) (c ω / C ω)
  have h1 := hlowω a ha hdist
  have h2 := hq a ha
  have hCp := hCpos ω
  have h3 : c ω / C ω * normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a ≤ c ω / ε :=
    calc c ω / C ω * normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a
        ≤ c ω / C ω * (C ω / ε) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (hcpos ω).le hCp.le)
      _ = c ω / ε := by field_simp
  rw [add_mul, one_mul]
  linarith

end MatedCRT
