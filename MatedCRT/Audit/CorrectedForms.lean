import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec4.ObstacleSpecialization
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Steps.Sec6.ConstantOrderLowerBound
import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv
import MatedCRT.Steps.Sec6.ChanceOfBeingAbsorbed
import MatedCRT.Steps.Sec6.IterativeBound
import MatedCRT.Steps.Sec7.MassBoundOdometer
import MatedCRT.Steps.Sec7.CrudeUpperBound
import MatedCRT.Proofs.Sec6.AbelianIDLA.Statement
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Audit: corrected and relaxed forms versus the Draft statements

For every numbered result which a worker proved (or reduced) in a corrected or relaxed form instead of its Draft
statement, this file records the logical relation between the two forms as Lean facts, so that the operator can rule
with them in hand. The table, the escalations and the authors are in `docs/campaign/CORRECTED-FORMS.md`.

* `corrected ⇒ Draft`: 5.2 (`GeneralIDLALowerBoundRelaxedStep`), 6.3 (`AbelianIDLAAnyStartStep`, proved).
* `Draft ⇒ corrected`: 3.2, 4.4, 4.5, 6.7 (b), 6.8 (b), 6.9 (local rate and (b)), 7.2 (above scale).
* neither: 3.1 (`D` open and polynomially summable scales weaken it; the `ε⁻¹`-scaled Hölder data (N1) strengthen
  it). Both forms imply their common part `DiscretePotentialTightnessOnOpenStmt`.
* False as drafted, proved here: Lemmas 4.4 and 4.5 (ESCALATIONS E-c1-1). Each forces `μ_h(B_ρ) = ∞` almost surely
  (`discreteLaplacianBound_ae_measure_ball_eq_top`, `discreteConservationOfMass_ae_measure_ball_eq_top`), which
  contradicts the local finiteness of the LQG measure (Fact 2.2 I, `LQGMeasurePropertiesStmt`), for any valid
  environment (`not_discreteLaplacianBoundStmt`, `not_discreteConservationOfMassStmt`).
* Rerouting: Lemmas 7.2 (above scale), 7.3 and 7.4 use only the first conjunct of Lemma 4.4, which the corrected form
  keeps; `massBoundOdometerAboveScale_of_corrected`, `odometerBoundMass_of_corrected` and
  `crudeUpperBound_of_corrected` derive them from `DiscreteLaplacianBoundCorrectedStmt` in place of the false Draft
  4.4.
-/

namespace MatedCRT.Audit.CorrectedForms

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

variable {𝒮 : SpaceFillingSLEModel}

/-- Polynomially high probability is preserved by enlarging the events for `ε ∈ (0, 1)`. -/
theorem polyHighProb_mono_lt_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (h : PolyHighProb P E) (hEF : ∀ ε, 0 < ε → ε < 1 → E ε ⊆ F ε) : PolyHighProb P F := by
  unfold PolyHighProb at h ⊢
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := h
  refine ⟨p, hp, C, min r₀ 1, lt_min hr₀ one_pos, fun r hr hrr => ?_⟩
  exact (measure_mono (compl_subset_compl.2 (hEF r hr (hrr.trans_le (min_le_right _ _))))).trans
    (h r hr (hrr.trans_le (min_le_left _ _)))

/-! ## Lemma 3.1: neither form implies the other; both imply their common part -/

/-- **Lemma 3.1, common part** of `DiscretePotentialTightnessStmt` (Draft) and `DiscretePotentialTightnessCorrectedStmt`
(c1): the hypotheses of the corrected form (`D` open, scales in a polynomially summable deterministic sequence `e`)
with the conclusion of the Draft form (unscaled Hölder data `C' (ε ∨ |η(a) - η(b)|)^χ` in the "moreover" part). -/
def DiscretePotentialTightnessOnOpenStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
  ∀ e : ℕ → ℝ, IsPolySummableScales e →
  ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ ω n, E ω n ∈ range e) →
    (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
    (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) →
    Measurable[S.envSigma] C → (∀ ω, 0 < C ω) →
    (∀ ω n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
      |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) →
    (∀ ω n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |u ω n a| ≤ C ω / E ω n) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop O) ∧
      ((SimplyConnectedSpace D ∧
          (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D, matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
          ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n, E ω n < 1 →
            ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
              |u ω n a - u ω n b| ≤
                C' * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ) →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop (closure D))

/-- The Draft Lemma 3.1 implies the common part (it has fewer hypotheses). -/
theorem discretePotentialTightnessOnOpen_of_draft (h : DiscretePotentialTightnessStmt 𝒮) :
    DiscretePotentialTightnessOnOpenStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS D hDρ _ hDc e he E u C hEm hEe hE0 hu hCm hCpos hlap hbd
  refine h γ hγ hγ2 ρ hρ hρ1 Ω S hS D hDρ hDc E u C hEm (fun ω n => ?_) hE0 hu hCm hCpos hlap hbd
  obtain ⟨j, hj⟩ := hEe ω n
  rw [← hj]
  exact he.1 j

/-- The corrected Lemma 3.1 implies the common part: for `ε < 1` the unscaled Hölder data `C' (ε ∨ |·|)^χ` are
`ε⁻¹`-scaled data `C' ε⁻¹ (ε ∨ |·|)^χ` (N1 strengthens the "moreover" part). -/
theorem discretePotentialTightnessOnOpen_of_corrected (h : DiscretePotentialTightnessCorrectedStmt 𝒮) :
    DiscretePotentialTightnessOnOpenStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS D hDρ hDo hDc e he E u C hEm hEe hE0 hu hCm hCpos hlap hbd
  obtain ⟨Φ, hΦ, h⟩ := h γ hγ hγ2 ρ hρ hρ1 Ω S hS D hDρ hDo hDc e he E u C hEm hEe hE0 hu hCm hCpos hlap hbd
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [h] with ω hω
  obtain ⟨hmono, ubar, hcont, hO, hmore⟩ := hω
  refine ⟨hmono, ubar, hcont, hO, fun ⟨hsc, hharm, χ, C', hχ, hχ1, hC', hhol⟩ => hmore ⟨hsc, hharm, χ, C', hχ,
    hχ1, hC', fun n hn a ha b hb => ?_⟩⟩
  have hEpos : 0 < E ω n := by
    obtain ⟨j, hj⟩ := hEe ω n
    rw [← hj]
    exact he.1 j
  refine (hhol n hn a ha b hb).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact le_div_self hC'.le hEpos hn.le
  · exact Real.rpow_nonneg (le_max_of_le_left hEpos.le) χ

/-! ## Lemma 3.2: adopted corrected statement -/

/-- The adopted Draft statement implies the corrected step, whose exponent may also depend on `C'`. -/
theorem discreteHolderContinuityCorrected_of_draft (h : DiscreteHolderContinuityStmt 𝒮) :
    DiscreteHolderContinuityCorrectedStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1
  obtain ⟨ξ, A, β, hξ, hξ1, hA, hβ, hβ1, h⟩ := h γ hγ hγ2 ρ hρ hρ1
  refine ⟨ξ, A, β, hξ, hξ1, hA, hβ, hβ1, ?_⟩
  intro χ C' hχ hχ1 hC'
  obtain ⟨ξ', hξ', hξ'1, _, h⟩ := h χ hχ hχ1
  obtain ⟨C, hC, h⟩ := h C' hC'
  exact ⟨ξ', C, hξ', hξ'1, hC, h⟩

/-! ## Lemmas 4.4 and 4.5: Draft ⇒ corrected; the Draft forms are false (E-c1-1) -/

/-- The Draft Lemma 4.4 implies its corrected form (the corrected origin claim has one more hypothesis). -/
theorem discreteLaplacianBoundCorrected_of_draft (h : DiscreteLaplacianBoundStmt 𝒮) :
    DiscreteLaplacianBoundCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [h γ hγ hγ2 ρ hρ hρ1 Ω S hS] with ω hω t ε ht hε
  obtain ⟨h1, h2, h3, h4⟩ := hω t ε ht hε
  exact ⟨h1, h2, h3, fun h5 _ => h4 h5⟩

/-- The Draft Lemma 4.5 implies its corrected form (the corrected mass identity has one more hypothesis). -/
theorem discreteConservationOfMassCorrected_of_draft (h : DiscreteConservationOfMassStmt 𝒮) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [h γ hγ hγ2 ρ hρ hρ1 Ω S hS] with ω hω t ε ht hε
  obtain ⟨h1, h2, h3⟩ := hω t ε ht hε
  exact ⟨h1, h2, fun _ h5 => h3 h5⟩

/-- If `μ(B_ρ) < ε`, the origin is not in `V^ε(B_ρ) \ V^ε(∂B_ρ)`: its cell `η([-ε, 0])` has `μ`-mass `ε` and would lie
in `B_ρ`. -/
theorem origin_not_mem_ballInterior {μ : Measure ℂ} {η : ℝ → ℂ} (hA : IsAreaParametrized μ η) {ε ρ : ℝ}
    (hε : 0 < ε) (hlt : μ (ball 0 ρ) < ENNReal.ofReal ε) : (0 : ℤ) ∉ ballInterior ε η ρ := by
  intro hin
  have hsub : cell ε η 0 ⊆ ball 0 ρ := fun z hz => mem_ball_of_mem_cell hA.1 hin hz
  have hmass : μ (cell ε η 0) = ENNReal.ofReal ε := by
    have hlt' : ε * (((0 : ℤ) : ℝ) - 1) < ε * ((0 : ℤ) : ℝ) := by push_cast; linarith
    rw [cell, hA.2.2.2 _ _ hlt']
    congr 1
    push_cast
    ring
  exact absurd (hmass ▸ measure_mono hsub) (not_le.2 hlt)

/-- An `ε > 0` above the `μ`-mass of `B_ρ`, if it is finite. -/
theorem exists_measure_ball_lt {μ : Measure ℂ} {ρ : ℝ} (hfin : μ (ball 0 ρ) ≠ ∞) :
    ∃ ε : ℝ, 0 < ε ∧ μ (ball 0 ρ) < ENNReal.ofReal ε := by
  refine ⟨(μ (ball 0 ρ)).toReal + 1, by positivity, ?_⟩
  calc μ (ball 0 ρ) = ENNReal.ofReal (μ (ball 0 ρ)).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ < ENNReal.ofReal ((μ (ball 0 ρ)).toReal + 1) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)

/-- **The Draft Lemma 4.4 forces `μ_h(B_ρ) = ∞` almost surely.** If `μ_h(B_ρ) < ε`, then `0 ∉ V^ε(B_ρ) \ V^ε(∂B_ρ)`,
so `Λ^ε_t = ∅` (`matedDiscreteCluster_eq_empty`), while the Draft asks `0 ∈ Λ^ε_t` for `t = 2ε`. -/
theorem discreteLaplacianBound_ae_measure_ball_eq_top (h : DiscreteLaplacianBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, S.μ ω (ball 0 ρ) = ∞ := by
  filter_upwards [h γ hγ hγ2 ρ hρ hρ1 Ω S hS, hS.isAreaParametrized] with ω hω hA
  by_contra hfin
  obtain ⟨ε, hε, hlt⟩ := exists_measure_ball_lt hfin
  have hin := origin_not_mem_ballInterior hA hε hlt
  have h0 := (hω (2 * ε) ε (by positivity) hε).2.2.2 (by rw [mul_div_assoc, div_self hε.ne']; norm_num)
  rw [matedDiscreteCluster_eq_empty hin] at h0
  exact h0

/-- **The Draft Lemma 4.5 forces `μ_h(B_ρ) = ∞` almost surely.** If `μ_h(B_ρ) < ε`, then `0 ∉ V^ε(B_ρ) \ V^ε(∂B_ρ)`,
`Λ^ε_ε = ∅` and `Δ^ε w̃^ε_ε = 0` on `V^ε(B_ρ) \ V^ε(∂B_ρ)` (adjacent cells meet, `adjacentCellsMeetAeStep`), so the
Draft mass identity reads `0 = ε / ε`. -/
theorem discreteConservationOfMass_ae_measure_ball_eq_top (h : DiscreteConservationOfMassStmt 𝒮) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, S.μ ω (ball 0 ρ) = ∞ := by
  filter_upwards [h γ hγ hγ2 ρ hρ hρ1 Ω S hS, hS.isAreaParametrized,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hω hA hcell
  by_contra hfin
  obtain ⟨ε, hε, hlt⟩ := exists_measure_ball_lt hfin
  have hin := origin_not_mem_ballInterior hA hε hlt
  have hsum := (hω ε ε hε hε).2.2 (by rw [matedDiscreteCluster_eq_empty hin]; exact empty_subset _)
  have key : ∀ x : ballInterior ε (S.η ω) ρ,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ ε) x = 0 :=
    fun x => matedLaplacian_eq_zero_of_origin_not_mem hA.1 (hcell ε hε) hin x.2
  simp only [key, zero_mul, tsum_zero] at hsum
  rw [div_self hε.ne'] at hsum
  exact zero_ne_one hsum

/-- **The Draft Lemma 4.4 is false** for every valid environment whose LQG measure is almost surely locally finite
(Fact 2.2 I, `LQGMeasurePropertiesStmt`). -/
theorem not_discreteLaplacianBoundStmt {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hlf : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω)) :
    ¬ DiscreteLaplacianBoundStmt 𝒮 := by
  intro h
  have := hS.isProbabilityMeasure
  obtain ⟨ω, hω, hlfω⟩ := ((discreteLaplacianBound_ae_measure_ball_eq_top h hγ hγ2 (ρ := 1 / 2) (by norm_num)
    (by norm_num) hS).and hlf).exists
  have := hlfω
  exact measure_ball_lt_top.ne hω

/-- **The Draft Lemma 4.5 is false** for every valid environment whose LQG measure is almost surely locally finite
(Fact 2.2 I, `LQGMeasurePropertiesStmt`). -/
theorem not_discreteConservationOfMassStmt {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hlf : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω)) :
    ¬ DiscreteConservationOfMassStmt 𝒮 := by
  intro h
  have := hS.isProbabilityMeasure
  obtain ⟨ω, hω, hlfω⟩ := ((discreteConservationOfMass_ae_measure_ball_eq_top h hγ hγ2 (ρ := 1 / 2)
    (by norm_num) (by norm_num) hS).and hlf).exists
  have := hlfω
  exact measure_ball_lt_top.ne hω

/-! ## Lemmas 7.2-7.4 from the corrected Lemma 4.4 (only its first conjunct is used) -/

/-- `StoppedOdometerLaplacianStep` (eq:laplacian-of-uteps away from the origin) from the **corrected** Lemma 4.4: the
proof of `stoppedOdometerLaplacianStep_of_steps` (MatedCRT/Steps/Sec7/OdometerBoundMass.lean, c3) uses only the
first conjunct, `Δ^ε w̃^ε_t = (deg^ε)⁻¹` on `Λ^ε_t`, which the corrected form keeps verbatim. -/
theorem stoppedOdometerLaplacianStep_of_corrected (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : StoppedOdometerLaplacianStep 𝒮 := by
  have hstr := matedMapStructureStep_of_adjacentCellsMeet 𝒮 hcell
  have hgreen := greenKernelHarmonicStep_of_steps 𝒮 hstr
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hstr γ hγ hγ2 Ω S hS, h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS, hgreen γ hγ hγ2 ρ hρ hρ1 Ω S hS]
    with ω hω h4 hg
  intro ε t hε ht a ha ha0
  obtain ⟨hlf, -⟩ := hω ε hε
  have haΛ : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧
      matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a < matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a := ha
  have haV : a ∈ ballInterior ε (S.η ω) ρ := by
    by_contra hV
    have haW : a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ) := Sec7.cellVertices_mono ball_subset_closedBall haΛ.1
    have h1 := Sec7.matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior (m := S.mult ε ω) hε ht haW hV
    linarith [haΛ.2]
  have hw : mLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a =
      ((mdeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹ := (h4 t ε ht hε).1 a ha
  have hgr : mLaplacian (S.mult ε ω) (greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0) a =
      0 := hg ε hε a haV ha0
  show mLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a = ((mdeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹
  rw [Sec7.mLaplacian_stoppedOdometer hε ht hlf, hw, hgr, mul_zero, add_zero]

/-- **Lemma 7.2 (corrected, E-c3-2)** from Lemmas 2.16, 2.8 and the **corrected** Lemma 4.4 (in place of the false
Draft 4.4 of `massBoundOdometerAboveScale_of_draft`). -/
theorem massBoundOdometerAboveScale_of_corrected (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 :=
  massBoundOdometerAboveScale_of_inputs 𝒮 h216 h28
    (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮)) (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 7.3** from the **corrected** Lemma 4.4 (in place of the false Draft 4.4 of `odometerBoundMass_of_draft`). -/
theorem odometerBoundMass_of_corrected (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) : OdometerBoundMassStmt 𝒮 :=
  odometerBoundMass_of_steps 𝒮 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮))

/-- **Lemma 7.4** (Draft, the Λ-version of review-S (S4), E-c3-1) from the **corrected** Lemma 4.4 and the degree
bound (GMS19 Lemma 2.6), in place of the false Draft 4.4 of `crudeUpperBound_of_draft`. -/
theorem crudeUpperBound_of_corrected (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (hdeg : DegreeBoundInput 𝒮) :
    CrudeUpperBoundStmt 𝒮 :=
  crudeUpperBound_of_mapSteps 𝒮 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮)) hdeg

/-! ## Lemma 5.2: relaxed ⇒ Draft (c2) -/

example (h : GeneralIDLALowerBoundRelaxedStep 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_relaxed 𝒮 h

/-! ## Lemma 6.3: any start ⇒ Draft; both proved (c5) -/

example : AbelianIDLAAnyStartStep 𝒮 := AbelianIDLA.abelianIDLAAnyStartStep 𝒮

example (h : AbelianIDLAAnyStartStep 𝒮) : AbelianIDLAStmt 𝒮 := h.abelianIDLA

example : AbelianIDLAStmt 𝒮 := AbelianIDLA.abelianIDLA 𝒮

/-! ## Lemmas 6.7-6.9: Draft ⇒ route (b) of E-A10; Lemma 6.9: Draft ⇒ local rate (E-c5-1) ⇒ route (b) -/

example (h : ConstantOrderLowerBoundStmt 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 := h.logLoss

/-- The Draft Lemma 6.8 implies its route (b) form (the bound `1 - s₂` only increases to `1 - s₂ (1 + |log r|)⁻²`).
Same statement as `Sec7.constantOrderLowerBoundDivLog_of_fixed` (x2, Proofs/Sec7/DivSandpileUpperBound/LogSurvival
.lean), restated here without its import of Proofs/Sec6/ConstantOrderLowerBound/OfSteps. -/
theorem constantOrderLowerBoundDivLog_of_draft (h : ConstantOrderLowerBoundDivStmt 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβm
  obtain ⟨ω₀, hω₀, h⟩ := h γ hγ hγ2 ρ hρ hρ1 βm hβm
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, h⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hE⟩ := h Ω S hS
  refine ⟨dd, hdd, hddpos, hE.mono' fun ε ω hω => ?_⟩
  intro r hr1 hr2 Θ hΘ1 hΘ2 A hA hcount a ha
  have hL : 1 ≤ (1 + |Real.log r|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  exact (hω r hr1 hr2 Θ hΘ1 hΘ2 A hA hcount a ha).trans
    (ENNReal.ofReal_le_ofReal (by linarith [div_le_self hs₂.le hL]))

example (h : ChanceOfBeingAbsorbedStmt 𝒮) : ChanceOfBeingAbsorbedLocalRateStmt 𝒮 := h.localRate

example (h : ChanceOfBeingAbsorbedLocalRateStmt 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := h.logLoss

example (h : ChanceOfBeingAbsorbedStmt 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := h.logLoss

/-! ## Lemma 7.2: Draft ⇒ above scale (E-c3-2); the Draft is false (argument in E-c3-2) -/

/-- The Draft Lemma 7.2 implies its corrected form (`β = 1`; the corrected conclusion is asked only for `s ≥ ε^β`). -/
theorem massBoundOdometerAboveScale_of_massBoundOdometer (h : MassBoundOdometerStmt 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1
  obtain ⟨C, c₀, hC, hc₀, hc₀1, h⟩ := h γ hγ hγ2 ρ hρ hρ1
  refine ⟨C, c₀, 1, hC, hc₀, hc₀1, one_pos, fun Ω _ S hS => ?_⟩
  refine polyHighProb_mono_lt_one (h Ω S hS) fun ε _ _ ω hω => ?_
  intro t ht Θ hΘ hΘc hΘ0 s z hs _ hsub
  exact hω t ht Θ hΘ hΘc hΘ0 s z hs hsub

end MatedCRT.Audit.CorrectedForms
