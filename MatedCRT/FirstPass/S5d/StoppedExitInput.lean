import MatedCRT.FirstPass.S5d.StoppedPathwise
import MatedCRT.FirstPass.S5d.RandomLevel
import MatedCRT.Proofs.Sec5.StoppedMeanValueInequality
import MatedCRT.Proofs.Sec5.MeanValueInequality.ExitTimeMonotonicity
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Measurability.GoodScale
import MatedCRT.Draft.Section2

/-!
# The exit-sum input (E) of the stopped clause

Proves the exit bound `∑_{b ∈ I^ε_t} g_{I}(a, b) ≤ C(ω) / ε` on the targets `a ∈ Z^ε_t` (the third conjunct of
`StoppedFirstGreenInputsStep`, referee/paper: `q^ε_{I_ε}(a) ≤ C ε⁻¹` with a finite positive random `C`, paper
Proposition 5.1 proof, [C21]), from:
* the killing set is contained in the cluster: `I^ε_t ⊆ V^ε(Λ_t)` (definition of `stoppedKillSet`), and both are finite
  (`StoppedPathwiseInputs`);
* the exit-time domain monotonicity `normExitTime_mono_of_firstStep` (ExitTimeMonotonicity.lean:18), with the first-step
  equations from `WalkPotential.mLaplacian_greenFn` (GreenFirstStep.lean:210);
* the random constant of the stopped mean value inequality `exists_stoppedSurplusFrame` (Proofs/Sec5/StoppedMeanValueInequality.lean:81),
  which is `Measurable[envSigma]` (measurability of `ν ↦ 𝓜_ν(B_ρ)`, SurplusSteps.lean:81), hence no measurability gap for `C`.
The bound holds on `{t < T}` with probability tending to one (`TendsToOneOn`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Domain monotonicity of the normalized exit time for finite domains `A ⊆ B` (Lawler-Limic, killed walk): the
normalized exit time killed on the smaller finite set is at most the one killed on the larger finite set. -/
theorem normExitTime_killing_le {m : ℤ → ℤ → ℕ} {A B : Set ℤ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (a : ℤ) :
    normExitTime m A a ≤ normExitTime m B a :=
  normExitTime_mono_of_firstStep hlf hcons hA hB hAB
    (fun b => WalkPotential.mLaplacian_greenFn hlf hcons hA b)
    (fun b => WalkPotential.mLaplacian_greenFn hlf hcons hB b) a

/-- A null exceptional set absorbs the failure of an inclusion: `μ (F ∩ Gᶜ) ≤ μ Eᶜ` whenever `F ∩ Gᶜ ⊆ Eᶜ ∪ N`
and `μ N = 0`. -/
theorem measure_le_of_inclusion {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {F G E N : Set Ω}
    (hN : μ N = 0) (h : F ∩ Gᶜ ⊆ Eᶜ ∪ N) : μ (F ∩ Gᶜ) ≤ μ Eᶜ := by
  refine (measure_mono h).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [hN, add_zero]

/-- **The exit-sum input (E) of the stopped clause.** For `δ ∈ (0, ρ)` and `t > 0` there is a measurable random constant
`C > 0` such that, on `{t < T}`, with probability tending to one as `ε → 0⁺`, every target `a ∈ Z^ε_t` satisfies
`∑_{b ∈ I^ε_t} g_{I}(a, b) ≤ C / ε` (`g_I` the degree-normalized Green kernel of the killed walk on `I^ε_t`). -/
theorem stoppedExit_input (𝒮 : SpaceFillingSLEModel) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (_hδ : 0 < δ) (_hδρ : δ < ρ) (ht : 0 < t) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 0 < C ω) ∧
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω | ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
        ∑' b : stoppedKillSet S Λ ρ t ε ω,
          greenKernel (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a b ≤ C ω / ε} := by
  obtain ⟨C, hCm, hCpos, hframe⟩ := exists_stoppedSurplusFrame h218 h217 hμ hγ hγ2 hρ hρ1 hS hΛ ht
  have hpw := stoppedPathwiseInputs_ae 𝒮 hcell hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  have hmon : ∀ᵐ ω ∂S.P, MonotoneOn (Λ ω) (Ioi 0) := hΛ.mono fun ω h => h.2.1.monotoneOn
  have hall := hmon.and hpw
  refine ⟨C, hCm, hCpos, ?_⟩
  set N : Set Ω := {ω | ¬ (MonotoneOn (Λ ω) (Ioi 0) ∧ ∀ ε : ℝ, 0 < ε → StoppedPathwiseInputs S Λ ρ t ε ω)} with hNdef
  have hN : S.P N = 0 := ae_iff.1 hall
  unfold TendsToOneOn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hframe ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    refine measure_le_of_inclusion hN ?_
    intro ω hω
    · obtain ⟨hF, hG⟩ := hω
      rw [Set.mem_compl_iff] at hG
      by_cases hNω : ω ∈ N
      · exact Or.inr hNω
      · left
        rw [Set.mem_compl_iff]
        intro hE
        apply hG
        rw [Set.mem_ofPred_eq]
        simp only [hNdef, Set.mem_ofPred_eq, not_not] at hNω
        obtain ⟨hmono, hPI⟩ := hNω
        obtain ⟨hsymm, hlf, hcons, hB, hBfin, hcl, h0⟩ := hPI ε hε0
        have hT : t < clusterExitTime (Λ ω) ρ := hF
        have hΛball : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime_cover hρ hmono ht hT
        have hVfin : (cellVertices ε (S.η ω) (Λ ω t)).Finite :=
          hBfin.subset (cellVertices_mono_set hΛball)
        have hI : (stoppedKillSet S Λ ρ t ε ω).Finite :=
          hBfin.subset fun a ha => mem_cellVertices_ball_of_mem_matedDiscreteCluster ha.2.1
        have hIV : stoppedKillSet S Λ ρ t ε ω ⊆ cellVertices ε (S.η ω) (Λ ω t) := fun a ha => ha.2.2
        rw [Set.mem_ofPred_eq] at hE
        obtain ⟨-, hQ⟩ := hE hF
        intro a ha
        have haV : a ∈ cellVertices ε (S.η ω) (Λ ω t) :=
          cellVertices_mono_set (fun _ hy => hy.1) (show a ∈ cellVertices ε (S.η ω) (innerNbhd δ (Λ ω t)) from ha)
        calc ∑' b : stoppedKillSet S Λ ρ t ε ω,
              greenKernel (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a b
            = normExitTime (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a := rfl
          _ ≤ normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a :=
            normExitTime_killing_le hlf hcons hI hVfin hIV a
          _ ≤ C ω / ε := hQ a haV

/-- Intersections of two events that hold on `{t < T}` with probability tending to one. -/
theorem tendsToOneOn_inter {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {E₁ E₂ : ℝ → Set Ω}
    (h₁ : TendsToOneOn P F E₁) (h₂ : TendsToOneOn P F E₂) : TendsToOneOn P F fun ε => E₁ ε ∩ E₂ ε := by
  unfold TendsToOneOn at h₁ h₂ ⊢
  have hsum := h₁.add h₂
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · refine Filter.Eventually.of_forall fun ε => ?_
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    rintro ω ⟨hF, hn⟩
    have hn' : ¬ (ω ∈ E₁ ε ∧ ω ∈ E₂ ε) := hn
    by_cases h1 : ω ∈ E₁ ε
    · right
      exact ⟨hF, fun h2 => hn' ⟨h1, h2⟩⟩
    · left
      exact ⟨hF, h1⟩

/-- **The surplus floor of the stopped clause (named hypothesis, see docs/campaign/COUNTED.md; paper Proposition 5.1 proof, [C21], corrected tex 2362-2363).** For
`δ ∈ (0, ρ)` and `t > 0` there is a measurable random constant `c > 0` such that, on `{t < T}`, with probability tending to one as
`ε → 0⁺`, the surplus floor `c/ε ≤ u^ε(a)` holds for every target `a ∈ Z^ε_t = V^ε(B⁻_δ(Λ_t))` (`stoppedTargetSet`). The written
source: the strict-gap argument of Proposition 4.2 ([C20], tex 1912-1960) with the convergence of Theorem `convergence-divisible`
and Lemmas `uniform-convergence-of-greens-function`, `cell-size-estimate`, giving `u^ε(a) ≥ c ε⁻¹` for every cell meeting
`B⁻_{δ/2}(Λ_t)` off an event of vanishing probability (tex 2362). The rescaled convergence is a separate input (see docs/campaign/COUNTED.md). -/
def StoppedFloorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ stoppedTargetSet S Λ δ t ε ω, c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a}

/-- **The surplus maximum outside the killing set (named hypothesis, see docs/campaign/COUNTED.md; paper Proposition 5.1 proof, [C21], corrected tex 2364).** With
`M^ε = sup_{a ∉ I^ε_t} u^ε(a)`, for every `κ > 0` the event `M^ε ≤ κ/(2ε)` (i.e. `ε M^ε ≤ κ/2`) holds on `{t < T}` with
probability tending to one as `ε → 0⁺`: the written statement is `ε M^ε → 0` in probability on `{t < T}`. -/
def StoppedMaxOutsideStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ κ : ℝ, 0 < κ →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ b ∉ stoppedKillSet S Λ ρ t ε ω, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤ κ / (2 * ε)}

/-- **The floor and ceiling input of the stopped clause (paper Proposition 5.1 proof, [C21]).** For `δ ∈ (0, ρ)` and `t > 0`
there is a measurable random constant `c > 0` such that, on `{t < T}`, with probability tending to one as `ε → 0⁺`: the surplus
floor `c/ε ≤ u^ε(a)` on the targets `Z^ε_t` (`stoppedTargetSet`) and the ceiling `u^ε(b) ≤ c/(2ε)` off the killing set `I^ε_t`
(`stoppedKillSet`). It is DERIVED from the floor `StoppedFloorStep` and the maximum `StoppedMaxOutsideStep`
(`stoppedFloorCeiling_of_floor_max`), so it is not a separate input. -/
def StoppedFloorCeilingStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      (∀ a ∈ stoppedTargetSet S Λ δ t ε ω, c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ∧
      (∀ b ∉ stoppedKillSet S Λ ρ t ε ω, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤ c ω / (2 * ε))}

/-- **The ceiling from the surplus maximum.** `StoppedFloorCeilingStep` follows from the floor `StoppedFloorStep` and the
open maximum `StoppedMaxOutsideStep`: the constant `c` of the floor serves for the ceiling, by `tendsToOneOn_randomLevel`
(`S5d/RandomLevel.lean`) for the level `x ↦ ∀ b ∉ I^ε_t, u^ε(b) ≤ x`, which is monotone in `x`. -/
theorem stoppedFloorCeiling_of_floor_max (𝒮 : SpaceFillingSLEModel) (hfl : StoppedFloorStep 𝒮)
    (hmax : StoppedMaxOutsideStep 𝒮) : StoppedFloorCeilingStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, hcm, hcpos, hF⟩ := hfl γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨c, hcm, hcpos, ?_⟩
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hC := tendsToOneOn_randomLevel (P := S.P) (F := {ω | t < clusterExitTime (Λ ω) ρ}) (c := c) hcpos
    (fun κ _ => hS.nullMeasurableSet_of_envSigma (measurableSet_lt hcm measurable_const))
    (Lv := fun ε x ω => ∀ b ∉ stoppedKillSet S Λ ρ t ε ω, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤ x)
    (fun _ _ _ _ hxy h b hb => (h b hb).trans hxy)
    (fun κ hκ => hmax γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht κ hκ)
  have h := tendsToOneOn_inter hF hC
  simpa only [TendsToOneOn, Set.ofPred_and] using h

/-- **The stopped first Green input from the floor and the maximum.** `StoppedFirstGreenInputsStep` follows from the
floor `StoppedFloorStep` and the maximum `StoppedMaxOutsideStep` (through `stoppedFloorCeiling_of_floor_max`), together
with the proved exit input `stoppedExit_input`: the random constants are `c` from the floor and `C` from the exit bound. -/
theorem stoppedFirstGreenInputsStep_of_floorCeiling (𝒮 : SpaceFillingSLEModel) (hfl : StoppedFloorStep 𝒮)
    (hmax : StoppedMaxOutsideStep 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮) : StoppedFirstGreenInputsStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, hcm, hcpos, hFC⟩ :=
    stoppedFloorCeiling_of_floor_max 𝒮 hfl hmax γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨C, hCm, hCpos, hE⟩ := stoppedExit_input 𝒮 h218 h217 hμ hcell hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨c, C, hcm, hCm, hcpos, hCpos, ?_⟩
  have h := tendsToOneOn_inter hFC hE
  simpa only [← Set.ofPred_and, and_assoc] using h

end MatedCRT
