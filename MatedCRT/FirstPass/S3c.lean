import MatedCRT.FirstPass.S3c.CommonSelection
import MatedCRT.FirstPass.S3c.Thinning
import MatedCRT.FirstPass.S3c.PointwiseSelection
import MatedCRT.FirstPass.S3c.CountableFamilies
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# First pass, result 3.1 (IDLA Lemma 3.1, lemma:discrete-potential-tightness), faithful corrected form (q4)

Task fp-S3c-3-1-faithful. The Draft form `DiscretePotentialTightnessCorrectedStmt`
(MatedCRT/Steps/Sec3/DiscretePotentialTightness.lean) places the domain `D` and the random data before the almost-sure
quantifier. ChatGPT's fidelity check (notes/fp-gaps/CHATGPT-fidelity-corrected-2.md) found this TOO WEAK for [C11].
`DiscretePotentialTightnessFaithfulStmt` below puts the deterministic thinning and one probability-one event first.

`MatedCRT.S3c.firstPass_3_1_corrected` proves it from the same inputs as `MatedCRT.firstPass_3_1_corrected`
(FirstPass/S3S4.lean), with no new external input:
* the proof is `tightness_selection_common` (FirstPass/S3c/CommonSelection.lean), i.e. the existing argument of
  `tightnessSelectionStep_of_meps` and `tightnessEquicontinuityStep_of_steps` with the almost-sure event moved in front of
  the domain and the data (the events used there do not mention `D`, `E`, `u`, `C`);
* the deterministic thinning is `exists_polySummable_thinning` (FirstPass/S3c/Thinning.lean).

Task fp-S3c-3-1-fidelity-fix (audit notes/fp-gaps/CHATGPT-idla-3-1-audit.md, §1.3): the admissibility of the data
(range, convergence of the scales, positivity of `C`, the two bounds) is samplewise. `DiscretePotentialTightnessPointwiseStmt`
puts it inside the implication on the common event (only the measurability of the data is global); it is proved by
`tightness_selection_pointwise` (FirstPass/S3c/PointwiseSelection.lean). `DiscretePotentialTightnessFaithfulStmt` and
`firstPass_3_1_corrected` are kept unchanged for their consumers.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- **Lemma 3.1, corrected, with the quantifier order of [C11]** (lemma:discrete-potential-tightness, paper line 976 of
paper/idla_mated_crt-corrected.tex; corrections [C3], [C10], [C11], N1 and N3 of docs/campaign/CORRECTIONS.md).

[C11] (docs/campaign/CORRECTIONS.md): "The printed random input sequence precedes a high-probability extraction. First
thin each deterministic sequence deterministically, then allow measurable random subsubsequences and countable families on
the inherited event." The printed statement: for each deterministic sequence `𝒮 ∋ ε → 0` there is a deterministic
subsequence `𝒮_* ⊂ 𝒮` such that the following holds almost surely: for every connected domain `D ⊂ B_ρ`, every
`σ(h,η)`-measurable `E ⊂ 𝒮_*` tending to zero and every `σ(h,η)`-measurable family `u^ε` satisfying the hypotheses, there
are a `σ(h,η)`-measurable subsequence `E₀ ⊂ E` and `ū ∈ C(D)` with `ū^ε → ū` uniformly on compacts of `D`, and on `cl(D)`
under the "moreover" hypotheses.

Formal reading. For every positive deterministic sequence `σ₀ → 0` there is a strictly increasing `φ` (the thinned scales
`σ₀ ∘ φ`) and ONE event `Ω₀` of probability one, chosen before the domain and the data; for every connected open
`D ⊆ B_ρ` and all data `E, u, C` satisfying the hypotheses of Lemma 3.1 with `E ω n ∈ range (σ₀ ∘ φ)`, there is a
measurable subsequence `Φ` (so `E₀ = E ∘ Φ`) such that at every `ω ∈ Ω₀` the conclusion holds. In
`DiscretePotentialTightnessCorrectedStmt` the domain and the data precede the almost-sure event, which is weaker. -/
def DiscretePotentialTightnessFaithfulStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ σ₀ : ℕ → ℝ, (∀ n, 0 < σ₀ n) → Tendsto σ₀ atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ Ω₀) ∧
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
  ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ ω n, E ω n ∈ range (fun k => σ₀ (φ k))) →
    (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
    (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) →
    Measurable[S.envSigma] C → (∀ ω, 0 < C ω) →
    (∀ ω n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
      |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) →
    (∀ ω n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |u ω n a| ≤ C ω / E ω n) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ ω ∈ Ω₀, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop O) ∧
      ((SimplyConnectedSpace D ∧
          (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D, matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
          ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n, E ω n < 1 →
            ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
              |u ω n a - u ω n b| ≤
                C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ) →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop (closure D))

namespace S3c

/-- **Lemma 3.1, corrected, faithful form** (`DiscretePotentialTightnessFaithfulStmt`; [C11]). The hypotheses are those of
`MatedCRT.firstPass_3_1_corrected` (FirstPass/S3S4.lean): `MepsScalingInput` (External, eq:meps-scaling, BG20 (1.8)),
Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`) and the frozen corrected Lemma 3.2
(`FrozenDiscreteHolderContinuityCorrected`). The name is namespaced because `MatedCRT.firstPass_3_1_corrected` already
names the weaker form. -/
theorem firstPass_3_1_corrected {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    DiscretePotentialTightnessFaithfulStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS σ₀ hpos hlim
  obtain ⟨φ, hφ, hpoly⟩ := exists_polySummable_thinning hpos hlim
  obtain ⟨Ω₀, hΩ₀, hsel⟩ := tightness_selection_common hm (boundedExitTimeRV_of_steps h27) h218 h32
    (adjacentCellsMeetAeStep 𝒮) γ hγ hγ2 ρ hρ hρ1 Ω S hS (fun k => σ₀ (φ k)) hpoly
  refine ⟨φ, hφ, Ω₀, hΩ₀, fun D hDρ hDo hDc E u C h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
  exact hsel D hDρ hDo hDc E u C (by unfold IsTightnessData; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩)

/-- **Lemma 3.1, corrected, samplewise admissibility** (task fp-S3c-3-1-fidelity-fix, audit §1.3). As
`DiscretePotentialTightnessFaithfulStmt`, but only the measurability of the data is imposed on the whole carrier; the
range condition, the convergence of the scales, the positivity of `C` and the two bounds are imposed at each sample
`ω ∈ Ω₀` inside the implication (`PointwiseTightnessData`). The conclusion is the same. -/
def DiscretePotentialTightnessPointwiseStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ σ₀ : ℕ → ℝ, (∀ n, 0 < σ₀ n) → Tendsto σ₀ atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ Ω₀) ∧
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
  ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) →
    Measurable[S.envSigma] C →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ ω ∈ Ω₀, PointwiseTightnessData S D (fun k => σ₀ (φ k)) E u C ω →
      StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop O) ∧
      ((SimplyConnectedSpace D ∧
          (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D, matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
          ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n, E ω n < 1 →
            ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
              |u ω n a - u ω n b| ≤
                C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ) →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop (closure D))

/-- **Lemma 3.1, corrected, samplewise faithful form** (`DiscretePotentialTightnessPointwiseStmt`; fidelity fix §1.3). -/
theorem firstPass_3_1_faithful {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    DiscretePotentialTightnessPointwiseStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS σ₀ hpos hlim
  obtain ⟨φ, hφ, hpoly⟩ := exists_polySummable_thinning hpos hlim
  obtain ⟨Ω₀, hΩ₀, hsel⟩ := tightness_selection_pointwise hm (boundedExitTimeRV_of_steps h27) h218 h32
    (adjacentCellsMeetAeStep 𝒮) γ hγ hγ2 ρ hρ hρ1 Ω S hS (fun k => σ₀ (φ k)) hpoly
  exact ⟨φ, hφ, Ω₀, hΩ₀, fun D hDρ hDo hDc E u C hEm hum hCm => hsel D hDρ hDo hDc E u C hEm hum hCm⟩

end S3c

end MatedCRT

#print axioms MatedCRT.S3c.firstPass_3_1_corrected
#print axioms MatedCRT.S3c.firstPass_3_1_faithful
