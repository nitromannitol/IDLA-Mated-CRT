import MatedCRT.FirstPass.S5d.StoppedPathwise
import MatedCRT.Proofs.Sec5.StoppedMeanValueInequality
import MatedCRT.Proofs.Sec5.MeanValueInequality.ExitTimeMonotonicity
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Measurability.GoodScale
import MatedCRT.Draft.Section2

/-!
# The exit-sum input (E) of the stopped clause (task fp-S5d-5-1-stopped-repair)

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
        have hΛball : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime hρ hmono ht hT
        have hVfin : (cellVertices ε (S.η ω) (Λ ω t)).Finite :=
          hBfin.subset (cellVertices_mono_set hΛball)
        have hI : (stoppedKillSet S Λ ρ t ε ω).Finite :=
          hBfin.subset fun a ha => mem_cellVertices_ball_of_mem_matedDiscreteCluster ha.2.1
        have hIV : stoppedKillSet S Λ ρ t ε ω ⊆ cellVertices ε (S.η ω) (Λ ω t) := fun a ha => ha.2.2
        rw [Set.mem_ofPred_eq] at hE
        obtain ⟨-, hQ⟩ := hE hF
        intro a ha
        have haV : a ∈ cellVertices ε (S.η ω) (Λ ω t) := by
          rcases ha with ha | ha
          · exact cellVertices_mono_set (fun y hy => hy.1) ha
          · rw [Set.mem_singleton_iff] at ha
            rw [ha]
            exact h0
        calc ∑' b : stoppedKillSet S Λ ρ t ε ω,
              greenKernel (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a b
            = normExitTime (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a := rfl
          _ ≤ normExitTime (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a :=
            normExitTime_killing_le hlf hcons hI hVfin hIV a
          _ ≤ C ω / ε := hQ a haV

end MatedCRT
