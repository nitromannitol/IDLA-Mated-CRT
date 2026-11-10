import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelopeOn
import MatedCRT.FirstPass.S3t.Defs

/-!
# Truncated quenched laws, Step 2: bounded-Lipschitz extension to continuous functionals (fp-S3t, z2)

Step 2 of `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md` (section 3). Convergence in probability of the quenched
integrals of bounded-Lipschitz path functionals (Theorem 2.11 of the paper, Berestycki–Gwynne Theorem 1.2) extends to
bounded path functionals `H` that are continuous at almost every limiting path for the local uniform distance. The
argument is the Pasch–Hausdorff envelope argument of `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PathEnvelopeOn.lean`
(`MatedCRT.tendstoInProbability_of_ae_continuousWithin_pathFunctional`), specialised to the whole path space and rescaled
so that the bound is `1`.

Differences from the answer's statement, each needed and flagged: the probability measure `P` is a probability measure;
the measures `μ ε ω` and `ν` are finite; and the measurability hypotheses `hFW`, `hFX`, `hFXω`, `hHW` are included, since
without them the integrals need not be defined. `Measurable H` is not needed: `hHW` suffices. Continuity is
`PathFunctionalContinuousAt` (`PathEnvelope.lean`), which is `ContinuousAtLocalUniform` of the answer.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- Scaling by a positive constant preserves convergence in probability. -/
theorem tendstoInProbability_const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → ℝ}
    {Y : Ω → ℝ} {c : ℝ} (hc : 0 < c) (h : MatedCRT.TendstoInProbability P X Y) :
    MatedCRT.TendstoInProbability P (fun ε ω => c * X ε ω) (fun ω => c * Y ω) := by
  intro δ hδ
  refine Tendsto.congr (fun ε => ?_) (h (δ / c) (div_pos hδ hc))
  dsimp only
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [← mul_sub, abs_mul, abs_of_pos hc, div_lt_iff₀ hc, mul_comm c]

/-- Step 2, bounded-Lipschitz extension: convergence in probability of the quenched integrals of every bounded-Lipschitz
path functional gives the same for every bounded path functional `H` that is continuous at almost every limiting path
(for the local uniform distance). -/
theorem quenched_integral_tendsto_of_bl_of_ae_continuous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ℝ → Ω → Measure α) (hμ : ∀ ε ω, IsFiniteMeasure (μ ε ω))
    (W : ℝ → Ω → α → ℝ≥0 → ℂ)
    (ν : Measure β) [IsFiniteMeasure ν] (X : Ω → β → ℝ≥0 → ℂ)
    (𝒞 : Set (ℝ≥0 → ℂ)) (h𝒞 : 𝒞.Nonempty)
    (hW𝒞 : ∀ ε ω, ∀ᵐ a ∂(μ ε ω), W ε ω a ∈ 𝒞) (hX𝒞 : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, X ω b ∈ 𝒞)
    (hBL : ∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F →
      MatedCRT.TendstoInProbability P (fun ε ω => ∫ a, F (W ε ω a) ∂(μ ε ω))
        (fun ω => ∫ b, F (X ω b) ∂ν))
    (hFW : ∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F → ∀ ε ω,
      AEStronglyMeasurable (fun a => F (W ε ω a)) (μ ε ω))
    (hFX : ∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F → ∀ᵐ ω ∂P,
      AEStronglyMeasurable (fun b => F (X ω b)) ν)
    (hFXω : ∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F →
      AEMeasurable (fun ω => ∫ b, F (X ω b) ∂ν) P)
    (H : (ℝ≥0 → ℂ) → ℝ) (hHbd : ∃ L : ℝ, ∀ w, |H w| ≤ L)
    (hHW : ∀ ε ω, AEStronglyMeasurable (fun a => H (W ε ω a)) (μ ε ω))
    (hHcont : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, MatedCRT.PathFunctionalContinuousWithinAt 𝒞 H (X ω b)) :
    MatedCRT.TendstoInProbability P (fun ε ω => ∫ a, H (W ε ω a) ∂(μ ε ω))
      (fun ω => ∫ b, H (X ω b) ∂ν) := by
  obtain ⟨c, hc, hcH⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w, |H w| ≤ c := by
    obtain ⟨L, hL⟩ := hHbd
    exact ⟨max L 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun w => (hL w).trans (le_max_left _ _)⟩
  have hG : ∀ w ∈ 𝒞, |c⁻¹ * H w| ≤ 1 := by
    intro w _
    rw [abs_mul, abs_inv, abs_of_pos hc]
    calc c⁻¹ * |H w| ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (hcH w) (inv_nonneg.2 hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hcontG : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, X ω b ∈ 𝒞 ∧
      MatedCRT.PathFunctionalContinuousWithinAt 𝒞 (fun v => c⁻¹ * H v) (X ω b) := by
    filter_upwards [hHcont, hX𝒞] with ω hω hXω
    filter_upwards [hω, hXω] with b hb hXb
    refine ⟨hXb, ?_⟩
    intro η hη
    obtain ⟨ρ, hρ, hρH⟩ := hb (c * η) (mul_pos hc hη)
    refine ⟨ρ, hρ, fun v hv_mem hv => ?_⟩
    have h1 := hρH v hv_mem hv
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * |H v - H (X ω b)| ≤ c⁻¹ * (c * η) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc.le)
      _ = η := inv_mul_cancel_left₀ hc.ne' η
  have key := MatedCRT.tendstoInProbability_of_ae_continuousWithin_pathFunctional P μ (fun ε ω => hμ ε ω) W
    (fun _ => ν) (fun _ => inferInstance) X (fun F hF => hBL F hF) 𝒞 h𝒞
    (fun w => c⁻¹ * H w) hG hW𝒞
    (fun ε ω => (hHW ε ω).const_mul c⁻¹) (fun F hF ε ω => hFW F hF ε ω) (fun F hF => hFX F hF)
    (fun F hF => hFXω F hF) hcontG
  have hscaled := tendstoInProbability_const_mul hc key
  have e1 : ∀ ε ω, c * ∫ x, c⁻¹ * H (W ε ω x) ∂(μ ε ω) = ∫ a, H (W ε ω a) ∂(μ ε ω) := fun ε ω => by
    rw [integral_const_mul, mul_inv_cancel_left₀ hc.ne']
  have e2 : ∀ ω, c * ∫ b, c⁻¹ * H (X ω b) ∂ν = ∫ b, H (X ω b) ∂ν := fun ω => by
    rw [integral_const_mul, mul_inv_cancel_left₀ hc.ne']
  simpa only [e1, e2] using hscaled

#print axioms quenched_integral_tendsto_of_bl_of_ae_continuous

end MatedCRT.TruncatedLaws
