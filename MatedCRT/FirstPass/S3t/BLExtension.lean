import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelopeOn
import MatedCRT.FirstPass.S3t.Defs

/-!
# Truncated quenched laws, Step 2: bounded-Lipschitz extension to continuous functionals

Step 2 of the truncated-laws argument (section 3). Convergence in probability of the quenched
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

/-- Scaling by a constant preserves continuity within a path set. -/
lemma pathFunctionalContinuousWithinAt_const_mul {𝒞 : Set (ℝ≥0 → ℂ)} {H : (ℝ≥0 → ℂ) → ℝ} {w : ℝ≥0 → ℂ}
    (c : ℝ) (hH : MatedCRT.PathFunctionalContinuousWithinAt 𝒞 H w) :
    MatedCRT.PathFunctionalContinuousWithinAt 𝒞 (fun v => c * H v) w := by
  intro η hη
  obtain ⟨ρ, hρ, hcont⟩ := hH (η / (|c| + 1)) (div_pos hη (by positivity))
  refine ⟨ρ, hρ, fun v hv hd => ?_⟩
  have h1 := hcont v hv hd
  rw [← mul_sub, abs_mul]
  calc |c| * |H v - H w| ≤ (|c| + 1) * (η / (|c| + 1)) :=
        mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity)
    _ = η := by field_simp

/-- **Measurable closure of a scalar LBM observable** (answer 46(a2) §1, `lbm_scalar_measurable_of_bl_envelopes`).
If `H` is bounded on the continuous-path set `𝒞`, continuous within `𝒞` at almost every limiting path, and every
bounded-Lipschitz observable of the limiting path is measurable (`hBLmeas`), then `b ↦ H (X ω b)` is
`AEStronglyMeasurable` for almost every `ω`, and `ω ↦ ∫ H (X ω b) dν` is `AEMeasurable`. Neither joint measurability of
`X` nor global measurability of `H` is used: the bounded-Lipschitz upper envelopes of `H / L₁` over `𝒞`
(`MatedCRT.pathUpperEnvelopeOn`) converge to `H / L₁` at every continuity point in `𝒞`, and dominated convergence
transfers this to the integrals. The nonempty hypothesis `h𝒞` is needed for the envelopes. -/
theorem lbm_scalar_measurable_of_bl_envelopes
    {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B] {P : Measure Ω} {ν : Measure B} [IsFiniteMeasure ν]
    (𝒞 : Set (ℝ≥0 → ℂ)) (h𝒞 : 𝒞.Nonempty) (X : Ω → B → ℝ≥0 → ℂ) (H : (ℝ≥0 → ℂ) → ℝ)
    (hX𝒞 : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, X ω b ∈ 𝒞)
    (hHbd : ∃ L : ℝ, ∀ w ∈ 𝒞, |H w| ≤ L)
    (hHcont : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, MatedCRT.PathFunctionalContinuousWithinAt 𝒞 H (X ω b))
    (hBLmeas : ∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F →
      (∀ᵐ ω ∂P, AEStronglyMeasurable (fun b => F (X ω b)) ν) ∧
        AEMeasurable (fun ω => ∫ b, F (X ω b) ∂ν) P) :
    (∀ᵐ ω ∂P, AEStronglyMeasurable (fun b => H (X ω b)) ν) ∧
      AEMeasurable (fun ω => ∫ b, H (X ω b) ∂ν) P := by
  obtain ⟨L, hL⟩ := hHbd
  set L₁ : ℝ := max 1 |L| with hL₁def
  have hL₁ : 0 < L₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  set G : (ℝ≥0 → ℂ) → ℝ := fun w => L₁⁻¹ * H w with hGdef
  have hG : ∀ w ∈ 𝒞, |G w| ≤ 1 := by
    intro w hw
    have hbound : |H w| ≤ L₁ := (hL w hw).trans ((le_abs_self L).trans (le_max_right _ _))
    rw [hGdef, abs_mul, abs_of_pos (inv_pos.2 hL₁)]
    calc L₁⁻¹ * |H w| ≤ L₁⁻¹ * L₁ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hL₁.le)
      _ = 1 := inv_mul_cancel₀ hL₁.ne'
  have hGcont : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, X ω b ∈ 𝒞 ∧ MatedCRT.PathFunctionalContinuousWithinAt 𝒞 G (X ω b) := by
    filter_upwards [hHcont, hX𝒞] with ω hω hXω
    filter_upwards [hω, hXω] with b hb hXb
    exact ⟨hXb, pathFunctionalContinuousWithinAt_const_mul _ hb⟩
  have hF : ∀ n : ℕ, IsBoundedLipschitzPathFunctional (MatedCRT.pathUpperEnvelopeOn 𝒞 G n) := fun n =>
    MatedCRT.isBoundedLipschitzPathFunctional_pathUpperEnvelopeOn hG (Nat.cast_nonneg n) h𝒞
  have hlimF : ∀ w ∈ 𝒞, MatedCRT.PathFunctionalContinuousWithinAt 𝒞 G w →
      Tendsto (fun n : ℕ => MatedCRT.pathUpperEnvelopeOn 𝒞 G n w) atTop (𝓝 (G w)) :=
    fun w hw hc => MatedCRT.tendsto_pathUpperEnvelopeOn hG hw hc
  have hmeasN : ∀ᵐ ω ∂P, ∀ n : ℕ,
      AEStronglyMeasurable (fun b => MatedCRT.pathUpperEnvelopeOn 𝒞 G n (X ω b)) ν :=
    ae_all_iff.2 fun n => (hBLmeas _ (hF n)).1
  have hlim : ∀ᵐ ω ∂P, ∀ᵐ b ∂ν,
      Tendsto (fun n : ℕ => MatedCRT.pathUpperEnvelopeOn 𝒞 G n (X ω b)) atTop (𝓝 (G (X ω b))) :=
    hGcont.mono fun ω h => h.mono fun b hb => hlimF _ hb.1 hb.2
  have hAE : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun b => G (X ω b)) ν := by
    filter_upwards [hmeasN, hlim] with ω hmω hlimω
    exact aestronglyMeasurable_of_tendsto_ae atTop hmω hlimω
  have hint : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ b, MatedCRT.pathUpperEnvelopeOn 𝒞 G n (X ω b) ∂ν) atTop
      (𝓝 (∫ b, G (X ω b) ∂ν)) := by
    filter_upwards [hmeasN, hlim] with ω hmω hlimω
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hmω (integrable_const 1) ?_ hlimω
    intro n
    obtain ⟨hb1, _⟩ := hF n
    exact Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hb1 (X ω b)
  have hAEint : AEMeasurable (fun ω => ∫ b, G (X ω b) ∂ν) P :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hBLmeas _ (hF n)).2) hint
  have e2 : ∀ ω, (∫ b, H (X ω b) ∂ν) = L₁ * ∫ b, G (X ω b) ∂ν := fun ω => by
    rw [← integral_const_mul]
    congr 1
    funext b
    exact (mul_inv_cancel_left₀ hL₁.ne' _).symm
  refine ⟨?_, ?_⟩
  · filter_upwards [hAE] with ω hω
    have e : (fun b => H (X ω b)) = fun b => L₁ * G (X ω b) := by
      funext b
      exact (mul_inv_cancel_left₀ hL₁.ne' _).symm
    rw [e]
    exact hω.const_mul L₁
  · have e : (fun ω => ∫ b, H (X ω b) ∂ν) = fun ω => L₁ * ∫ b, G (X ω b) ∂ν := funext e2
    rw [e]
    exact hAEint.const_mul L₁

#print axioms lbm_scalar_measurable_of_bl_envelopes

end MatedCRT.TruncatedLaws
