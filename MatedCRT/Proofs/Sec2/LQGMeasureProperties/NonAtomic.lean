import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Main
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Fact 2.2 I: no atoms in the unit disk from the volume growth estimate

The non-atomicity of `μ_h` (Fact 2.2 I, line 477) is not a consequence of the definition of `μ_h` as the vague limit
along `2⁻ᵏ` of the circle average approximations. Inside the unit disk it follows from the upper half of the cited volume
growth estimate (Lemma 2.7, BG20 Lemma A.1): with polynomially high probability `μ_h(B_δ(z)) ≤ δ^{β⁺}` for all
`z ∈ B_{1-δ}`, so by Borel-Cantelli along `δ = 2⁻ᵏ` a.s. `μ_h({x}) ≤ μ_h(B_{2⁻ᵏ}(x)) → 0` for every `x ∈ B_1`
(`ae_measure_singleton_eq_zero_of_volumeGrowth`).

Two other routes do not give all points at once:
* a fixed-point statement (`μ_h({x}) = 0` a.s. for each fixed `x`; for the whole-plane field this is Leonardo Bonanno's
  `MatedCRTHarmonic.GMCFacts.ae_measure_singleton_eq_zero`, `LatticeProb/Bonanno/MatedCRTHarmonic/GMCFacts/NoAtom.lean`)
  together with Fubini only gives `∫ P(μ_h({x}) > 0) dx = 0`, i.e. a.s. the set of atoms is Lebesgue-null, which holds
  for every locally finite measure (its atoms are countable);
* the cone field is not translation invariant and its dilations by a deterministic `s` do not preserve its law, so the
  disk `B_1` of Lemma 2.7 cannot be moved to other points without transferring the volume growth event through the law
  of the rescaled cone (`QuantumConeScalingInput`), which needs `μ_h` as a measurable function of the circle average
  process.
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Fact 2.2 I in the unit disk** from Lemma 2.7 (cited, BG20 Lemma A.1). A.s. the LQG measure of the quantum cone
has no atom in the open unit disk. -/
theorem ae_measure_singleton_eq_zero_of_volumeGrowth (h27 : VolumeGrowthStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hμ : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, ∀ x ∈ ball (0 : ℂ) 1, μ ω {x} = 0 := by
  have h2γ : 0 < 2 - γ := sub_pos.2 hγ2
  obtain ⟨βp, hβp, hβp2⟩ : ∃ β : ℝ, 0 < β ∧ β < (2 - γ) ^ 2 / 2 :=
    ⟨(2 - γ) ^ 2 / 4, by positivity, by nlinarith [sq_pos_of_pos h2γ]⟩
  have h := h27 γ hγ hγ2 βp ((2 + γ) ^ 2 / 2 + 1) hβp hβp2 (by linarith) Ω P hC hcirc μ hμ
  have htend : Tendsto (fun k : ℕ => ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ βp)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹ ^ k) ^ βp) atTop (𝓝 ((0 : ℝ) ^ βp)) :=
      (Real.continuousAt_rpow_const 0 βp (Or.inr (by first | exact hβp | exact hβp.le))).tendsto.comp
        tendsto_dyadicScale
    rw [Real.zero_rpow hβp.ne'] at h0
    have h1 := ENNReal.tendsto_ofReal h0
    rwa [ENNReal.ofReal_zero] at h1
  filter_upwards [h.ae_eventually_dyadic] with ω hω x hx
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
  have hsmall : ∀ᶠ k : ℕ in atTop, (2 : ℝ)⁻¹ ^ k < 1 - ‖x‖ :=
    tendsto_dyadicScale.eventually (gt_mem_nhds (sub_pos.2 hx1))
  refine le_antisymm (ge_of_tendsto htend ?_) zero_le
  filter_upwards [hω, hsmall] with k hk hks
  have hk' : ∀ z ∈ ball (0 : ℂ) (1 - (2 : ℝ)⁻¹ ^ k),
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ μ ω (ball z ((2 : ℝ)⁻¹ ^ k)) ∧
        μ ω (ball z ((2 : ℝ)⁻¹ ^ k)) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ βp) := hk
  have hxk : x ∈ ball (0 : ℂ) (1 - (2 : ℝ)⁻¹ ^ k) := mem_ball_zero_iff.2 (by linarith)
  exact (measure_mono (singleton_subset_iff.2 (mem_ball_self (pow_pos (by norm_num) k)))).trans (hk' x hxk).2

end MatedCRT.LQGMeasure
