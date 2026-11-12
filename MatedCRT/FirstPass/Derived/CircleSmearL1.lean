import MatedCRT.FirstPass.Derived.ConeRadialL4
import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.LQGMetric.Field.CircleSmearDilate

/-!
# Smeared circle averages of the quantum cone at every dilation scale

For the circle average embedding `h` of the `γ`-quantum cone, a test function `φ`, and a regular representative
`H : Ω → DistC` of the pairings of `h` (that is, a.s. `(h, χ) = H χ` for every test function `χ`), almost surely,
for **every** dilation `s > 0` simultaneously,
`∫ φ(s z) h_ε(z) dz → H(φ(s ·))` as `ε ↓ 0`.

The proof intersects, over the countably many rational pairs `(s, ε)`, the events of the circle smear identity
`∫ ψ(z) h_ε(z) dz = (h, K_ε ψ)` for `ψ = φ(s ·)` (`IsQuantumCone.circleSmearIdentity`), with the event on which the
circle average process is jointly continuous and the event on which `H` represents `h`. On that event the identity
extends to all real `(s, ε)` by continuity, and the circle means `K_ε ψ` converge to `ψ` in the test function topology
(`LQGMetric.tendsto_integral_smul_mul_of_rat`).

For the environment of the paper the representative is the cone field of the mating-of-trees coupling
(`MatedCRTEnv.IsValid.exists_ae_tendsto_integral_smul_mul_circle`).
-/

open MeasureTheory Filter Set Topology HarmonicBalls

namespace MatedCRT.LQGMeasure

/-- **Smeared circle averages of the quantum cone at all dilation scales.** If `H` represents the pairings of the
circle average embedding of the `γ`-quantum cone, then for every test function `φ`, almost surely, for every `s > 0`,
`∫ φ(s z) h_ε(z) dz → H(φ(s ·))` as `ε ↓ 0` (here `φ(s ·) = testAffinePull s⁻¹ 0 φ`). -/
theorem IsQuantumCone.ae_tendsto_integral_smul_mul_circle {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc)
    {H : Ω → LQGMetric.DistC} (hH : ∀ᵐ ω ∂P, ∀ χ : LQGMetric.TestC, hC ω ⇑χ = H ω χ)
    (φ : LQGMetric.TestC) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → Tendsto (fun ε => ∫ z, φ (s • z) * hcirc ω ε z) (𝓝[>] 0)
      (𝓝 (H ω (LQGMetric.testAffinePull s⁻¹ 0 φ))) := by
  have hA : ∀ᵐ ω ∂P, ∀ s ε : ℚ, 0 < s → 0 < ε → ε < 1 →
      ∫ z, φ ((s : ℝ) • z) * hcirc ω (ε : ℝ) z =
        hC ω (circleKernel ⇑(LQGMetric.testAffinePull (s : ℝ)⁻¹ 0 φ) (ε : ℝ)) := by
    rw [ae_all_iff]
    intro s
    rw [ae_all_iff]
    intro ε
    by_cases hs : (0 : ℚ) < s
    · by_cases hε : (0 : ℚ) < ε ∧ ε < 1
      · have hψ : IsTestFunction univ ⇑(LQGMetric.testAffinePull (s : ℝ)⁻¹ 0 φ) :=
          ⟨(LQGMetric.testAffinePull (s : ℝ)⁻¹ 0 φ).contDiff,
            (LQGMetric.testAffinePull (s : ℝ)⁻¹ 0 φ).hasCompactSupport, subset_univ _⟩
        have hε0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε.1
        have hε1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε.2.le
        have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
        filter_upwards [IsQuantumCone.circleSmearIdentity hQ hψ hε0 hε1] with ω hω
        intro _ _ _
        rw [← hω]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [LQGMetric.testAffinePull_inv_zero_apply φ hs0 z]
      · exact Eventually.of_forall fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hε
    · exact Eventually.of_forall fun _ h => absurd h hs
  filter_upwards [hA, hH, hQ.ae_continuousOn_circle] with ω hAω hHω hcont s hs
  refine LQGMetric.tendsto_integral_smul_mul_of_rat (H ω) φ hcont (fun s ε hs hε hε1 => ?_) hs
  rw [hAω s ε hs hε hε1]
  exact hHω (LQGMetric.circleMeanTest (LQGMetric.testAffinePull (s : ℝ)⁻¹ 0 φ) (ε : ℝ))

end MatedCRT.LQGMeasure

namespace MatedCRT

/-- **Smeared circle averages in the environment of the paper.** For a valid environment, the cone field of the
mating-of-trees coupling is a regular representative `H` of the pairings of `h`, and for every test function `φ`,
almost surely, for every `s > 0`, `∫ φ(s z) h_ε(z) dz → H(φ(s ·))` as `ε ↓ 0`. -/
theorem MatedCRTEnv.IsValid.exists_ae_tendsto_integral_smul_mul_circle {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hv : S.IsValid 𝒮 γ) :
    ∃ H : Ω → LQGMetric.DistC, (∀ᵐ ω ∂S.P, ∀ χ : LQGMetric.TestC, S.hC ω ⇑χ = H ω χ) ∧
      ∀ φ : LQGMetric.TestC, ∀ᵐ ω ∂S.P, ∀ s : ℝ, 0 < s →
        Tendsto (fun ε => ∫ z, φ (s • z) * S.hcirc ω ε z) (𝓝[>] 0)
          (𝓝 (H ω (LQGMetric.testAffinePull s⁻¹ 0 φ))) := by
  obtain ⟨X, _, _, B, B', _, _, _, _, _, _, _, hrep⟩ := hv.matingOfTrees
  refine ⟨fun ω => MatedCRTHarmonic.MatedCRT.coneField (X ω)
    (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), ?_, fun φ => ?_⟩
  · filter_upwards [hrep] with ω hω
    exact hω.2
  · refine LQGMeasure.IsQuantumCone.ae_tendsto_integral_smul_mul_circle hv.isQuantumCone ?_ φ
    filter_upwards [hrep] with ω hω
    exact hω.2

end MatedCRT
