import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.SourceVertex
import MatedCRT.Draft.Section3

/-! # Convergence of the discrete obstacle away from its pole -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory HarmonicBalls

/-- Lemma 3.3 gives convergence of the actual Section 4 obstacle on sets
separated from the origin. The source identification holds almost surely
simultaneously for all positive meshes. -/
theorem obstacle_convergence_off_origin (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) (O : Set ℂ)
    (hO : O ⊆ closedBall 0 ρ \ {0}) (hdist : 0 < infDist (0 : ℂ) O) :
    ProbTendsToOne S.P fun ε => {ω | ∀ x ∈ O,
      |rescale (S.mε ε) ε (S.η ω) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)| ≤ δ} := by
  have hgreen := h33 γ hγ hγ' ρ hρ hρ' Ω S hS ρ 0 0 hρ (Subset.rfl)
    (mem_ball_self hρ) (δ / t) (div_pos hδ ht) O hO hdist
  unfold ProbTendsToOne at hgreen ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgreen
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono_ae
  filter_upwards [hS.ae_vertexOf_zero_eq_zero] with ω hsource
  intro hbad hgood
  apply hbad
  intro x hx
  have hg := hgood x hx
  rw [hsource ε hε] at hg
  have hid : rescale (S.mε ε) ε (S.η ω)
      (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x =
      -t * rescale (S.mε ε) ε (S.η ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a) x := by
    simp only [rescale, matedObstacle, div_eq_mul_inv]
    ring
  rw [hid]
  have hid' : -t * rescale (S.mε ε) ε (S.η ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a) x -
      (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) =
      -t * (rescale (S.mε ε) ε (S.η ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a) x -
        S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x) := by ring
  rw [hid', abs_mul, abs_neg, abs_of_pos ht]
  calc
    t * |rescale (S.mε ε) ε (S.η ω)
      (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a) x -
      S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x| ≤ t * (δ / t) :=
        mul_le_mul_of_nonneg_left hg ht.le
    _ = δ := by field_simp

end MatedCRT
