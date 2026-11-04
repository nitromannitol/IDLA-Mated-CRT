import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-! # Bounds on the discrete Green kernel away from its pole -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The logarithmic Green estimate gives a uniform bound at separated marked
points, simultaneously for every finite killed domain contained in the ball. -/
theorem separated_greenKernel_bound_in_probability (𝒮 : SpaceFillingSLEModel)
    (h214 : GreenKernelUpperBoundStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {d : ℝ} (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ProbTendsToOne S.P fun ε => {ω |
      ∀ A : Set ℤ, A.Finite →
        A ⊆ interiorCellVertices ε (S.η ω) (ball 0 ρ) →
        (interiorCellVertices ε (S.η ω) (ball 0 ρ)).Finite →
        (∀ a, {b | S.mult ε ω a b ≠ 0}.Finite) →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
        d ≤ ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ →
        greenKernel (S.mult ε ω) A a b ≤ K} := by
  obtain ⟨β, hβ, hβrest⟩ := h214 γ hγ hγ2
  obtain ⟨C, hC, hCrest⟩ := hβrest ρ hρ hρ1
  let K : ℝ := C * (|Real.log (1 / d)| + 1) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hgood := MatedCRT.HarmonicBalls.PolyHighProb.probTendsToOne (hCrest Ω S hS)
  unfold ProbTendsToOne at *
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgood
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_rpow_nhdsGT_zero hβ).eventually (Iio_mem_nhds hd)] with ε hε hpow
  apply measure_mono
  intro ω hbad hupper
  apply hbad
  intro A hA hAB hB hlf a ha b hb hsep
  have hdist : 0 < ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ :=
    hd.trans_le hsep
  have hlog : Real.log (1 / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ≤
      Real.log (1 / d) :=
    Real.log_le_log (one_div_pos.mpr hdist) (one_div_le_one_div_of_le hd hsep)
  calc
    greenKernel (S.mult ε ω) A a b ≤
        greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b :=
      greenKernel_mono_of_finite hlf (S.mult_succ_ne_zero hε.le ω) hA hB hAB a b
    _ ≤ C * Real.log (1 / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) + C :=
      hupper a ha b hb (hpow.le.trans hsep)
    _ ≤ K := by dsimp [K]; nlinarith [le_abs_self (Real.log (1 / d))]

end MatedCRT
