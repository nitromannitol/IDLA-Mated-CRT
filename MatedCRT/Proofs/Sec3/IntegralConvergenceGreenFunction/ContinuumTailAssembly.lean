import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.DiscreteTailProbability
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Measure

/-! Almost-sure limits of continuum truncations and convergence in probability. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Almost-sure convergence of almost-everywhere measurable real variables
implies convergence of the strict-error event probabilities to zero. -/
theorem tendsto_measure_abs_sub_gt_of_ae_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (V : ℕ → Ω → ℝ) (U : Ω → ℝ)
    (hV : ∀ n, AEMeasurable (V n) P) (hU : AEMeasurable U P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (U ω)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => P {ω | t < |V n ω - U ω|}) atTop (𝓝 0) := by
  apply tendsto_measure_zero_of_ae_eventually_not_mem P
  · intro n
    exact ((hV n).sub hU).abs.nullMeasurableSet_preimage measurableSet_Ioi
  · filter_upwards [hconv] with ω hω
    have hnear := hω.eventually (Metric.ball_mem_nhds (U ω) ht)
    filter_upwards [hnear] with n hn
    change dist (V n ω) (U ω) < t at hn
    exact not_lt_of_ge (by simpa [Real.dist_eq] using hn.le)

/-- The Green sum converges once fixed-time convergence and almost-sure
convergence of the integer-time continuum occupations are established. -/
theorem integralConvergenceGreenFunction_of_fixed_and_ae_continuum
    {𝒮 : SpaceFillingSLEModel} (h17 : BoundedExitTimeRVStmt)
    (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : Ω → ℂ → ℝ)
    (hfmeas : ∀ x, Measurable[S.envSigma] fun ω => f ω x)
    (hfbound : ∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M)
    (hfcont : ∀ ω, IsHolderContinuousOn (f ω) (ball z r))
    (hfixed : ∀ T : ℝ, 0 < T → TendstoInProbability S.P
      (fun ε ω => truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω)
      (truncatedLBMOccupation S (ball z r) y f T))
    (hVm : ∀ n : ℕ, AEMeasurable (truncatedLBMOccupation S (ball z r) y f n) S.P)
    (hUm : AEMeasurable (fun ω => S.c₀ *
      ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω) S.P)
    (hV : ∀ᵐ ω ∂S.P, Tendsto
      (fun n : ℕ => truncatedLBMOccupation S (ball z r) y f n ω) atTop
      (𝓝 (S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω))) :
    TendstoInProbability S.P
      (fun ε ω => (S.mε ε)⁻¹ * ∑' x : cellVertices ε (S.η ω) (ball z r),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) x * f ω (vertexPoint ε (S.η ω) x))
      (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω) := by
  let := hS.isProbabilityMeasure
  apply integralConvergenceGreenFunction_of_truncation S (ball z r) y f hfixed
  intro t ht e he
  obtain ⟨T, hT, hdisc⟩ := discrete_green_occupation_tail_uniform_in_time
    h17 h18 hscale hγ hγ2 hρ hρ1 S hS hr hball hy f hfmeas hfbound hfcont t ht e he
  have hprob := tendsto_measure_abs_sub_gt_of_ae_tendsto S.P
    (fun n => truncatedLBMOccupation S (ball z r) y f n)
    (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω)
    hVm hUm hV ht
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hprob.eventually (gt_mem_nhds he))
  obtain ⟨k, hk⟩ := exists_nat_gt T
  let n := max N k
  have hnk : k ≤ n := le_max_right _ _
  have hTn : T ≤ (n : ℝ) := le_trans hk.le (by exact_mod_cast hnk)
  have hn : 0 < (n : ℝ) := hT.trans_le hTn
  refine ⟨n, hn, ?_, hN n (le_max_left _ _)⟩
  filter_upwards [hdisc] with ε hε
  exact hε n hTn

end MatedCRT
