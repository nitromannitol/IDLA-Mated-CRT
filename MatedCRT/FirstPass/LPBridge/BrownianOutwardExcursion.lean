import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.LPStaging.Prob.BrownianOutwardExcursion
import MatedCRT.LPStaging.Prob.PlanarBrownianGermZeroOne
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-!
# Bridge: the frozen planar outward excursion at the exit time of a disk (#53)

`FrozenBrownianOutwardExcursionAtExit` (FirstPass/Frozen/S3S4.lean) is the planar Brownian outward
excursion at the exit time of a disk (Mörters–Peres, *Brownian Motion*, Theorems 2.7 and 2.16).
This file reduces it to the Mathlib-only planar result `LatticeProb.PlanarBrownian.ae_frequently_excursion`.

Two literature inputs are explicit hypotheses of `frozenBrownianOutwardExcursionAtExit_of_inputs`:
* `hGerm`: Blumenthal's zero-one law for the germ σ-algebra of every planar Brownian motion
  (Mörters–Peres, Theorem 2.7 with `d = 2`);
* `hRestart`: for the exit time `τ` of a disk, the post-`τ` increments are a planar Brownian motion
  independent of `B_τ`, and `B_τ` is measurable (strong Markov property at `τ`,
  Mörters–Peres, Theorem 2.16).

The unconditional statement needs these inputs as Props in `MatedCRT/External`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped NNReal ENNReal Topology

namespace MatedCRT

/-- The planar outward excursion at the exit time of a disk, conditional on the germ zero-one law
and on the strong Markov restart at the exit time. -/
theorem frozenBrownianOutwardExcursionAtExit_of_inputs
    (hGerm : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : ℝ≥0 → Ω → ℂ), LatticeProb.PlanarBrownian.IsPlanarBrownian W P →
      ∀ A : Set Ω,
        MeasurableSet[⨅ n : ℕ, LatticeProb.PlanarBrownian.pathSigmaTo W
          (LatticeProb.PlanarBrownian.freqEps n)] A → P A = 0 ∨ P A = 1)
    (hRestart : ∀ (y z : ℂ) (r : ℝ), y ∈ Metric.ball z r →
      LatticeProb.PlanarBrownian.IsPlanarBrownian
          (fun (s : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal + s) -
              b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (planarBrownianMotion y) ∧
        IndepFun
          (fun b : MarkovProcess.ContinuousPath ℂ =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (fun (b : MarkovProcess.ContinuousPath ℂ) (s : ℝ≥0) =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal + s) -
              b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (planarBrownianMotion y) ∧
        AEMeasurable
          (fun b : MarkovProcess.ContinuousPath ℂ =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (planarBrownianMotion y)) :
    FrozenBrownianOutwardExcursionAtExit := by
  intro y z r hy
  obtain ⟨hW, hind, hBτ⟩ := hRestart y z r hy
  have hpos : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.1 hy)
  have hfin : ∀ᵐ b ∂planarBrownianMotion y,
      MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top y
      (Metric.isBounded_ball (x := z) (r := r))).mono fun b hb => hb.ne
  have hstart : ∀ᵐ b ∂planarBrownianMotion y, b 0 = y :=
    ae_planarBrownianMotion_eval_zero y
  have hz : ∀ᵐ b ∂planarBrownianMotion y,
      b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal) ≠ z := by
    filter_upwards [hfin, hstart] with b hb hb0
    have hmem0 : b 0 ∈ Metric.ball z r := by rw [hb0]; exact hy
    have hfr := MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier
      (Metric.ball z r) isOpen_ball b hmem0 hb
    rw [frontier_ball z hpos.ne'] at hfr
    intro heq
    rw [heq, mem_sphere, dist_self] at hfr
    exact hpos.ne hfr
  exact LatticeProb.PlanarBrownian.ae_frequently_excursion (hW := hW)
    (hBlum := fun A hA => hGerm _ _ _ hW A hA) (hBτ := hBτ) (hind := hind) (hz := hz)

/-- The germ zero-one law of the frozen excursion statement is discharged by the ported Blumenthal
law: the coordinate germ laws of a planar Brownian motion are trivial (`isTrivialSigma_iInf_bmPast`),
so the planar germ σ-algebra is trivial (`isTrivialSigma_iInf_pathSigmaTo_planar`). Only the strong
Markov restart at the exit time remains an explicit input. -/
theorem frozenBrownianOutwardExcursionAtExit_of_restart
    (hRestart : ∀ (y z : ℂ) (r : ℝ), y ∈ Metric.ball z r →
      LatticeProb.PlanarBrownian.IsPlanarBrownian
          (fun (s : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal + s) -
              b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (planarBrownianMotion y) ∧
        IndepFun
          (fun b : MarkovProcess.ContinuousPath ℂ =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (fun (b : MarkovProcess.ContinuousPath ℂ) (s : ℝ≥0) =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal + s) -
              b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (planarBrownianMotion y) ∧
        AEMeasurable
          (fun b : MarkovProcess.ContinuousPath ℂ =>
            b ((MarkovProcess.ContinuousPath.exitTime (Metric.ball z r) b).toNNReal))
          (planarBrownianMotion y)) :
    FrozenBrownianOutwardExcursionAtExit :=
  frozenBrownianOutwardExcursionAtExit_of_inputs
    (fun _ _ _ _ _ hW A hA =>
      LatticeProb.PlanarBrownian.isTrivialSigma_iInf_pathSigmaTo_planar hW
        (LatticeProb.isTrivialSigma_iInf_bmPast hW.re fun t => Complex.measurable_re.comp (hW.measurable t))
        (LatticeProb.isTrivialSigma_iInf_bmPast hW.im fun t => Complex.measurable_im.comp (hW.measurable t))
        A hA)
    hRestart

end MatedCRT
