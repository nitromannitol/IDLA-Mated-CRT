import MatedCRT.FirstPass.Derived.GMS21UniformStartOfHdiagProb
import LatticeProb.MeasureTheory.AeEventuallySubsequence

/-!
# The uniform-start invariance principle from the diagonal estimate in probability, without hypotheses on
measures

`gms21UniformStartInput_of_hdiagProb` takes two general measure-theory statements as hypotheses: the first
Borel–Cantelli lemma along a subsequence for arbitrary sets and the reverse Fatou lemma along subsequences.
This file supplies both from the probability library, so that the only hypothesis left is the diagonal estimate
in probability.

## Main results

* `gms21UniformStartInput_of_hdiagProb_derived`: the diagonal estimate in probability implies
  `GMS21UniformStartInput`.
-/

open MeasureTheory Set Metric MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace UniformStartGood

open LatticeProb MatedCRT.StopAtExitCmp MatedCRT.BlockExit

/-- **The uniform-start invariance principle from the diagonal estimate in probability, without hypotheses on
measures.** The statement is `gms21UniformStartInput_of_hdiagProb` with the Borel–Cantelli and reverse Fatou
hypotheses discharged by `LatticeProb.exists_strictMono_ae_eventually_notMem_of_tendsto_measure` and
`LatticeProb.exists_eps_measure_compl_le_of_ae_eventually_subseq`. -/
theorem gms21UniformStartInput_of_hdiagProb_derived {𝒮 : SpaceFillingSLEModel}
    (hdiagProb : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ (s ρ₀ δ : ℝ), 0 < s → 0 < δ →
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ s / 2 ∧ 24 * θ / s ≤ δ / 2 ∧
        ∀ θ' : ℝ, 0 < θ' → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S.P {ω | ¬ ∀ y ∉ ballFrozenSet s ρ₀, ∀ u : ℤ, dist (vertexPoint ε (S.η ω) u) y ≤ θ →
            ProkhorovLE (walkNextBlockExitKernel (S.mult ε ω) (vertexPoint ε (S.η ω)) zero_le_one s
                (ballFrozenSet s ρ₀) (y, u))
              (blockExitKernel s (cellIndex s y) (vertexPoint ε (S.η ω) u)) δ (δ / 2)} ≤
            ENNReal.ofReal θ') :
    GMS21UniformStartInput 𝒮 :=
  gms21UniformStartInput_of_hdiagProb
    (fun μ B h => LatticeProb.exists_strictMono_ae_eventually_notMem_of_tendsto_measure μ B h)
    (fun P _ M hM h _ hθ => LatticeProb.exists_eps_measure_compl_le_of_ae_eventually_subseq P M hM h hθ)
    hdiagProb

end UniformStartGood

end MatedCRT
