import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.B1EnvPwG68

/-!
# The counting residual `ShellCGResCountGood` (q2, fp-S4S6c-cgres-count)

STEP A (`resCountGood_pt`): the pointwise counting lower bound on the cells of `D ⊆ B(0, ρ)` at one environment `ω`. Its
counting membership is the component `ω ∈ countingMeshEventR` (`countingMeshEventR_counting`, Guard68S10.lean); the bound is
`hCountGood_pw_g` (B1EnvPwG68.lean:60), the Berestycki-Gwynne counting lemma (Draft Lemma 2.9, `CountingMeasureConvergenceStmt`,
Draft/Section2.lean:143). The body of `resCountGood_pt` is the body of `ShellCGResCountGood` (ShellCoreCG68.lean:435) after its
two premises. The full-support clause of `ShellPtPremCG` is not used.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGResCount

open Lemma68Guard10

/-- `shellEps0ZCG ≤ 1` for `0 < CG`: `shellEps0ZCG ≤ shellEps0CG ≤ exp(-2CG)/2 ≤ 1`. -/
lemma shellEps0ZCG_le_one {γ α ω₀ ζ CG : ℝ} (hCG : 0 < CG) : shellEps0ZCG γ α ω₀ ζ CG ≤ 1 := by
  have h1 : shellEps0ZCG γ α ω₀ ζ CG ≤ shellEps0CG γ α ω₀ CG := shellEps0ZCG_le γ α ω₀ ζ CG
  have h2 : shellEps0CG γ α ω₀ CG ≤ Real.exp (-(2 * CG)) / 2 := by
    unfold shellEps0CG
    exact min_le_left _ _
  have h3 : Real.exp (-(2 * CG)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **Residual `hCountGood`, pointwise (STEP A, `resCountGood_pt`).** Binders: `0 < CG`; the sparsity-free numeric clauses
`0 ≤ β` (from the counting exponent of `CountingMeasureConvergenceStmt`, which gives `0 < β`), `0 < ε`,
`ε ≤ shellEps0ZCG` (clauses of `ShellPtPremCG`); the counting membership `ω ∈ countingMeshEventR`; the premise
`FullAdmAt (shellS1CG γ CG)`. Conclusion: the body of `ShellCGResCountGood` after its premises. -/
theorem resCountGood_pt {γ ω₀ α ζ ρ CG CE β ε s₀ r : ℝ} {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) (i : Lemma68Config.Config68)
    (hCG : 0 < CG) (hβ : 0 ≤ β) (hε0 : 0 < ε) (hεS : ε ≤ shellEps0ZCG γ α ω₀ ζ CG)
    (hωc : ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε)
    (hFA : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i) :
    ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ) :=
  Lemma68B1EnvPwG.hCountGood_pw_g S ω i hβ hε0 (hεS.trans (shellEps0ZCG_le_one hCG))
    (countingMeshEventR_counting hωc) hFA

end Lemma68CGResCount
end MatedCRT

#print axioms MatedCRT.Lemma68CGResCount.shellEps0ZCG_le_one
#print axioms MatedCRT.Lemma68CGResCount.resCountGood_pt
