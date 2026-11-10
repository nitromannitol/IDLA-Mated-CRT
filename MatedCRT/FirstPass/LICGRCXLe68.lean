import MatedCRT.FirstPass.LICGRCX68

/-!
# The counting one-test order input under the constant order `C ≤ CG` (lead li, round 78, request 80a)

`ShellOneTestOrderAeCGRCXLeStmt` is `ShellOneTestOrderAeCGRCXStmt` (LICGRCX68.lean) with one extra premise `C ≤ CG`
right after `WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C'`. Nothing else changes.

Why (round 78 of lead li): the `_g2` producer (z5, CGRCXG2Core68.lean) needs `C ≤ CG` at its `hCCG` binder. The pointwise
residual `ShellCGResG2CLe` asks it for every window constant `C` admitted by the premises, but `WindowPrevAt` is
monotone in `C` (q3's trace, reports/q3.md 19:30 UTC), so that residual cannot hold for all such `C`. The constant order
belongs at the call site of the chain, where `C` is chosen: there it is the existential input of request 80a (window
prevalence with a constant `C ≤ CG`). This file only states the weaker interface; producer and chain variants are tasks.
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace LICGRCXLe68

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The counting one-test order input under `C ≤ CG` (lead li, request 80a).** Copy of
`LICGRCX68.ShellOneTestOrderAeCGRCXStmt` with the extra premise `C ≤ CG` after `WindowPrevAt`. -/
def ShellOneTestOrderAeCGRCXLeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' → C ≤ CG →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- The form without the constant order implies the new one (the new one only has one more premise). -/
theorem shellOneTestOrderAeCGRCXLe_of_CGRCX (𝒮 : SpaceFillingSLEModel)
    (h : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) : ShellOneTestOrderAeCGRCXLeStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 C C' hC hC' hW _hCG
  exact h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 C C' hC hC' hW

end LICGRCXLe68
end MatedCRT
