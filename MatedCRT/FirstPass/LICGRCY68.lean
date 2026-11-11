import MatedCRT.FirstPass.LICGRCX68

/-!
# The counting one-test order input, split-constant successor

`ShellOneTestOrderAeCGRCYStmt` is `LICGRCX68.ShellOneTestOrderAeCGRCXStmt` with three changes:

* The radius clause carries the volume guard `VolReady68 S γ ζ r ω` after `ω ∈ Ew (dyadicD r)`;
  the chain supplies it from the final random cutoff (field-measurable volume cutoff `tVol`).
* (75a) the lower Green bound is also available at a Green exponent `ωG` independent of the shell exponent `ω₀`, with
  `2 * ω₀ < ωG`: a `PolyHighProb` hypothesis for `greenLowEvent68 S ωG ρ CG` and the almost sure premise
  `ω ∈ greenLowEvent68 S ωG ρ CG ε`; the conclusion may shrink the mesh range by a constant `εG > 0` (`ε ≤ εG`).
* The good-annulus constant `C` stays free (split constants, Q4): no comparison of `C` with the Green constant `CG`.
  The route `LICGRCXLe68` (premise `C ≤ CG`) is retired: its witness `WindowPrevLeCGStmt` is false.
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace LICGRCY68

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **Volume readiness of a shell radius.** Some cutoff radius `t > 0` carries the volume lower bound
`δ^((2+γ)²/2+1) ≤ μ(B(z,δ))` for `δ < t`, `z ∈ B(0,1-δ)`, and the shell radius `r` is below the cap
`(t/(8·2^{shortExp ζ}))^{1/(1+ζ)}`. Same body as the conclusion of `ShellCGResG2Rad` (CGRCXG2Core68.lean:41). -/
def VolReady68 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ζ r : ℝ) (ω : Ω) : Prop :=
  ∃ t : ℝ, 0 < t ∧
    (∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) ∧
    r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ))

/-- **The counting one-test order input, split-constant successor.** Copy of
`LICGRCX68.ShellOneTestOrderAeCGRCXStmt` with the Green exponent `ωG` (`2 * ω₀ < ωG`, its `PolyHighProb` hypothesis
and almost sure premise, mesh range `ε ≤ εG`) and the volume guard `VolReady68 S γ ζ r ω`. -/
def ShellOneTestOrderAeCGRCYStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → ∀ ωG : ℝ, 2 * ω₀ < ωG →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 εG : ℝ, 0 < q0 ∧ 0 < εG ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ωG ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ε ≤ εG → ∀ᵐ ω ∂S.P,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
        ω ∈ greenLowEvent68 S ωG ρ CG ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) → VolReady68 S γ ζ r ω →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- The successor only adds premises (and `εG := 1`), so the CGRCX form implies it. -/
theorem shellOneTestOrderAeCGRCY_of_CGRCX (𝒮 : SpaceFillingSLEModel)
    (h : LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮) : ShellOneTestOrderAeCGRCYStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 ωG _hωG C C' hC hC' hW
  obtain ⟨q0, hq0, hq0c, hR⟩ := h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 C C' hC hC' hW
  refine ⟨q0, 1, hq0, one_pos, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp _hGp' hCp hEp hEp' hKp Ew hEwm hEwp hav ε hε hle _hle'
  refine (hR R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hEp' hKp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hexit _hgreen hcurve hmult r hr1 hr2 hωE _hvol i hi
  exact hω hmesh hexit hcurve hmult r hr1 hr2 hωE i hi

end LICGRCY68
end MatedCRT
