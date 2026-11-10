import MatedCRT.FirstPass.S4S6c.ShellChainCGRCX68
import MatedCRT.FirstPass.LICGRCXLe68

/-!
# The X counting CG chain under the constant order `C ≤ CG` (fp-S4S6c-chain-le, lead li, request 80a)

Copy of the X chain of `ShellChainCGRCX68.lean` in which the one-test input is
`LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt` (the premise `C ≤ CG` after `WindowPrevAt`) and the prevalence input is
`WindowPrevLeCGStmt` (a window constant with `C ≤ CG`). The chain statement `ShellChainCGRCXStmt`, the guard
`guardProbStmtCGRCX_of_chainCGRCX` and `uniformConstantOrderLowerBoundCGRCX_of_chain` do not mention `C`, so they are
reused from `ShellChainCGRCX68.lean`.

`WindowPrevLeCGStmt` is open mathematics (the residual of request 80a, reports/q3.md), not a frozen input.
Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Armitage-Gardiner (balls).
-/

open MeasureTheory Filter Set HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CGRCXLe

open MatedCRT.Lemma68Window MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10
open MatedCRT.Lemma68ConstOrder DyadicCutoff68 Lemma68Window
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellHoneInst
open MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The window constant with `C ≤ CG` (residual of request 80a, lead li).** For `γ`, `ζ`, `CG` in the ranges of the
chain there are window constants `0 < C ≤ CG` and `C'` with `WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C'`. This is
`ShortWindowGoodRadiusPrevalenceStmt` (S6r/ShortWindow.lean:61) at `a = shortExp ζ`, `c₀ = shellC0 CG`, with the extra bound
`C ≤ CG`, which the repository does not give (q3 trace, reports/q3.md). Open mathematics: NOT a frozen input. -/
def WindowPrevLeCGStmt : Prop :=
  ∀ γ ζ CG : ℝ, 0 < γ → γ < 2 → 0 < shortExp ζ → shortExp ζ < 1 → 0 < CG →
    ∃ C C' : ℝ, 0 < C ∧ C ≤ CG ∧ 0 < C' ∧ WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C'

/-- **`ShellChainCoreCGRCXStmt` under `C ≤ CG` (request 80a).** The core `ShellChainCoreCGRCXStmt`
(ShellChainCGRCX68.lean:39) with the extra premise `C ≤ CG` after `WindowPrevAt`; the conclusion is unchanged. -/
def ShellChainCoreCGRCXLeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
            ∃ N : ℕ, countConst ζ * r ^ (-ζ) ≤ (N : ℝ) ∧
              Lemma68Config.exitQ S ε ω r i ≤ (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N

/-- **`ShellChainCoreCGRCXLeStmt` from the X one-test order input (fp-S4S6c-cgrcx-closures).** Copy of
`shellChainCoreCGRCStmt_of_oneTestOrderCGRC` (ShellHoneInst68.lean:448) with the extra exit clause passed through. -/
theorem shellChainCoreCGRCXLe_of_oneTestOrderCGRCXLe {𝒮 : SpaceFillingSLEModel}
    (h : LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮) : ShellChainCoreCGRCXLeStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP hCC
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP hCC
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hEr hKp Ew hEwm hEwp hav ε hε hle
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hEr hKp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hexit hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hexit hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2


/-- **`ShellChainCGRCXStmt` from the X counting core under `C ≤ CG` (request 80a).** Copy of `shellChainCGRCX_of_core`
(ShellChainCGRCX68.lean:122) with `hprevLe` in place of `hprev`: the window constant `C` and its bound `C ≤ CG` come from one
existential. -/
theorem shellChainCGRCXLe_of_core {𝒮 : SpaceFillingSLEModel} (hprevLe : WindowPrevLeCGStmt)
    (hcore : ShellChainCoreCGRCXLeStmt 𝒮) : Lemma68CGRCX.ShellChainCGRCXStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1
  have ha0 : 0 < shortExp ζ := by unfold shortExp; linarith
  have ha1 : shortExp ζ < 1 := by unfold shortExp; linarith
  obtain ⟨C, C', hC0, hCC, hC'0, hP⟩ := hprevLe γ ζ CG hγ0 hγ2 ha0 ha1 hCG
  have hP' : WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' := hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    hcore γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC0 hC'0 hP' hCC
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq1, fun R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hEr hKp => ?_⟩
  obtain ⟨Ew, hEwm, hEwp, hav⟩ :=
    shortWindow_fieldFamily_at hγ0 hγ2 S hS (shortExp ζ) (shellC0 CG) C C' ρ hρ0 hρ1 hP'
  exact ⟨Ew, hEwm, hEwp, hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hEr hKp Ew hEwm hEwp hav⟩


/-- **`hU` from the X counting core under `C ≤ CG` (request 80a).** Copy of `hU_of_core_cgRCX`
(ShellChainCGRCX68.lean:245), with `hprevLe` for the prevalence input. -/
theorem hU_of_core_cgRCXLe {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮) (hprevLe : WindowPrevLeCGStmt)
    (hcore : ShellChainCoreCGRCXLeStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68CGRCX.uniformConstantOrderLowerBoundCGRCX_of_chain 𝒮 hG hC hK (shellChainCGRCXLe_of_core hprevLe hcore)

end Lemma68CGRCXLe

namespace Lemma68ShellTopCGRCXLe

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the X counting CG one-test order input under `C ≤ CG`
(request 80a).** Copy of `hU_top_cgRCX` (ShellChainCGRCX68.lean:256) with the prevalence inputs `hLit hBM hCC hB1 hμ`
replaced by `hprevLe`, and `hOne` by `hOneXLe`. -/
theorem hU_top_cgRCXLe {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : MatedCRT.Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hprevLe : MatedCRT.Lemma68CGRCXLe.WindowPrevLeCGStmt)
    (hOneXLe : MatedCRT.LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68CGRCXLe.hU_of_core_cgRCXLe hG hC hK hprevLe
    (Lemma68CGRCXLe.shellChainCoreCGRCXLe_of_oneTestOrderCGRCXLe hOneXLe)

end Lemma68ShellTopCGRCXLe
end MatedCRT

#print axioms MatedCRT.Lemma68ShellTopCGRCXLe.hU_top_cgRCXLe
