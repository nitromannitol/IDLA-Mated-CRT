import MatedCRT.FirstPass.S4S6c.CGRCYCore68
import MatedCRT.FirstPass.S4S6c.CGResGreenY68
import MatedCRT.FirstPass.S4S6c.CGResWalkG68
import MatedCRT.FirstPass.S4S6c.CGResTestEnd68
import MatedCRT.FirstPass.S4S6c.CGResCtr68

/-!
# The CG-R split constants instantiated; one named input for the walk

Instantiates the named binders of `Lemma68CGRCYCore.shellOneTestOrderAeCGRCY_of_split` with landed theorems:

* `epsG := shellEpsG68` and `hεG := shellEpsG68_pos` (CGResGreenY68.lean);
* `hTest := shellCGTestEndLoc_holds 𝒮` (CGResTestEnd68.lean);
* `hCtr := shellCGResG2Ctr_holds 𝒮` (CGResCtr68.lean);
* `hWalk`: `ShellCGResWalkY 𝒮 shellEpsG68`, from the single named input `ShellWalkFirstCGStmt 𝒮`.

`ShellWalkFirstCGStmt 𝒮` is the named input of `CGResWalkG68.walkG_pt` (its `hFirst` at `K.ω = ω₀`), closed over the binders
of `ShellCGResWalkY`. Its second conjunct `ε ^ ωG ≤ winRf / 8` is derived (`walkG_full_pt`). Nothing else is named.
The hypotheses of `walkG_pt` (positivity, `r ≤ ρ / 4`, `countThreshold`, `RegularEnvAt68`, the cell-diameter bound,
the gap) are derived from `ShellPtPremCG`, as in `CGRCYCore68.shellOneTestPointwiseCGRY_of_split`.
-/

namespace MatedCRT
namespace Lemma68CGRCYInst

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow
open MatedCRT.Lemma68B1Assembly MatedCRT.Lemma68ShellCoreCG
open MatedCRT.Lemma68ShellOneCGRCX
open MatedCRT.Lemma68CGRCXG2Core
open MatedCRT.LICGRCY68
open MatedCRT.Lemma68CGRCYCore

/-- **Named input (walk exit vertex in ball 0 (ρ - ε ^ ω₀)); not a frozen Prop.** The first conjunct of the
walk binder `hWalk` of the split leaf (`B1GoodEnvSplit68.shellOneTest_at_of_goodEnv_loc_split`, B1GoodEnvSplit68.lean:212),
at the shell exponent `K.ω = ω₀`: the walk exit vertex lies in the cell ball `ball 0 (ρ - ε ^ ω₀)`. Closed over the binders
of `ShellCGResWalkY` (`ShellPtPremCG`, `2 * ω₀ < ωG`, `ε ≤ shellEpsG68`, the Green event at `ωG`, the full admissibility
at the shell). It is the named `hFirst` of `CGResWalkG68.walkG_pt`. -/
def ShellWalkFirstCGStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r ωG : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    2 * ω₀ < ωG → ε ≤ MatedCRT.Lemma68CGResGreenY.shellEpsG68 γ α ω₀ ζ CG →
    ω ∈ MatedCRT.greenLowEvent68 S ωG ρ CG ε →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀))

/-- **The residual `ShellCGResWalkY` from the walk first conjunct.** The second conjunct
`ε ^ ωG ≤ winRf / 8` and the gap come from `CGResWalkG68.walkG_pt` (`walkG_full_pt`, no named input); the first conjunct is
`h`. The premises `ShellPtPremCG` supply the positivity, `r ≤ ρ / 4`, `countThreshold`, `RegularEnvAt68`, the cell-diameter
bound (`cellDiamLe_rhoCell_of_meshEventR`) and the gap, exactly as in `CGRCYCore68.shellOneTestPointwiseCGRY_of_split`. -/
theorem shellCGResWalkY_of_walkFirst {𝒮 : SpaceFillingSLEModel} (h : ShellWalkFirstCGStmt 𝒮) :
    ShellCGResWalkY 𝒮 (fun γ ω₀ α ζ _ CG _ _ _ => MatedCRT.Lemma68CGResGreenY.shellEpsG68 γ α ω₀ ζ CG) := by
  intro γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r ωG Ω _ S Ew ω i hpre hωG hεG hgreen hadm
  have hFirst := h γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r ωG Ω S Ew ω i hpre hωG hεG hgreen
  obtain ⟨hγ0, hγ2, hω₀, -, -, -, -, hω2ζ, hCG, -, -, hζ0, hζ1, hρ0, hρ1, -, hq0, -, hq0B, -, hRρ, hRA, -,
    hs₀, -, -, hε, hεe, hr10, hrR, -, hmeshω, hgap, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll, -, -⟩ := hpre
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hr10
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := le_trans hrR hRA
  have hrz := MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp hq0 hq0B hζ0 hζ1 hrA
  have hεcell := MatedCRT.Lemma68ShellCoreCG.shellKCG_eps_cell
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hε hεe hr10
  have hmesh := MatedCRT.Lemma68ShellCoreCG.cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmeshω.1
    hε hρ1 hr0 hrρ (MatedCRT.Lemma68ShellCoreCG.shellC0_le_one_cg hCG) hεcell
  have hgapM : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    have h1 := Real.rpow_nonneg (MatedCRT.Lemma68Window.dyadicD_pos r).le (shortExp ζ)
    have h2 := MatedCRT.Lemma68Window.dyadicD_pos r
    linarith
  have hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω :=
    ⟨MatedCRT.Lemma68ShellCoreCG.meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω.1,
      hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, hadjAll⟩
  exact MatedCRT.Lemma68CGResWalkG.walkG_pt (α := α) (CE := CE) (C := C) (c0W := shellC0 CG) (s₀ := s₀) S ω i
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG)
    hγ0 hγ2 hρ0 hρ1 hζ0 hζ1 hCG hω₀ hωG hε hs₀ hr0 hrρ hrz hr10 hreg hmesh hgapM hFirst hadm

#print axioms MatedCRT.Lemma68CGRCYInst.shellCGResWalkY_of_walkFirst

/-- The split epsilon `shellEpsG68` is a positive mesh constant (`ShellEpsGPos`). -/
theorem shellEpsGPos_shellEpsG68 :
    ShellEpsGPos (fun γ ω₀ α ζ _ CG _ _ _ => MatedCRT.Lemma68CGResGreenY.shellEpsG68 γ α ω₀ ζ CG) := by
  intro γ _ _ ω₀ α ζ ρ CG CE β ωG
  intros
  exact MatedCRT.Lemma68CGResGreenY.shellEpsG68_pos γ α ω₀ ζ CG

/-- **The CG-R counting swap under the split constants, from the walk first conjunct.**
`LICGRCY68.ShellOneTestOrderAeCGRCYStmt` from the single named input `ShellWalkFirstCGStmt 𝒮`, the landed
test-end and centre-bound theorems, and the landed positivity of `shellEpsG68`. -/
theorem shellOneTestOrderAeCGRCY_of_walkFirst {𝒮 : SpaceFillingSLEModel} (h : ShellWalkFirstCGStmt 𝒮) :
    LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮 :=
  shellOneTestOrderAeCGRCY_of_split
    (fun γ ω₀ α ζ _ CG _ _ _ => MatedCRT.Lemma68CGResGreenY.shellEpsG68 γ α ω₀ ζ CG)
    shellEpsGPos_shellEpsG68
    (MatedCRT.Lemma68CGResTestEnd.shellCGTestEndLoc_holds 𝒮)
    (MatedCRT.Lemma68CGResCtr.shellCGResG2Ctr_holds 𝒮)
    (shellCGResWalkY_of_walkFirst h)

#print axioms MatedCRT.Lemma68CGRCYInst.shellOneTestOrderAeCGRCY_of_walkFirst

end Lemma68CGRCYInst
end MatedCRT
