import MatedCRT.FirstPass.S4S6c.CGRCYCore68
import MatedCRT.FirstPass.S4S6c.ShellChainCGRCYSq68
import MatedCRT.FirstPass.S4S6c.CGResGreenY68
import MatedCRT.FirstPass.S4S6c.CGResWalkG68
import MatedCRT.FirstPass.S4S6c.CGResTestEnd68
import MatedCRT.FirstPass.S4S6c.CGResCtr68
import MatedCRT.FirstPass.S4S6c.CGResCount68

/-!
# The one-test order input with the square premise, with no named input

Produces `Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮` (ShellChainCGRCYSq68.lean:42), the one-test order input whose
radius clause carries the square premise `4 * ε ^ ω₀ ≤ r ^ 2` in addition to `10 * ε ^ ω₀ ≤ r` (request 83a, option (a)).

The walk binder of the split leaf `B1GoodEnvSplit68.shellOneTest_at_of_goodEnv_loc_split` is `CGResWalkG68.walkG_pt_sq`
(CGResWalkG68.lean:117), which takes the square premise `hsq` and no named input. Everything else is the instantiation of
`CGRCYInst68` / `CGRCYCore68.shellOneTestPointwiseCGRY_of_split`: `epsG := shellEpsG68` (positive, CGResGreenY68),
`hTest := shellCGTestEndLoc_holds 𝒮` (CGResTestEnd68), `hCtr := shellCGResG2Ctr_holds 𝒮` (CGResCtr68),
`shellCGResCountGood_holds 𝒮` (CGResCount68). The almost sure swap is the one of `CGRCYCore68.shellOneTestOrderAeCGRCY_of_pointwise`,
copied here with the square premise in the radius clause.

The leaf takes the Green bound from the event premise `ω ∈ greenLowEvent68 S ωG ρ CG ε` (no Green residual); the walk
binder at `ωG` is `walkG_pt_sq`. No `hVG`, no `hCCG`, no `hRad`, no named input.

Terminology: Duplantier-Sheffield (LQG measure, walk exit of an annulus), Armitage-Gardiner (balls, Green function),
Armstrong-Kuusi-Mourrat (good annuli, shell order).
-/

namespace MatedCRT
namespace Lemma68CGRCYSqInst

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

/-- **The one-test order input with the square premise, with no named input.**
`Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮`: the shell one-test at every radius with `10 * ε ^ ω₀ ≤ r`,
`4 * ε ^ ω₀ ≤ r ^ 2`, `r ≤ R`, `ω ∈ Ew (dyadicD r)` and the volume guard, almost surely. The walk is `walkG_pt_sq`;
the test end and the centre bound are the landed `shellCGTestEndLoc_holds` and `shellCGResG2Ctr_holds`. -/
theorem shellOneTestOrderAeCGRCYSq_holds (𝒮 : SpaceFillingSLEModel) :
    Lemma68CGRCYSq.ShellOneTestOrderAeCGRCYSqStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hωG C C' hC hC' hP
  obtain ⟨q0, hq0, hq0A, hq0B, hq⟩ : ∃ q0 : ℝ, 0 < q0 ∧
      q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ∧
      Lemma68Cutoff.rAmp q0 ζ ≤ Real.sqrt ((((Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4)) ^ (1 / shortExp ζ) / 2) := by
    have h1 := one_le_shellChone68 CE C
    have h2 := one_le_shellChone68 CE CG
    have hA : (0 : ℝ) < (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) := div_pos (by norm_num) (by linarith)
    have hB : (0 : ℝ) < (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) := div_pos (by norm_num) (by linarith)
    have hc0 : 0 < (Lemma68HoneCellGood.rhoCell68 ρ - ρ) / 4 := by
      unfold Lemma68HoneCellGood.rhoCell68; linarith
    obtain ⟨q0, hq0, hqm, hr⟩ := exists_q0_rAmp_le hζ0 hc0 (lt_min hA hB)
    exact ⟨q0, hq0, le_trans hqm (min_le_left _ _), le_trans hqm (min_le_right _ _), hr⟩
  refine ⟨q0, MatedCRT.Lemma68CGResGreenY.shellEpsG68 γ α ω₀ ζ CG, hq0,
    MatedCRT.Lemma68CGResGreenY.shellEpsG68_pos γ α ω₀ ζ CG, hq0A, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hGpG hCp hEp hEp' hCntp Ew hEwm hEwp hav ε hε hεe _hεG
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, Lemma68ShellCorePw.ae_null_singleton_of_valid hS,
    Lemma68ShellCorePw.ae_finite_on_compacts_of_valid hS,
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    MatedCRT.Lemma68HoneExitGeom.hadj_of_valid hγ0 hγ2 S hS hε, TraceInputs68.ae_adjacent hγ0 hγ2 S hS]
    with ω hω hηc hμN hμF hdg hadjA hadjAll hmesh hexitω hgreen hcurve hmult
  intro r hr10 hsq hrR hωE hvol i hadm
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hr10
  have hrA : r ≤ Lemma68Cutoff.rAmp q0 ζ := le_trans hrR hRA
  have hrρ : r ≤ ρ / 4 := le_trans hrR hRρ
  obtain ⟨hεc, hε1, hεs⟩ := shellKCG_eps_le (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hεe
  have hεcell := shellKCG_eps_cell (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hε hεe hr10
  obtain ⟨hκ2, hα, hrε⟩ := shellKCG_leaf_ineqs (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) ω₀ α ζ CG
    hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG rfl hω2ζ hωβ hr10
  have hrz := MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp hq0 hq0B hζ0 hζ1 hrA
  have hgap := hgapShell_of_rAmp_le hρ1 hζ0 hζ1 hr0 hrA hq
  have hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω :=
    ⟨MatedCRT.Lemma68ShellCoreCG.meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmesh.1,
      hcurve, hmult, hηc, hμN, hμF, hdg, hadjA, hadjAll⟩
  have hcell := MatedCRT.Lemma68ShellCoreCG.cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmesh.1
    hε hρ1 hr0 hrρ (MatedCRT.Lemma68ShellCoreCG.shellC0_le_one_cg hCG) hεcell
  have hgapM : dyadicD r / 100 ≤ Lemma68HoneCellGood.rhoCell68 ρ - ρ := by
    have h1' := Real.rpow_nonneg (MatedCRT.Lemma68Window.dyadicD_pos r).le (shortExp ζ)
    have h2' := MatedCRT.Lemma68Window.dyadicD_pos r
    linarith
  obtain ⟨t, ht, hcut, hrt⟩ := hvol
  have hpre : ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω :=
    ⟨hγ0, hγ2, hω₀, hωα, hα0, hωζ, hωβ, hω2ζ, hCG, hCE, hβ, hζ0, hζ1, hρ0, hρ1, hC, hq0, hq0A, hq0B,
      hR0, hRρ, hRA, hRcut, hs₀, hs₁, hS, hε, hεe, hr10, hrR, hωE, hmesh, hgap, hcurve, hmult, hηc, hμN, hμF,
      hdg, hadjA, hadjAll, ⟨t, ht, hcut⟩, hω⟩
  obtain ⟨Rf, h1, h2⟩ := MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_split hγ0 hγ2 (shellC0 CG) S
    hρ0 hρ1 hζ0 hζ1 hCG hC hq0 hq0A hq0B hε hs₀ hr0 hrρ hrz hrA ω₀ hω₀ ωG hωG
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) rfl ω hreg i
    hεc hεcell hκ2 hα hεs hrε hε1 hmesh.1 hexitω hadm
    (MatedCRT.Lemma68CGResTestEnd.shellCGTestEndLoc_holds 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    t ht hrt hcut
    (MatedCRT.Lemma68CGResCtr.shellCGResG2Ctr_holds 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    hgreen
    (MatedCRT.Lemma68CGResCount.shellCGResCountGood_holds 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (cut_of_hRcut hRcut hr0 hrR)
    (MatedCRT.Lemma68CGResWalkG.walkG_pt_sq (c0W := shellC0 CG) (α := α) (CE := CE) (C := C) (s₀ := s₀) S ω i
      (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG)
      hγ0 hγ2 hρ0 hρ1 hζ0 hζ1 hCG hω₀ hωG hε hs₀ hr0 hrρ hrz hr10 hreg hcell hgapM hsq)
    rfl (hω (Nat.log 2 ⌊1 / r ^ 2⌋₊) hωE)
  exact ⟨Rf, h1, h2⟩

#print axioms MatedCRT.Lemma68CGRCYSqInst.shellOneTestOrderAeCGRCYSq_holds

end Lemma68CGRCYSqInst
end MatedCRT
