import MatedCRT.FirstPass.S4S6c.ShellCoreCG68
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.CGResElSel68
import MatedCRT.FirstPass.S4S6c.CGResCount68
import MatedCRT.FirstPass.S4S6c.CGResRr68
import MatedCRT.FirstPass.S4S6c.CGResX1MomS68

/-!
# The a.s. counting swap of the CG pointwise producer (fp-S4S6c-cgrc-swap, z5)

`shellOneTestOrderAeCGRC_of_res` proves `ShellOneTestOrderAeCGRCStmt` (ShellHoneInst68.lean:414, the counting one-test
order input with the mesh clause `countingMeshEventR`) from the pointwise producer
`shellOneTestPointwiseCGR_of_goodEnv_loc_g` (ShellCoreCG68.lean), its twelve residual binders `ShellCGRes…`, and the
temporary positivity residual `ShellCGResPos`.

The almost-sure facts are: the countable window avoidance (`ae_all_iff` over `ℕ`), the regularity facts of a valid
environment (`ae_continuous_eta`, `ae_null_singleton_of_valid`, `ae_finite_on_compacts_of_valid`, `ae_adjacent`,
`hdeg_of_valid`, `hadj_of_valid`) and the cutoff (`cutoff_ae`, which needs the volume-growth input `hVG`). The counting mesh
membership `ω ∈ countingMeshEventR` is the a.s. clause of the Stmt itself. No global full support is used.
-/

namespace MatedCRT
namespace Lemma68ShellOneCGRC

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

/-- **The a.s. counting swap of the CG pointwise producer.** `ShellOneTestOrderAeCGRCStmt` from the pointwise producer and its
residual binders (one binder per residual Prop: the twelve `ShellCGRes…` of ShellCoreCG68.lean and the temporary
`ShellCGResPos`). `hVG : VolumeGrowthStmt` is the volume-growth input of the cutoff a.s. fact (Draft/Section2.lean:121). -/
theorem shellOneTestOrderAeCGRC_of_res {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt)
    (hShellLoc : ShellCGResLoc 𝒮) (hEl : ShellCGResEl 𝒮) (hstopFin : ShellCGResStopFin 𝒮)
    (hRr : ShellCGResRr 𝒮) (hVolC : ShellCGResVolC 𝒮) (hVolY : ShellCGResVolY 𝒮)
    (hGreen : ShellCGResGreen 𝒮) (hCountGood : ShellCGResCountGood 𝒮) (hsel : ShellCGResSel 𝒮)
    (hx1 : ShellCGResX1 𝒮) (hmomS : ShellCGResMomS 𝒮) (hWalk : ShellCGResWalk 𝒮)
    (hPos : ShellCGResPos 𝒮) :
    ShellOneTestOrderAeCGRCStmt 𝒮 := by
  have h := shellOneTestPointwiseCGR_of_goodEnv_loc_g hShellLoc hEl hstopFin hRr hVolC hVolY hGreen hCountGood
    hsel hx1 hmomS hWalk hPos
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hCntp Ew hEwm hEwp hav ε hε hεe
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, Lemma68ShellCorePw.ae_null_singleton_of_valid hS,
    Lemma68ShellCorePw.ae_finite_on_compacts_of_valid hS,
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    MatedCRT.Lemma68HoneExitGeom.hadj_of_valid hγ0 hγ2 S hS hε, TraceInputs68.ae_adjacent hγ0 hγ2 S hS,
    Lemma68HVolCutoffAe.cutoff_ae S hS hVG hγ0 hγ2 (β := (2 + γ) ^ 2 / 2 + 1) (by linarith)]
    with ω hω hηc hμN hμF hdg hadjA hadjAll hcutA hmesh hcurve hmult
  exact hcl R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hCntp Ew hEwm hEwp ε hε hεe ω hmesh hcurve hmult
    hηc hμN hμF hdg hadjA hadjAll hcutA (fun k hk => hω k hk)

#print axioms MatedCRT.Lemma68ShellOneCGRC.shellOneTestOrderAeCGRC_of_res

/-- **The counting swap with the landed residual wrappers (`shellOneTestOrderAeCGRC_of_open`, fp-S4S6c-cgrc-swap, step 3).**
`ShellOneTestOrderAeCGRCStmt` (ShellHoneInst68.lean:414) from `shellOneTestOrderAeCGRC_of_res` with the five residuals whose
unconditional wrappers have landed plugged in: `ShellCGResEl`, `ShellCGResStopFin` (`shellCGResEl_holds`,
`shellCGResStopFin_holds`, CGResElSel68.lean, 1f1a4b4), `ShellCGResRr` (`shellCGResRr_holds`, CGResRr68.lean),
`ShellCGResCountGood` (`shellCGResCountGood_holds`, CGResCount68.lean) and `ShellCGResX1` (`shellCGResX1_holds`,
CGResX1MomS68.lean). The binders that stay open are the residual Props not yet discharged: `ShellCGResLoc` (z1),
`ShellCGResVolC`, `ShellCGResVolY` (z9, radius cap 77a), `ShellCGResGreen`, `ShellCGResWalk` (z11, G1 of request 75a),
`ShellCGResSel` (z10, C ≤ CG, request 73a), `ShellCGResMomS` (q3, named premise `ShellCGExitRhoCell`, request 77b), and the
temporary `ShellCGResPos` (q4). The conditional wrappers are not plugged: their extra inputs are open. -/
theorem shellOneTestOrderAeCGRC_of_open {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt)
    (hShellLoc : ShellCGResLoc 𝒮) (hVolC : ShellCGResVolC 𝒮) (hVolY : ShellCGResVolY 𝒮)
    (hGreen : ShellCGResGreen 𝒮) (hsel : ShellCGResSel 𝒮)
    (hmomS : ShellCGResMomS 𝒮) (hWalk : ShellCGResWalk 𝒮) (hPos : ShellCGResPos 𝒮) :
    ShellOneTestOrderAeCGRCStmt 𝒮 :=
  shellOneTestOrderAeCGRC_of_res hVG hShellLoc (MatedCRT.Lemma68CGResElSel.shellCGResEl_holds 𝒮)
    (MatedCRT.Lemma68CGResElSel.shellCGResStopFin_holds 𝒮)
    (MatedCRT.Lemma68CGResRr.shellCGResRr_holds 𝒮) hVolC hVolY hGreen
    (MatedCRT.Lemma68CGResCount.shellCGResCountGood_holds 𝒮) hsel
    (MatedCRT.Lemma68CGResX1MomS.shellCGResX1_holds 𝒮) hmomS hWalk hPos

#print axioms MatedCRT.Lemma68ShellOneCGRC.shellOneTestOrderAeCGRC_of_open

end Lemma68ShellOneCGRC
end MatedCRT
