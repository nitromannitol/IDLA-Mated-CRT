import MatedCRT.FirstPass.S4S6c.ShellOneCGRCX68
import MatedCRT.FirstPass.S4S6c.B1GoodEnvLoc68
import MatedCRT.FirstPass.S4S6c.CGResLoc68

/-!
# CG-R counting swap with the `_g2` producer

`MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_g2` (B1GoodEnvLoc68.lean:360) has no `hShellLoc`, `hEl`,
`hstopFin`, `hRr`, `hVolC`, `hVolY`, `hsel`, `hPos`, `hx1`, `hcap`, `hCellGood` binders: they are discharged inside it.
Here its remaining binders are supplied as follows.
* From the `ShellPtPremCG` clauses and the exit premise: the moment binder `hmomS` is `resMomS_pt S i hexitω`.
* From the landed wrappers: `hCountGood` (`shellCGResCountGood_holds`), `hcutR` (`cut_of_hRcut`).
* `hwin` is the Stmt premise `hav` at `k = Nat.log 2 ⌊1/r²⌋₊`, since `dyadicD r = (1/2)^k` by definition.
* `hKc0` is `rfl` (`shellKCG` has `c0 = exp(-2CG)/32 = shellC0 CG`, `C = CG`, `ω = ω₀`, `βm = (2+γ)²/2+1`).
* `hmeshω.1` is `hωR`, `hadm` is `hadm`.
The binders not supplied this way are named residual Props, one per open request:
`ShellCGTestEndLoc` (79a, existing), `ShellCGResGreen` (75a Green scale, existing), `ShellCGResWalk` (75a G1, existing),
`ShellCGResG2Rad` (77a radius cap, new), `ShellCGResG2Ctr` (74a exit-vertex centre bound, new),
`ShellCGResG2CLe` (73a `C ≤ CG`, new).
-/

namespace MatedCRT
namespace Lemma68CGRCXG2Core

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

/-- **Residual `77a` (radius cap, new; open math).** At a `FullAdmAt` point of `ShellPtPremCG`, some cutoff radius `t > 0`
carries the volume cut `δ^((2+γ)²/2+1) ≤ μ(B(z,δ))` for `δ < t`, `z ∈ B(0,1-δ)`, and the radius cap
`r ≤ (t/(8·2^{shortExp ζ}))^{1/(1+ζ)}`. The form is existential in `t`: the universal form `∀ t, cut t → r ≤ cap t` is
refutable, since the cut is monotone in `t` (a valid `t` gives valid `t' < t`) and `cap t' → 0`. -/
def ShellCGResG2Rad (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∃ t : ℝ, 0 < t ∧
        (∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
          ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) ∧
        r ≤ (t / (8 * 2 ^ shortExp ζ)) ^ (1 / (1 + ζ))

/-- **Residual `74a` (exit-vertex centre bound, new).** The `hc` binder of `shellOneTest_at_of_goodEnv_loc_g2`: the
exit vertex of a leaf path lies within `1 - windowRf(centre)/4` of the origin. -/
def ShellCGResG2Ctr (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat)‖ <
            1 - windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω (shellCentre ε (S.η ω)
              (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4

/-- **Residual `73a` (`C ≤ CG`, new; open).** The binder `hCCG` of `shellOneTest_at_of_goodEnv_loc_g2` (used by
`hsel_fixedOmega_g`). Not a consequence of the premises of `ShellOneTestPointwiseCGRXStmt`: `WindowPrevAt` bounds the
bad-window probability and does not bound `C`. -/
def ShellCGResG2CLe (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i → C ≤ CG

/-- **The CG-R pointwise producer through `_g2`.** `ShellOneTestPointwiseCGRXStmt` from
`shellOneTest_at_of_goodEnv_loc_g2`, with the binders listed in the module docstring. Copy of
`shellOneTestPointwiseCGRX_of_goodEnv_loc_g` (ShellOneCGRCX68.lean) with the call replaced. The cutoff radius `t` and the
cut `hcut` come from `ShellCGResG2Rad`, not from the Stmt premise `(∃ t, cut)`, which is therefore unused. -/
theorem shellOneTestPointwiseCGRX_of_g2 {𝒮 : SpaceFillingSLEModel}
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮) (hGreen : ShellCGResGreen 𝒮)
    (hWalk : ShellCGResWalk 𝒮) (hRad : ShellCGResG2Rad 𝒮) (hCtr : ShellCGResG2Ctr 𝒮)
    (hCLe : ShellCGResG2CLe 𝒮) :
    ShellOneTestPointwiseCGRXStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC _hC' _hP
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
  refine ⟨q0, hq0, hq0A, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hCntp Ew hEwm hEwp ε hε hεe ω hmeshω hexitω hcurve hmult
    hcont hμN hμF hdeg hadj hadjAll hcutA hav r hr10 hrR hωE i hadm
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)) hr10
  have hr1 : r ≤ 1 := by linarith
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
    ⟨meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω.1, hcurve, hmult, hcont, hμN, hμF,
      hdeg, hadj, hadjAll⟩
  have hpre : ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω :=
    ⟨hγ0, hγ2, hω₀, hωα, hα0, hωζ, hωβ, hω2ζ, hCG, hCE, hβ, hζ0, hζ1, hρ0, hρ1, hC, hq0, hq0A, hq0B,
      hR0, hRρ, hRA, hRcut, hs₀, hs₁, hS, hε, hεe, hr10, hrR, hωE, hmeshω, hgap, hcurve, hmult, hcont,
      hμN, hμF, hdeg, hadj, hadjAll, hcutA, hav⟩
  obtain ⟨t, ht, hcut, hrt⟩ := hRad γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre hadm
  obtain ⟨Rf, h1, h2⟩ := MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_g2 hγ0 hγ2 (shellC0 CG) S
    hρ0 hρ1 hζ0 hζ1 hCG hq0 hq0B hε hs₀ hr0 hrρ hrz hrA ω₀ hω₀
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) rfl ω hreg i
    hεc hεcell hκ2 hα hεs hrε hε1 hmeshω.1 hadm
    (hTest γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    t ht hrt hcut
    (hCtr γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hGreen γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (MatedCRT.Lemma68CGResCount.shellCGResCountGood_holds 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (cut_of_hRcut hRcut hr0 hrR)
    (MatedCRT.Lemma68CGResX1MomS.resMomS_pt S i hexitω)
    (hWalk γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    rfl (hav (Nat.log 2 ⌊1 / r ^ 2⌋₊) hωE)
    (hCLe γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre hadm)
  exact ⟨Rf, h1, h2⟩

#print axioms MatedCRT.Lemma68CGRCXG2Core.shellOneTestPointwiseCGRX_of_g2

/-- **The CG-R counting swap through `_g2`.** `LICGRCX68.ShellOneTestOrderAeCGRCXStmt` from
`shellOneTestPointwiseCGRX_of_g2` by the almost sure swap of `shellOneTestOrderAeCGRCX_of_open` (ShellOneCGRCX68.lean:158).
Binders: `hVG` (Lemma 2.7, frozen) and the residuals `hTest` (79a), `hGreen` (75a), `hWalk` (75a G1), `hRad` (77a),
`hCtr` (74a), `hCLe` (73a). -/
theorem shellOneTestOrderAeCGRCX_of_open2 {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮) (hGreen : ShellCGResGreen 𝒮)
    (hWalk : ShellCGResWalk 𝒮) (hRad : ShellCGResG2Rad 𝒮) (hCtr : ShellCGResG2Ctr 𝒮)
    (hCLe : ShellCGResG2CLe 𝒮) :
    MatedCRT.LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮 := by
  have h := shellOneTestPointwiseCGRX_of_g2 hTest hGreen hWalk hRad hCtr hCLe
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp _hEpR hCntp Ew hEwm hEwp hav ε hε hεe
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, Lemma68ShellCorePw.ae_null_singleton_of_valid hS,
    Lemma68ShellCorePw.ae_finite_on_compacts_of_valid hS,
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    MatedCRT.Lemma68HoneExitGeom.hadj_of_valid hγ0 hγ2 S hS hε, TraceInputs68.ae_adjacent hγ0 hγ2 S hS,
    Lemma68HVolCutoffAe.cutoff_ae S hS hVG hγ0 hγ2 (β := (2 + γ) ^ 2 / 2 + 1) (by linarith)]
    with ω hω hηc hμN hμF hdg hadjA hadjAll hcutA hmesh hexitω hcurve hmult
  exact hcl R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hCntp Ew hEwm hEwp ε hε hεe ω hmesh hexitω hcurve
    hmult hηc hμN hμF hdg hadjA hadjAll hcutA (fun k hk => hω k hk)

#print axioms MatedCRT.Lemma68CGRCXG2Core.shellOneTestOrderAeCGRCX_of_open2

end Lemma68CGRCXG2Core
end MatedCRT
