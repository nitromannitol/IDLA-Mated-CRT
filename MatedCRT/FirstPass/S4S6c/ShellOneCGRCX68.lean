import MatedCRT.FirstPass.S4S6c.ShellOneCGRC68
import MatedCRT.FirstPass.LICGRCX68

/-!
# The CG-R counting swap with the exit-time event at the cell radius (fp-S4S6c-cgrcx-producer, z5)

`shellOneTestOrderAeCGRCX_of_open` proves `LICGRCX68.ShellOneTestOrderAeCGRCXStmt` (LICGRCX68.lean, the statement after
request 77b: `ShellOneTestOrderAeCGRCStmt` plus the `PolyHighProb` hypothesis at radius `rhoCell68 ρ` and the almost sure
premise `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε` after the `countingMeshEventR` premise).

The moment residual `ShellCGResMomS` is not a binder here. Its pointwise body is `resMomS_pt` (CGResX1MomS68.lean:97), which
takes the exit membership `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε` and the full admissibility `FullAdmAt`. The exit
membership is the almost sure premise (ii) of the statement. So the pointwise producer
`shellOneTestPointwiseCGRX_of_goodEnv_loc_g` is `shellOneTestPointwiseCGR_of_goodEnv_loc_g` (ShellCoreCG68.lean:496) with
`hmomS` replaced by `resMomS_pt S i hexitω`; its body is otherwise the same. `ShellPtPremCG` is unchanged.

The almost sure swap is `shellOneTestOrderAeCGRC_of_res` (ShellOneCGRC68.lean:65) with the one extra premise, unchanged in
its almost sure facts (`ae_all_iff` over the dyadic windows, the valid-environment regularity, `cutoff_ae`).
The residual binders that remain open are those of `shellOneTestOrderAeCGRC_of_open` (ShellOneCGRC68.lean:76) except
`hmomS`.
-/

namespace MatedCRT
namespace Lemma68ShellOneCGRCX

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

/-- The pointwise CG-R one-test statement with the exit-time event at the cell radius as a further premise: the almost
sure premise `ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε` of `LICGRCX68.ShellOneTestOrderAeCGRCXStmt`, placed after the
membership in `countingMeshEventR`. Its only difference from `ShellOneTestPointwiseCGRStmt` (ShellCoreCG68.lean:104) is that
premise. -/
def ShellOneTestPointwiseCGRXStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ((1 + ρ) / 2)) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
      HarmonicBalls.PolyHighProb S.P (HoneModelInputs68.countingGoodEvent S α β ρ) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ ω : Ω,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        Continuous (S.η ω) → (∀ v : ℂ, S.μ ω {v} = 0) → IsFiniteMeasureOnCompacts (S.μ ω) →
        (∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) →
        (∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty) →
        (∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty) →
        (∃ t : ℝ, 0 < t ∧ ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
          ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ)) →
        (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k)) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **The CG-R pointwise producer with the exit premise (fp-S4S6c-cgrcx-producer).** Copy of
`shellOneTestPointwiseCGR_of_goodEnv_loc_g` (ShellCoreCG68.lean:496) with two changes: the premise
`ω ∈ exitTimeEvent68 S α (rhoCell68 ρ) CE ε` (`hexitω`) is an argument, and the moment residual is the pointwise body
`resMomS_pt S i hexitω` (CGResX1MomS68.lean:97) instead of the binder `hmomS`. The remaining twelve residuals are the
binders of `shellOneTestPointwiseCGR_of_goodEnv_loc_g` except `hmomS`; `hCountGood`, `hRr`, `hx1`, `hstopFin`, `hEl` are
the same as there. -/
theorem shellOneTestPointwiseCGRX_of_goodEnv_loc_g {𝒮 : SpaceFillingSLEModel}
    (hShellLoc : ShellCGResLoc 𝒮) (hEl : ShellCGResEl 𝒮) (hstopFin : ShellCGResStopFin 𝒮)
    (hRr : ShellCGResRr 𝒮) (hVolC : ShellCGResVolC 𝒮) (hVolY : ShellCGResVolY 𝒮)
    (hGreen : ShellCGResGreen 𝒮) (hCountGood : ShellCGResCountGood 𝒮) (hsel : ShellCGResSel 𝒮)
    (hx1 : ShellCGResX1 𝒮) (hWalk : ShellCGResWalk 𝒮) (hPos : ShellCGResPos 𝒮) :
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
  have hcutR := cut_of_hRcut hRcut hr0 hrR
  have hgap := hgapShell_of_rAmp_le hρ1 hζ0 hζ1 hr0 hrA hq
  have hrz := MatedCRT.Lemma68HoneSetupAdapt.hrz_of_rAmp hq0 hq0B hζ0 hζ1 hrA
  have hmesh := cellDiamLe_rhoCell_of_meshEventR (c0 := shellC0 CG) S ω hmeshω.1 hε hρ1 hr0 hrρ
    (shellC0_le_one_cg hCG) hεcell
  have hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω :=
    ⟨meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω.1, hcurve, hmult, hcont, hμN, hμF,
      hdeg, hadj, hadjAll⟩
  have hpre : ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω :=
    ⟨hγ0, hγ2, hω₀, hωα, hα0, hωζ, hωβ, hω2ζ, hCG, hCE, hβ, hζ0, hζ1, hρ0, hρ1, hC, hq0, hq0A, hq0B,
      hR0, hRρ, hRA, hRcut, hs₀, hs₁, hS, hε, hεe, hr10, hrR, hωE, hmeshω, hgap, hcurve, hmult, hcont,
      hμN, hμF, hdeg, hadj, hadjAll, hcutA, hav⟩
  obtain ⟨Rf, h1, h2⟩ := shellOneTest_at_of_goodEnv_loc_g hγ0 hγ2 (shellC0 CG) S hρ0 hρ1 hζ0 hζ1 hCG hq0 hq0B
    hε hs₀ hr0 hrρ hrz hrA ω₀ hω₀ (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) rfl ω hreg i
    hεc hεcell hκ2 hα hεs hrε hε1 hmesh
    (hShellLoc γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    hadm
    (hEl γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hstopFin γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hRr γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (MatedCRT.Lemma68HoneSetupAdapt.hcap_of_continuous_g (s1 := shellS1CG γ CG) S ω hcont hε hr0 i)
    (hVolC γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hVolY γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hGreen γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hCountGood γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (fun _ k' hk => (hmeshω.1.1.2 k' hk).2)
    hcutR
    (hx1 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (MatedCRT.Lemma68CGResX1MomS.resMomS_pt S i hexitω)
    (hWalk γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hsel γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (hPos γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
  exact ⟨Rf, h1, h2⟩

#print axioms MatedCRT.Lemma68ShellOneCGRCX.shellOneTestPointwiseCGRX_of_goodEnv_loc_g

/-- **The CG-R counting swap with the exit-time event at the cell radius (fp-S4S6c-cgrcx-producer, z5).**
`LICGRCX68.ShellOneTestOrderAeCGRCXStmt` from `shellOneTestPointwiseCGRX_of_goodEnv_loc_g` by the almost sure swap of
`shellOneTestOrderAeCGRC_of_res` (ShellOneCGRC68.lean:65). Binders: `hVG` (Lemma 2.7, frozen) and the residual Props that
remain open, as in `shellOneTestOrderAeCGRC_of_open` (ShellOneCGRC68.lean:76) except `hmomS`. Plugged: `ShellCGResEl`,
`ShellCGResStopFin`, `ShellCGResRr`, `ShellCGResCountGood`, `ShellCGResX1` by their unconditional wrappers. The binder
`hShellLoc : ShellCGResLoc 𝒮` is kept as in `_of_open`, although `shellCGResLoc_of_test` is now on HEAD (e41bb17). -/
theorem shellOneTestOrderAeCGRCX_of_open {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt)
    (hShellLoc : ShellCGResLoc 𝒮) (hVolC : ShellCGResVolC 𝒮) (hVolY : ShellCGResVolY 𝒮)
    (hGreen : ShellCGResGreen 𝒮) (hsel : ShellCGResSel 𝒮)
    (hWalk : ShellCGResWalk 𝒮) (hPos : ShellCGResPos 𝒮) :
    MatedCRT.LICGRCX68.ShellOneTestOrderAeCGRCXStmt 𝒮 := by
  have h := shellOneTestPointwiseCGRX_of_goodEnv_loc_g hShellLoc
    (MatedCRT.Lemma68CGResElSel.shellCGResEl_holds 𝒮) (MatedCRT.Lemma68CGResElSel.shellCGResStopFin_holds 𝒮)
    (MatedCRT.Lemma68CGResRr.shellCGResRr_holds 𝒮) hVolC hVolY hGreen
    (MatedCRT.Lemma68CGResCount.shellCGResCountGood_holds 𝒮) hsel
    (MatedCRT.Lemma68CGResX1MomS.shellCGResX1_holds 𝒮) hWalk hPos
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

#print axioms MatedCRT.Lemma68ShellOneCGRCX.shellOneTestOrderAeCGRCX_of_open

end Lemma68ShellOneCGRCX
end MatedCRT
