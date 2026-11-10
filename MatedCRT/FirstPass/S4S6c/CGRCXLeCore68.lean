import MatedCRT.FirstPass.LICGRCXLe68
import MatedCRT.FirstPass.S4S6c.CGRCXG2Core68

/-!
# CG-R counting swap under the constant order `C ≤ CG` (fp-S4S6c-cgrcx-le, z5)

Copy of `Lemma68CGRCXG2Core` (CGRCXG2Core68.lean) with the residual `ShellCGResG2CLe` (73a, `C ≤ CG` as a function of the
premises) removed. Its role is taken by the premise `C ≤ CG` of the statement
`LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt` (lead li, decision after q3's trace: `WindowPrevAt` is monotone in `C`, so the
pointwise residual `ShellCGResG2CLe` cannot hold for every `C` allowed by the premises; the existential source of `C ≤ CG`
is request 80a, a chain-level input).

* `ShellOneTestPointwiseCGRXLeStmt 𝒮`: `ShellOneTestPointwiseCGRXStmt` (ShellOneCGRCX68.lean) with the premise `C ≤ CG`
  after `WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C'`.
* `shellOneTestPointwiseCGRXLe_of_g2`: that pointwise statement, from `shellOneTest_at_of_goodEnv_loc_g2`
  (B1GoodEnvLoc68.lean:360), with `hCCG` taken from the premise (in `_g2` it was the residual `hCLe`).
* `shellOneTestOrderAeCGRCXLe_of_open3`: `LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮`, by the almost sure swap of
  `shellOneTestOrderAeCGRCX_of_open2` (CGRCXG2Core68.lean), with `C ≤ CG` passed through.

Binders of the final theorem: `hVG` (Lemma 2.7, frozen), `hTest` (`ShellCGTestEndLoc`, 79a), `hGreen` (`ShellCGResGreen`,
75a), `hWalk` (`ShellCGResWalk`, 75a G1), `hRad` (`ShellCGResG2Rad`, 77a radius cap, existential in `t`), `hCtr`
(`ShellCGResG2Ctr`, 74a centre bound). No binder for `C ≤ CG`.
-/

namespace MatedCRT
namespace Lemma68CGRCXLeCore

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

/-- The CG-R pointwise one-test statement under the constant order `C ≤ CG` (fp-S4S6c-cgrcx-le, z5). Copy of
`ShellOneTestPointwiseCGRXStmt` (ShellOneCGRCX68.lean) with the premise `C ≤ CG` after `WindowPrevAt`. -/
def ShellOneTestPointwiseCGRXLeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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

/-- **The CG-R pointwise producer under `C ≤ CG` through `_g2` (fp-S4S6c-cgrcx-le, z5).** Copy of
`shellOneTestPointwiseCGRX_of_g2` (CGRCXG2Core68.lean) without the residual `hCLe`: the constant order is the premise
`hCCG : C ≤ CG` of the statement, passed to `shellOneTest_at_of_goodEnv_loc_g2` as its `C ≤ CG` argument. -/
theorem shellOneTestPointwiseCGRXLe_of_g2 {𝒮 : SpaceFillingSLEModel}
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮) (hGreen : ShellCGResGreen 𝒮)
    (hWalk : ShellCGResWalk 𝒮) (hRad : ShellCGResG2Rad 𝒮) (hCtr : ShellCGResG2Ctr 𝒮) :
    ShellOneTestPointwiseCGRXLeStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC _hC' _hP hCCG
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
    hCCG
  exact ⟨Rf, h1, h2⟩

#print axioms MatedCRT.Lemma68CGRCXLeCore.shellOneTestPointwiseCGRXLe_of_g2

/-- **The CG-R counting swap under `C ≤ CG` (fp-S4S6c-cgrcx-le, z5).** `LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt` from
`shellOneTestPointwiseCGRXLe_of_g2` by the almost sure swap of `shellOneTestOrderAeCGRCX_of_open2`
(CGRCXG2Core68.lean), with the premise `C ≤ CG` passed through. Binders: `hVG` (Lemma 2.7, frozen) and the residuals
`hTest` (79a), `hGreen` (75a), `hWalk` (75a G1), `hRad` (77a), `hCtr` (74a). -/
theorem shellOneTestOrderAeCGRCXLe_of_open3 {𝒮 : SpaceFillingSLEModel} (hVG : VolumeGrowthStmt)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮) (hGreen : ShellCGResGreen 𝒮)
    (hWalk : ShellCGResWalk 𝒮) (hRad : ShellCGResG2Rad 𝒮) (hCtr : ShellCGResG2Ctr 𝒮) :
    MatedCRT.LICGRCXLe68.ShellOneTestOrderAeCGRCXLeStmt 𝒮 := by
  have h := shellOneTestPointwiseCGRXLe_of_g2 hTest hGreen hWalk hRad hCtr
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP hCCG
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP hCCG
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

#print axioms MatedCRT.Lemma68CGRCXLeCore.shellOneTestOrderAeCGRCXLe_of_open3

end Lemma68CGRCXLeCore
end MatedCRT
