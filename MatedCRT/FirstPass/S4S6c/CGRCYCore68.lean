import MatedCRT.FirstPass.LICGRCY68
import MatedCRT.FirstPass.S4S6c.CGRCXG2Core68
import MatedCRT.FirstPass.S4S6c.B1GoodEnvSplit68

/-!
# The counting one-test order under the split constants: assembler (fp-S4S6c-cgrcy, z5)

Assembles `LICGRCY68.ShellOneTestOrderAeCGRCYStmt` (lead, a03e347; Codex 19:56 UTC, notes/fp-gaps/
CODEX-idla-hOne-residuals-sol-20261110.md). The good-annulus constant `C` stays free: there is no `C ≤ CG` anywhere.

Three changes relative to the CGRCX interface, and where each one enters:
* (77a, Codex Q2a steps 1-2) the radius clause carries the volume guard `VolReady68 S γ ζ r ω`. The pointwise producer
  destructs it, `obtain ⟨t, ht, hcut, hrt⟩ := hvol`, and passes the four facts to the split leaf. No `ShellCGResG2Rad`.
* (75a) a Green exponent `ωG` with `2 * ω₀ < ωG`, the premise `ω ∈ greenLowEvent68 S ωG ρ CG ε`, and the mesh bound
  `ε ≤ εG`, where `εG` is an explicit positive function of the constants (`epsG`).
* No `hCCG`, no `hCLe`, no `hVG`: the cut comes from `VolReady68`, not from the volume cutoff a.s. (`cutoff_ae`).

Chain: the split leaf `Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_split` (B1GoodEnvSplit68.lean, q4, landed 3b38f40)
gives the pointwise pair; `shellOneTestPointwiseCGRY_of_split` supplies its binders; `shellOneTestOrderAeCGRCY_of_pointwise`
is the almost sure swap.

The leaf (committed f411c6e) takes the Green bound from the event premise `ω ∈ greenLowEvent68 S ωG ρ CG ε` (no Green
residual), and the walk binder at the free exponent `ωG` only in the second conjunct (`ε ^ ωG ≤ window / 8`); the cell ball
keeps `ε ^ ω₀` (= `ε ^ K.ω`). The residual `ShellCGResWalkY` below has exactly this form.

NAMED INPUTS (not yet landed; each replaced by a theorem when it lands):
* `epsG` with `ShellEpsGPos epsG` (z11, `shellEpsG68`, CGResGreenY68.lean).
* `ShellCGResWalkY 𝒮 epsG` (z11, CGResGreenY68.lean).
Residuals taken from other tasks and used unchanged: `ShellCGTestEndLoc` (79a, z1, CGResLoc68.lean:102) and
`ShellCGResG2Ctr` (74a, z9, CGRCXG2Core68.lean:53).
-/

namespace MatedCRT
namespace Lemma68CGRCYCore

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

/-- **Positivity of the mesh constant (named input, z11).** `epsG γ ω₀ α ζ ρ CG CE β ωG` is positive under the hypotheses
of `LICGRCY68.ShellOneTestOrderAeCGRCYStmt` (where `2 * ω₀ < ωG`). -/
def ShellEpsGPos (epsG : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE β ωG : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE → 0 < β →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → 2 * ω₀ < ωG → 0 < epsG γ ω₀ α ζ ρ CG CE β ωG

/-- **Residual of the walk to the cell vertices at the free exponent `ωG` (named input, z11).** The `hWalk` binder of
`shellOneTest_at_of_goodEnv_loc_split`: as `ShellCGResWalk` (ShellCoreCG68.lean:461), with the cell ball `ball 0 (ρ - ε ^ ω₀)`
and the second conjunct `ε ^ ωG ≤ window / 8`, under the premises `2 * ω₀ < ωG`, `ε ≤ epsG …`, `ω ∈ greenLowEvent68 …`. -/
def ShellCGResWalkY (𝒮 : SpaceFillingSLEModel) (epsG : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r ωG : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (Ew : ℝ → Set Ω) (ω : Ω) (i : Lemma68Config.Config68),
    ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω →
    2 * ω₀ < ωG → ε ≤ epsG γ ω₀ α ζ ρ CG CE β ωG → ω ∈ greenLowEvent68 S ωG ρ CG ε →
    Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat ∈
              cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)) ∧
            ε ^ ωG ≤ (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            (windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)
              (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) (shellC0 CG) C (dyadicD r) ω)) k x).toNat))
                (sphere 0 ρ)

/-- The CG-R pointwise statement under the split constants: `ShellOneTestOrderAeCGRCYStmt` with the almost sure premises
replaced by their pointwise form (for each `ω`), and the volume guard `VolReady68` in the radius clause. The cut
`(∃ t, cut)` of the CGRCX pointwise statement is no longer a premise: it is destructed from the guard. -/
def ShellOneTestPointwiseCGRYStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ε ≤ εG → ∀ ω : Ω,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        ω ∈ exitTimeEvent68 S α (Lemma68HoneCellGood.rhoCell68 ρ) CE ε →
        ω ∈ greenLowEvent68 S ωG ρ CG ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        Continuous (S.η ω) → (∀ v : ℂ, S.μ ω {v} = 0) → IsFiniteMeasureOnCompacts (S.μ ω) →
        (∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) →
        (∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty) →
        (∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty) →
        (∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k)) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) → VolReady68 S γ ζ r ω →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **The almost sure swap (fp-S4S6c-cgrcy, z5).** `ShellOneTestOrderAeCGRCYStmt` from its pointwise form. The a.s.
premises used are the continuity of the trace, `μ{v} = 0`, finiteness on compacts, the degree and adjacency facts, and the
dyadic family `hav` (by `ae_all_iff`); none is a residual. No volume cutoff is needed: the cut is in `VolReady68`. -/
theorem shellOneTestOrderAeCGRCY_of_pointwise {𝒮 : SpaceFillingSLEModel} (hPw : ShellOneTestPointwiseCGRYStmt 𝒮) :
    LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hωG C C' hC hC' hP
  obtain ⟨q0, εG, hq0, hεG, hq0c, hcl⟩ :=
    hPw γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hωG C C' hC hC' hP
  refine ⟨q0, εG, hq0, hεG, hq0c, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hGpG hCp hEp hEp' hCntp Ew hEwm hEwp hav ε hε hεe hεG'
  have hdy : ∀ᵐ ω ∂S.P, ∀ k : ℕ, ω ∈ Ew ((1 / 2 : ℝ) ^ k) →
      ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C ((1 / 2 : ℝ) ^ k) :=
    ae_all_iff.mpr fun k => hav ((1 / 2 : ℝ) ^ k)
  filter_upwards [hdy, TraceInputs68.ae_continuous_eta hS, Lemma68ShellCorePw.ae_null_singleton_of_valid hS,
    Lemma68ShellCorePw.ae_finite_on_compacts_of_valid hS,
    MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid hγ0 hγ2 S hS hε,
    MatedCRT.Lemma68HoneExitGeom.hadj_of_valid hγ0 hγ2 S hS hε, TraceInputs68.ae_adjacent hγ0 hγ2 S hS]
    with ω hω hηc hμN hμF hdg hadjA hadjAll hmesh hexitω hgreen hcurve hmult
  exact hcl R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω S hS hGp hGpG hCp hEp hEp' hCntp Ew hEwm hEwp ε hε hεe hεG' ω
    hmesh hexitω hgreen hcurve hmult hηc hμN hμF hdg hadjA hadjAll (fun k hk => hω k hk)

#print axioms MatedCRT.Lemma68CGRCYCore.shellOneTestOrderAeCGRCY_of_pointwise

/-- **The CG-R pointwise producer under the split constants (fp-S4S6c-cgrcy, z5).** From the landed split leaf
`Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_split` (B1GoodEnvSplit68.lean). The volume guard is destructed
(`obtain ⟨t, ht, hcut, hrt⟩ := hvol`), the cut for `ShellPtPremCG` is `⟨t, ht, hcut⟩`, and the leaf's binders are supplied
as in `shellOneTestPointwiseCGRX_of_g2` (CGRCXG2Core68.lean), with the walk residual at `ωG`. No `hCCG`, no `hRad`. -/
theorem shellOneTestPointwiseCGRY_of_split {𝒮 : SpaceFillingSLEModel}
    (epsG : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (hεG : ShellEpsGPos epsG)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮)
    (hCtr : ShellCGResG2Ctr 𝒮) (hWalk : ShellCGResWalkY 𝒮 epsG) :
    ShellOneTestPointwiseCGRYStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 ωG hωG C C' hC _hC' _hP
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
  refine ⟨q0, epsG γ ω₀ α ζ ρ CG CE β ωG,
    hq0, hεG γ hγ0 hγ2 ω₀ α ζ ρ CG CE β ωG hω₀ hωα hα0 hωζ hωβ hω2ζ hCG hCE hβ hζ0 hζ1 hρ0 hρ1 hωG,
    hq0A, ?_⟩
  intro R hR0 hRρ hRA hRcut s₀ hs₀ hs₁ Ω _ S hS hGp hGpG hCp hEp hEp' hCntp Ew hEwm hEwp ε hε hεe hεG' ω
    hmeshω hexitω hgreen hcurve hmult hcont hμN hμF hdeg hadj hadjAll hav r hr10 hrR hωE hvol i hadm
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
    ⟨meshEventR_sub_meshEvent S (by linarith : ρ ≤ (1 + ρ) / 2) hmeshω.1, hcurve, hmult, hcont, hμN, hμF,
      hdeg, hadj, hadjAll⟩
  obtain ⟨t, ht, hcut, hrt⟩ := hvol
  have hpre : ShellPtPremCG 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r S Ew ω :=
    ⟨hγ0, hγ2, hω₀, hωα, hα0, hωζ, hωβ, hω2ζ, hCG, hCE, hβ, hζ0, hζ1, hρ0, hρ1, hC, hq0, hq0A, hq0B,
      hR0, hRρ, hRA, hRcut, hs₀, hs₁, hS, hε, hεe, hr10, hrR, hωE, hmeshω, hgap, hcurve, hmult, hcont,
      hμN, hμF, hdeg, hadj, hadjAll, ⟨t, ht, hcut⟩, hav⟩
  obtain ⟨Rf, h1, h2⟩ := MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_split hγ0 hγ2 (shellC0 CG) S
    hρ0 hρ1 hζ0 hζ1 hCG hC hq0 hq0A hq0B hε hs₀ hr0 hrρ hrz hrA ω₀ hω₀ ωG hωG
    (shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω₀ hζ0 hζ1 hCG) rfl ω hreg i
    hεc hεcell hκ2 hα hεs hrε hε1 hmeshω.1 hexitω hadm
    (hTest γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    t ht hrt hcut
    (hCtr γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    hgreen
    (MatedCRT.Lemma68CGResCount.shellCGResCountGood_holds 𝒮 γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r Ω S Ew ω i hpre)
    (cut_of_hRcut hRcut hr0 hrR)
    (hWalk γ ω₀ α ζ ρ CG CE β C q0 R s₀ ε r ωG Ω S Ew ω i hpre hωG hεG' hgreen)
    rfl (hav (Nat.log 2 ⌊1 / r ^ 2⌋₊) hωE)
  exact ⟨Rf, h1, h2⟩

#print axioms MatedCRT.Lemma68CGRCYCore.shellOneTestPointwiseCGRY_of_split

/-- **The CG-R counting swap under the split constants (fp-S4S6c-cgrcy, z5).** `LICGRCY68.ShellOneTestOrderAeCGRCYStmt`
from the split leaf through the pointwise producer and the a.s. swap.

Final binders: `epsG` and `hεG` (the walk mesh constant and its positivity, z11), `hTest` (test end, 79a, z1), `hCtr`
(centre bound, 74a, z9), `hWalk` (75a G1 at `ωG`, z11). No `hVG`, no `hCCG`, no `hRad`, no Green residual (the Green bound is
the event premise), no leaf binder (the split leaf is landed, B1GoodEnvSplit68.lean). -/
theorem shellOneTestOrderAeCGRCY_of_split {𝒮 : SpaceFillingSLEModel}
    (epsG : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (hεG : ShellEpsGPos epsG)
    (hTest : MatedCRT.Lemma68CGResLoc.ShellCGTestEndLoc 𝒮)
    (hCtr : ShellCGResG2Ctr 𝒮) (hWalk : ShellCGResWalkY 𝒮 epsG) :
    LICGRCY68.ShellOneTestOrderAeCGRCYStmt 𝒮 :=
  shellOneTestOrderAeCGRCY_of_pointwise
    (shellOneTestPointwiseCGRY_of_split epsG hεG hTest hCtr hWalk)

#print axioms MatedCRT.Lemma68CGRCYCore.shellOneTestOrderAeCGRCY_of_split

end Lemma68CGRCYCore
end MatedCRT
