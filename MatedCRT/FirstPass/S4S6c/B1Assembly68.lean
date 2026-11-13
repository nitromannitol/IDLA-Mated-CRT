import MatedCRT.FirstPass.S4S6c.HoneLeafAe68
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.BallExitMeas68
import MatedCRT.FirstPass.S4S6c.FiniteExitMoment68
import MatedCRT.Audit.StatementsSec3Sec5M1
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.ShellOrderWindow68
import MatedCRT.FirstPass.S4S6c.ShellConstants68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S6e.Geometry
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68
import MatedCRT.FirstPass.S4S6c.HoneGoodEventAe68
import MatedCRT.FirstPass.S4S6c.HoneSetup68
import MatedCRT.FirstPass.S4S6c.HoneSetup239_68
import MatedCRT.FirstPass.S4S6c.ShellOrderPw68
import MatedCRT.FirstPass.S4S6c.ShellHdePw68
import MatedCRT.FirstPass.S4S6c.WindowRfGlobal68
import MatedCRT.FirstPass.S4S6c.WalkLoc68

/-!
# The one-test bound and the shell order at one radius, at one regular environment

`shellOneTest_at_of_goodEnv_loc` gives, at one radius `r` and at one environment `ω` with `RegularEnvAt68`, the two
conjuncts of the B1 conclusion `ShellOneTestOrderAeStmt` (ShellHoneInst68.lean:159): the one-test bound `ShellOneTestAt`
and the shell order `ShellOrderAe`, for the window radius `Rf = winRf S ρ ζ C r ω` of the environment `ω`. The one-test
bound is the leaf `shellOneTest_of_direct_ae_rcell_stopFin_rho` (HoneLeafAe68.lean) at `ω`, with `m := S.mult ε ω`,
`η := S.η ω`, `μ := S.μ ω`, `Kset := fillCells ε (S.η ω) i.Θ` and `τU := vExitTime (killed …)`; the shell order is the
localized producer `hShellLoc`. `shellOneTest_at_of_goodEnv_loc_g` is the same statement with a free window constant
`c0W`.

Terminology: Armstrong-Kuusi-Mourrat (shells, one-test bound), Armitage-Gardiner (exit times of balls).
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68B1Assembly

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder MatedCRT.Lemma68ShellConstants
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst MatedCRT.Lemma68WindowRf MatedCRT.Lemma68ShellOrderWindow

/-- **The `hmult` fact of the window route, for a valid environment.** This is `hmult_of_valid68`
(WindowMult68.lean:34), re-proved here because WindowMult68 does not build at HEAD: its
`exitQ_core_ae_window_noMult` passes `hstart` without the `FullAdm` guard that ec953d8 added. -/
theorem hmult_ae_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := by
  filter_upwards [Uniform68Env.ae_envInputs hγ0 hγ2 hS] with ω hω
  obtain ⟨hlf, hsucc, -⟩ := Uniform68Env.envAt S hε ω hω.1 hω.2.1 hω.2.2
  exact ⟨hlf, hsucc⟩

/-- The window radius at the environment `ω`: `windowRfT` with `c₀ = shellC068` and `d = dyadicD r`. -/
noncomputable def winRf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ζ C r : ℝ) (ω : Ω) : ℂ → ℝ :=
  windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω

/-- The walk-prefix set of the leaf `shellOneTest_of_direct` at the shell `k`: `prefixSet` with `τU = vExitTime (killed …)`. -/
noncomputable def leafPre (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (r s d : ℝ) (Rf : ℂ → ℝ) (k : ℕ) :
    Set (ℕ → ℤ) :=
  prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) (↑A : Set ℤ) (shellExit ε η (fillCells ε η ↑Θ) r s d Rf k)
    (vExitTime (killed ε η Θ F0 r))

/-- **The regular environment at one environment `ω` and one scale `ε`.** The r-free
almost-sure inputs of the B1 assembly, gathered at `ω`: the eps-event `ω ∈ meshEvent` (Green lower bound, cell size and
exit time at `ε`), the curve escapes both ends, the multiplicities are locally finite with consecutive edges (every
`ε'`), `η ω` is continuous, `μ ω` has no atoms and is finite on compacts, and the degree and closed-cell adjacency
facts of `hb` hold at `ε`, and the open cells of adjacent edges meet at every `ε'` (`Lemma68ShellEnvAe.map_cells_meet_ae`,
the input of the pointwise shell order). Each field is almost surely true for a valid environment (`hdeg_of_valid`,
`hadj_of_valid`, `TraceInputs68.ae_continuous_eta`, `ae_null_singleton_of_valid`, `ae_finite_on_compacts_of_valid`,
`map_cells_meet_ae`). -/
def RegularEnvAt68 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ω₀ ρ CG ζ α CE ε : ℝ) (ω : Ω) : Prop :=
  ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε ∧ Lemma68Inputs.CurveEscapesBothEnds (S.η ω) ∧
    (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) ∧
    Continuous (S.η ω) ∧ (∀ v : ℂ, S.μ ω {v} = 0) ∧ IsFiniteMeasureOnCompacts (S.μ ω) ∧
    (∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤) ∧
    (∀ u v : ℤ, S.mult ε ω u v ≠ 0 → (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty) ∧
    (∀ ε' : ℝ, 0 < ε' → ∀ u v : ℤ, S.mult ε' ω u v ≠ 0 → (cell ε' (S.η ω) u ∩ cell ε' (S.η ω) v).Nonempty)

#print axioms MatedCRT.Lemma68HoneExitGeom.hb_ae_valid_centre_mesh

open Classical in
/-- **The one-test bound and the shell order at one radius, at one regular environment, with the exit mesh localized to a ball
and the walk exponent split.** This is the canonical CG route
(`ShellOneTestOrderAeCGStmt`, ShellHoneInst68.lean): the leaf constant is `K = shellKCG … CG` (`hK`), and the statement is
kept at this `K` (`K.C = CG`, `K.c0 = c₀(CG)`, `K.s1 = shellS1CG γ CG`).
* the mesh `hmesh` is the ball mesh at radius `rhoCell68 ρ = (1+ρ)/2` (its producer is the cell clause of `meshEventR`,
  Guard68S10.lean);
* the walk exponent is split: `hκ2 : 2 * K.ω < κ` with `κ = 2/(2+γ)^2 - ζ`; the second conjunct of `hWalk` is
  `ε ^ κ ≤ R/8`; `hα` and `hεs` keep `K.ω`;
* the stopped shell vertex lies almost surely in a finite set (`hstopFin`, the leaf
  `shellOneTest_of_direct_ae_rcell_stopFin_rho`), and `hRbd` is discharged by `windowRfT_hRbd_global`
  (WindowRfGlobal68.lean);
* `hx1`, `hmomS`, `hVolY` are taken at the radius `ρmom = rhoCell68 ρ = (1+ρ)/2` (the leaf's `ρmom`);
* the cut `hcutR : dyadicD r ^ shortExp ζ < rhoCell68 ρ - ρ` is the cut of `ShellOneTestOrderAeCGStmt`;
* the walk bound `hb` is `hb_ae_of_walk_loc` (WalkLoc68) on `hmesh`; the pointwise shell order is the named
  localized producer `hShellLoc`;
* `hfull`: `pos_iInf_annulus_ball` (HoneGoodEvent68.lean:119) needs the positivity of every ball of the annulus, not
  only `μ (ball x (c₀ R))`. -/
theorem shellOneTest_at_of_goodEnv_loc {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (_hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ)
    (_hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (ω₀ : ℝ) (hω0 : 0 < ω₀)
    (K : Constants68 γ ρ) (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (ω : Ω) (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (i : Lemma68Config.Config68)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- the exit mesh on the cell-size event of `meshEventR` (radius `rhoCell68 ρ = (1 + ρ)/2`)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    -- named localized producer, at `hmesh`
    (hShellLoc : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) →
      Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a)
    (hadm : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (hEl : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hstopFin : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∃ F : Set ℤ, F.Finite ∧
        ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x < ⊤ →
            x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ F)
    (hRr : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    (hcap : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r)
    (hVolC : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
              (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    (hVolY : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ y ∈ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ - winRf S ρ ζ C r ω
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)))
    (hGreen : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hCountGood : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hCellGood : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    (hcutR : dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hx1 : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < Lemma68HoneCellGood.rhoCell68 ρ - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hmomS : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ) →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    -- the walk second conjunct at the split exponent κ = 2/(2+γ)^2 - ζ (not `K.ω`)
    (hWalk : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)) (sphere 0 ρ))
    (hsel : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (winRf S ρ ζ C r ω z) z)
    (hfull : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t)) :
    ∃ Rf : ℂ → ℝ,
      ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
        (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  obtain ⟨-, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, -⟩ := hreg
  have hr1 : r ≤ 1 := by linarith
  have hd0 : 0 < dyadicD r := lt_of_lt_of_le (pow_pos hr0 2) (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd1 : dyadicD r ≤ 1 := by
    have h4 : r ≤ 1 / 4 := by linarith
    have h5 : r ^ 2 ≤ 1 / 16 := by nlinarith
    linarith [(Lemma68ChainGlue.dyadicD_mem hr0 hr1).2]
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hC0 : 0 < shellChone68 CE CG := lt_of_lt_of_le one_pos (one_le_shellChone68 CE CG)
  have hρm0 : 0 < Lemma68HoneCellGood.rhoCell68 ρ := by unfold Lemma68HoneCellGood.rhoCell68; linarith
  have hρm1 : Lemma68HoneCellGood.rhoCell68 ρ < 1 := by unfold Lemma68HoneCellGood.rhoCell68; linarith
  have hKs1 : K.s1 = shellS1CG γ CG := by subst hK; rfl
  have hKβ : K.βm = (2 + γ) ^ 2 / 2 + 1 := by subst hK; rfl
  have hKω : K.ω = ω₀ := by subst hK; rfl
  have hs1 : 0 < K.s1 := by rw [hKs1]; exact shellS1CG_pos γ CG
  have hβ1 : 1 ≤ K.βm := by rw [hKβ]; have := sq_nonneg (2 + γ); linarith
  have hω1 : 0 ≤ K.ω := by rw [hKω]; exact hω0.le
  have hα2 : 2 * K.ω ≤ α := le_trans (le_mul_of_one_le_right (by linarith) hβ1) hα.le
  have hαm : 2 * K.ω * K.βm ≤ α := hα.le

  have hTend := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hmω := hmult ε hε
  obtain ⟨hdr, hd2⟩ := Lemma68ChainGlue.dyadicD_mem hr0 hr1
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha1
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrz hd0 hd2
  have hspos : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd0 _
  obtain ⟨-, hjs, hN800, -⟩ := shell_parameters hr0 hd0 hζ0.le rfl hdr hd2 hs4
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h0 : (0 : ℝ) < (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) :=
      lt_of_lt_of_le (div_pos hr0 (mul_pos (by norm_num) hspos)) hN800
    exact_mod_cast h0
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hN1]
    exact (hjs 1 le_rfl hN1).2.2
  have hRw : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
        dyadicD r ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) := fun k hk =>
    (hEl hadm k hk).mono fun x hx hxm =>
      (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd0 hd1 ha1 ω (hx hxm)).1
  -- the walk bound `hb` at `ω`: the localized copy of `hb_ae_of_walk` (WalkLoc68), on the mesh `hmesh`;
  -- its gap `dyadicD r / 100 ≤ rhoCell68 ρ - ρ` follows from `dyadicD r / 100 ≤ dyadicD r ^ shortExp ζ` and `hcutR`
  have hbω := Lemma68WalkLoc.hb_ae_of_walk_loc (ρ := ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (r := r)
    (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Rf := winRf S ρ ζ C r ω)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    hcont hε (fillCells ε (S.η ω) ↑i.Θ) (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hdeg hadj (fun _ _ => rfl) hd0 ⟨0, hadm.1.2.2 (mem_ball_self hs₀)⟩ (subset_closure.trans hadm.1.2.1)
    hr0 hrρ hspos.le hNs (by linarith [hds, hcutR, hd0]) hmesh (fun k hk => hRw k hk)
  have hShell := hShellLoc hmesh hadm
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      winRf S ρ ζ C r ω z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd0 hd1 ha1 ω hz).2
  have hRr' := hRr hadm
  have hpos := Lemma68HoneGoodEventAe.hpos_ae K
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hfull hadm) hRr' hr0
  have hgood := Lemma68HoneGoodEventAe.hgood_ae K (hsel := hsel hadm) (hEl := hEl hadm)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hZ := fun _ _ => rfl)
  have hεα := Lemma68HoneGoodEventAe.hεα_ae K hε hε1 hα2 hrε hRr'
  have hεmass := Lemma68HoneGoodEventAe.hεmass_ae K hε hε1 hαm hrε hRr'
  have hsc := Lemma68HoneGoodEventAe.hsc_ae_threshold K (μ := S.μ ω) hε hrε hα hεs hRr' (hVolC hadm)
  have hdbl : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
        (S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
          (3 * K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal
          ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 CG * (S.μ ω (ball (vertexPoint ε (S.η ω) (x
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat))
            (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal := fun k hk => by
    filter_upwards [hbω k hk, hWalk hadm k hk, hgood k hk, hRr' k hk] with x hbx hWx hgx hRx
    intro hxm
    exact Lemma68HoneExitGeom.hdbl_of_exit_geom_path_split K hcont hε (μ := S.μ ω)
      (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := winRf S ρ ζ C r ω) (C_good := CG) (hr := hr0) k x
      (Lemma68HoneCellGood.rhoCell68 ρ) (Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1).le (hRx hxm)
      (K.c0 * r ^ 2) (mul_le_mul_of_nonneg_left (hRx hxm).1 K.hc0.le) (hWx hxm) (hCellGood hadm) hεcell
      (hgx hxm) (hbx hxm)
  have hL := Lemma68HoneSetup.hL68_of_clause (η := S.η ω) K i.A hε hr0 hs1
    (by
      obtain ⟨-, hAd⟩ := hadm
      obtain ⟨-, -, hcl⟩ := hAd
      rw [hKs1, hKβ]; exact hcl) (hcap hadm)
  refine ⟨winRf S ρ ζ C r ω, ?_, hShell⟩
  exact Lemma68LeafAe.shellOneTest_of_direct_ae_rcell_stopFin_rho_split
    (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) hρm0 hρm1 (K := K) (ε := ε) (η := S.η ω) (hη := hcont)
    (hprop := hTend) (hε := hε) (hεc := hεc) (μ := S.μ ω) (hμNull := hμN) (m := S.mult ε ω) (a := i.a)
    (A := (↑i.A : Set ℤ)) (hA := i.A.finite_toSet.measurableSet)
    (n := shellCount r (dyadicD r ^ shortExp ζ) - 1) (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := winRf S ρ ζ C r ω) (r := r) (s := dyadicD r ^ shortExp ζ)
    (d := dyadicD r) (q0 := q0) (α := α) (C_exit := CE) (C_good := CG) (C := shellChone68 CE CG)
    (N_cov := shellNcov68) (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0)
    (hCw := shellChone68_hCw CE CG) (hCg := hCG.le) (hlf := hmω.1) (hcons := hmω.2)
    (hstopFin := hstopFin hadm)
    (hRbd := fun k _ => by
      obtain ⟨t, ht⟩ := Lemma68WindowRfGlobal.windowRfT_hRbd_global S.μ ρ (shortExp ζ) shellC068 C (dyadicD r)
        hd0 hd1 ha1 ω ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k
      exact ⟨t, Filter.Eventually.of_forall fun x hx => ht x hx⟩)
    (hRr := hRr') (hL68 := hL) (rmin := K.c0 * r ^ 2)
    (hRmin := fun k hk => (hRr' k hk).mono fun x hx hxm => mul_le_mul_of_nonneg_left (hx hxm).1 K.hc0.le)
    (hVolC := hVolC hadm) (hVolY := hVolY hadm) (hGreen := hGreen hadm) (hWalk := hWalk hadm)
    (hCountGood := hCountGood hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (ρcell := Lemma68HoneCellGood.rhoCell68 ρ) (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCellGood hadm) (hd := hd0) (aW := shortExp ζ) (hRf := hRf) (hEl := hEl hadm)
    (hcut := hcutR) (hκ2 := hκ2) (hεcell := hεcell) (hsc := hsc) (hεα := hεα) (hεmass := hεmass)
    (hb := hbω) (hx1 := hx1 hadm) (hmomS := hmomS hadm) (hgood := hgood)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpos) (hdbl := hdbl)

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc

open Classical in
/-- **Copy of `shellOneTest_at_of_goodEnv_loc` with a free window constant `c0W`.**
Every window radius `winRf S ρ ζ C r ω` of `shellOneTest_at_of_goodEnv_loc` is written inline as
`windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω`, and `shellC068` is replaced by `c0W`; no new definition is made.
The statement and the proof are otherwise unchanged: `K.c0` (of `shellKCG`) is kept in `hVolC`, `hsel` and `hεcell`. -/
theorem shellOneTest_at_of_goodEnv_loc_g {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (c0W : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (_hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ)
    (_hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (ω₀ : ℝ) (hω0 : 0 < ω₀)
    (K : Constants68 γ ρ) (hK : K = shellKCG γ ρ ω₀ ζ CG hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1 hCG)
    (ω : Ω) (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (i : Lemma68Config.Config68)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- the exit mesh on the cell-size event of `meshEventR` (radius `rhoCell68 ρ = (1 + ρ)/2`)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)))
    -- named localized producer, at `hmesh`
    (hShellLoc : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)) →
      Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a)
    (hadm : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i)
    (hEl : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hstopFin : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∃ F : Set ℤ, F.Finite ∧
        ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x < ⊤ →
            x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat ∈ F)
    (hRr : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          r ^ 2 ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    (hcap : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r)
    (hVolC : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ENNReal.ofReal ((K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
              (K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    (hVolY : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ∀ y ∈ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)
            (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal (((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)))
    (hGreen : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hCountGood : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hCellGood : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    (hcutR : dyadicD r ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hx1 : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat)‖
            < Lemma68HoneCellGood.rhoCell68 ρ - (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hmomS : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Lemma68HoneCellGood.rhoCell68 ρ) →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    -- the walk second conjunct at the split exponent κ = 2/(2+γ)^2 - ζ (not `K.ω`)
    (hWalk : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat)) (sphere 0 ρ))
    (hsel : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z) z)
    (hfull : Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t)) :
    ∃ Rf : ℂ → ℝ,
      ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
        (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  obtain ⟨-, hcurve, hmult, hcont, hμN, hμF, hdeg, hadj, -⟩ := hreg
  have hr1 : r ≤ 1 := by linarith
  have hd0 : 0 < dyadicD r := lt_of_lt_of_le (pow_pos hr0 2) (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd1 : dyadicD r ≤ 1 := by
    have h4 : r ≤ 1 / 4 := by linarith
    have h5 : r ^ 2 ≤ 1 / 16 := by nlinarith
    linarith [(Lemma68ChainGlue.dyadicD_mem hr0 hr1).2]
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hC0 : 0 < shellChone68 CE CG := lt_of_lt_of_le one_pos (one_le_shellChone68 CE CG)
  have hρm0 : 0 < Lemma68HoneCellGood.rhoCell68 ρ := by unfold Lemma68HoneCellGood.rhoCell68; linarith
  have hρm1 : Lemma68HoneCellGood.rhoCell68 ρ < 1 := by unfold Lemma68HoneCellGood.rhoCell68; linarith
  have hKs1 : K.s1 = shellS1CG γ CG := by subst hK; rfl
  have hKβ : K.βm = (2 + γ) ^ 2 / 2 + 1 := by subst hK; rfl
  have hKω : K.ω = ω₀ := by subst hK; rfl
  have hs1 : 0 < K.s1 := by rw [hKs1]; exact shellS1CG_pos γ CG
  have hβ1 : 1 ≤ K.βm := by rw [hKβ]; have := sq_nonneg (2 + γ); linarith
  have hω1 : 0 ≤ K.ω := by rw [hKω]; exact hω0.le
  have hα2 : 2 * K.ω ≤ α := le_trans (le_mul_of_one_le_right (by linarith) hβ1) hα.le
  have hαm : 2 * K.ω * K.βm ≤ α := hα.le

  have hTend := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hmω := hmult ε hε
  obtain ⟨hdr, hd2⟩ := Lemma68ChainGlue.dyadicD_mem hr0 hr1
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hd0 hd1 ha1
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ0 hr0 hrz hd0 hd2
  have hspos : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd0 _
  obtain ⟨-, hjs, hN800, -⟩ := shell_parameters hr0 hd0 hζ0.le rfl hdr hd2 hs4
  have hN1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    have h0 : (0 : ℝ) < (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) :=
      lt_of_lt_of_le (div_pos hr0 (mul_pos (by norm_num) hspos)) hN800
    exact_mod_cast h0
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hN1]
    exact (hjs 1 le_rfl hN1).2.2
  have hRw : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
        dyadicD r ≤ (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) := fun k hk =>
    (hEl hadm k hk).mono fun x hx hxm =>
      (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω (hx hxm)).1
  -- the walk bound `hb` at `ω`: the localized copy of `hb_ae_of_walk` (WalkLoc68), on the mesh `hmesh`;
  -- its gap `dyadicD r / 100 ≤ rhoCell68 ρ - ρ` follows from `dyadicD r / 100 ≤ dyadicD r ^ shortExp ζ` and `hcutR`
  have hbω := Lemma68WalkLoc.hb_ae_of_walk_loc (ρ := ρ) (ρmesh := Lemma68HoneCellGood.rhoCell68 ρ) (r := r)
    (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (A := (↑i.A : Set ℤ))
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω))
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    hcont hε (fillCells ε (S.η ω) ↑i.Θ) (S.mult ε ω) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hdeg hadj (fun _ _ => rfl) hd0 ⟨0, hadm.1.2.2 (mem_ball_self hs₀)⟩ (subset_closure.trans hadm.1.2.1)
    hr0 hrρ hspos.le hNs (by linarith [hds, hcutR, hd0]) hmesh (fun k hk => hRw k hk)
  have hShell := hShellLoc hmesh hadm
  have hRf : ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) z ≤ dyadicD r ^ shortExp ζ := fun z hz =>
    (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) c0W C (dyadicD r) hd0 hd1 ha1 ω hz).2
  have hRr' := hRr hadm
  have hpos := Lemma68HoneGoodEventAe.hpos_ae K
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hfull hadm) hRr' hr0
  have hgood := Lemma68HoneGoodEventAe.hgood_ae K (hsel := hsel hadm) (hEl := hEl hadm)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hZ := fun _ _ => rfl)
  have hεα := Lemma68HoneGoodEventAe.hεα_ae K hε hε1 hα2 hrε hRr'
  have hεmass := Lemma68HoneGoodEventAe.hεmass_ae K hε hε1 hαm hrε hRr'
  have hsc := Lemma68HoneGoodEventAe.hsc_ae_threshold K (μ := S.μ ω) hε hrε hα hεs hRr' (hVolC hadm)
  have hdbl : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k →
        (S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
          (3 * K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal
          ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 CG * (S.μ ω (ball (vertexPoint ε (S.η ω) (x
            (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              ((windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) k x).toNat))
            (K.c0 * (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)))).toReal := fun k hk => by
    filter_upwards [hbω k hk, hWalk hadm k hk, hgood k hk, hRr' k hk] with x hbx hWx hgx hRx
    intro hxm
    exact Lemma68HoneExitGeom.hdbl_of_exit_geom_path_split K hcont hε (μ := S.μ ω)
      (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) (C_good := CG) (hr := hr0) k x
      (Lemma68HoneCellGood.rhoCell68 ρ) (Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1).le (hRx hxm)
      (K.c0 * r ^ 2) (mul_le_mul_of_nonneg_left (hRx hxm).1 K.hc0.le) (hWx hxm) (hCellGood hadm) hεcell
      (hgx hxm) (hbx hxm)
  have hL := Lemma68HoneSetup.hL68_of_clause (η := S.η ω) K i.A hε hr0 hs1
    (by
      obtain ⟨-, hAd⟩ := hadm
      obtain ⟨-, -, hcl⟩ := hAd
      rw [hKs1, hKβ]; exact hcl) (hcap hadm)
  refine ⟨(windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω), ?_, hShell⟩
  exact Lemma68LeafAe.shellOneTest_of_direct_ae_rcell_stopFin_rho_split
    (ρmom := Lemma68HoneCellGood.rhoCell68 ρ) hρm0 hρm1 (K := K) (ε := ε) (η := S.η ω) (hη := hcont)
    (hprop := hTend) (hε := hε) (hεc := hεc) (μ := S.μ ω) (hμNull := hμN) (m := S.mult ε ω) (a := i.a)
    (A := (↑i.A : Set ℤ)) (hA := i.A.finite_toSet.measurableSet)
    (n := shellCount r (dyadicD r ^ shortExp ζ) - 1) (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r))
    (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := (windowRfT S.μ ρ (shortExp ζ) c0W C (dyadicD r) ω)) (r := r) (s := dyadicD r ^ shortExp ζ)
    (d := dyadicD r) (q0 := q0) (α := α) (C_exit := CE) (C_good := CG) (C := shellChone68 CE CG)
    (N_cov := shellNcov68) (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0)
    (hCw := shellChone68_hCw CE CG) (hCg := hCG.le) (hlf := hmω.1) (hcons := hmω.2)
    (hstopFin := hstopFin hadm)
    (hRbd := fun k _ => by
      obtain ⟨t, ht⟩ := Lemma68WindowRfGlobal.windowRfT_hRbd_global S.μ ρ (shortExp ζ) c0W C (dyadicD r)
        hd0 hd1 ha1 ω ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) k
      exact ⟨t, Filter.Eventually.of_forall fun x hx => ht x hx⟩)
    (hRr := hRr') (hL68 := hL) (rmin := K.c0 * r ^ 2)
    (hRmin := fun k hk => (hRr' k hk).mono fun x hx hxm => mul_le_mul_of_nonneg_left (hx hxm).1 K.hc0.le)
    (hVolC := hVolC hadm) (hVolY := hVolY hadm) (hGreen := hGreen hadm) (hWalk := hWalk hadm)
    (hCountGood := hCountGood hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (ρcell := Lemma68HoneCellGood.rhoCell68 ρ) (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCellGood hadm) (hd := hd0) (aW := shortExp ζ) (hRf := hRf) (hEl := hEl hadm)
    (hcut := hcutR) (hκ2 := hκ2) (hεcell := hεcell) (hsc := hsc) (hεα := hεα) (hεmass := hεmass)
    (hb := hbω) (hx1 := hx1 hadm) (hmomS := hmomS hadm) (hgood := hgood)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpos) (hdbl := hdbl)

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv_loc_g

/-- **Mesh bound on the visited set from the radius-`ρ` cell-size event.** The cells
meeting `ball 0 ρ` (the visited set `F0 = cellVertices ε η (ball 0 ρ)` of `ConfigOK`) have diameter at most
`dyadicD r / 100` on the cell-size event of `meshEvent`, which is at radius `ρ` (not `(1+ρ)/2`). Route:
`hmesh_local_of_cellSize` at the radius `2ρ - 1`, for which `(1 + (2ρ-1))/2 = ρ`. The strict `2 ω₀ < κ` is the
hypothesis of that lemma; goodEnv' has only `K.ω ≤ κ`. -/
theorem cellDiamLe_F0_of_cellSize {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {γ ζ ρ ω₀ ε : ℝ}
    (hω₀ : 0 < ω₀) (hκ : 2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hcut : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ 1 / 100)
    (ω : Ω) (hω : ω ∈ cellSizeEvent68 S γ ζ ρ ε)
    (r : ℝ) (hr : 0 < r) (hrε : 10 * ε ^ ω₀ ≤ r) :
    CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) := by
  have e : (1 + (2 * ρ - 1)) / 2 = ρ := by ring
  have h := Lemma68HoneSetup239.hmesh_local_of_cellSize (ρ := 2 * ρ - 1) S hω₀ hκ hε1 hcut hε le_rfl ω
    (by rw [e]; exact hω) r hr hrε
  rw [e] at h
  exact h

/-- **Walk exponent `κ = 2/(2+γ)² - ζ` at a shell centre.** The walk second
conjunct `ε ^ κ ≤ R / 8` follows from `10 ε^{ω₀} ≤ r` and `r² ≤ R` (the `hRr` lower bound) by
`pow_le_div_eight_of_two_omega`, with the strict `2 ω₀ < κ`. κ enters this bound only; it is not used in `hα` or `hεs`. -/
theorem rpow_kappa_le_div_eight {ε ω₀ κ r R : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hκ : 2 * ω₀ < κ)
    (hrε : 10 * ε ^ ω₀ ≤ r) (hR : r ^ 2 ≤ R) : ε ^ κ ≤ R / 8 := by
  apply Lemma68ShellConstants.pow_le_div_eight_of_two_omega hε0 hε1 hκ
  have e2 : ε ^ (2 * ω₀) = (ε ^ ω₀) ^ 2 := by
    rw [show 2 * ω₀ = ω₀ * 2 by ring, Real.rpow_mul hε0.le, Real.rpow_two]
  have h10 : 0 ≤ 10 * ε ^ ω₀ := mul_nonneg (by norm_num) (Real.rpow_nonneg hε0.le _)
  have hsq : (10 * ε ^ ω₀) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h10 hrε 2
  calc 100 * ε ^ (2 * ω₀) = (10 * ε ^ ω₀) ^ 2 := by rw [e2]; ring
    _ ≤ r ^ 2 := hsq
    _ ≤ R := hR

end Lemma68B1Assembly
end MatedCRT


#print axioms MatedCRT.Lemma68B1Assembly.cellDiamLe_F0_of_cellSize
#print axioms MatedCRT.Lemma68B1Assembly.rpow_kappa_le_div_eight
