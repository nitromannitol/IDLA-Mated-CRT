import MatedCRT.FirstPass.S4S6c.HoneLeafAe68
import MatedCRT.FirstPass.S4S6c.HoneReduced68
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

/-!
# The one-test bound and the shell order at a fixed radius, almost surely (q1, fp-S4S6c-B1-assembly)

`shellOneTest_ae_fixedR` is the almost-sure form, at one fixed radius `r`, of the two conjuncts of the B1 conclusion
`ShellOneTestOrderAeStmt` (ShellHoneInst68.lean:159): the one-test bound `ShellOneTestAt` and the shell order `ShellOrderAe`,
for the window radius `Rf = winRf S ρ ζ C r ω` of the environment `ω`.

* `ShellOrderAe`: `shellOrderAe_window` (ShellOrderWindow68.lean:34); its binders `hmesh`, `hstart`, `htest` are kept.
* `ShellOneTestAt`: `shellOneTest_of_direct_reduced68` (HoneReduced68.lean:41) at the environment `ω`. Its binders are the
  a.s.-in-`ω` named hypotheses below, each the leaf binder with `m := S.mult ε ω`, `η := S.η ω`, `μ := S.μ ω`,
  `Kset := fillCells ε (S.η ω) i.Θ`, `τU := vExitTime (killed …)`, guarded by `ω ∈ E` and `FullAdm`.
  `hlf`, `hcons` come from `hmult_of_valid68` (WindowMult68.lean:34). `hN` is `shellNcov68_spec` (ShellConstOrder68.lean:118).
  `hRmin` is derived from `hRr` with `rmin := K.c0 * r ^ 2`.

Not proved here: the quantifier order of `ShellOneTestOrderAeStmt` (`∀ r` sits inside `∀ᵐ ω`), and the deterministic side
conditions `hεc`, `hεcell`, which depend on `ε` and `r` and are not implied by that statement (see the report).

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

/-- **The one-test bound and the shell order at a fixed radius, almost surely.** Each leaf binder that is not discharged
is an a.s.-in-`ω` named hypothesis: the leaf binder at the environment `ω`, guarded by `ω ∈ E` and `FullAdm`. -/
theorem shellOneTest_ae_fixedR {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (E : Set Ω) (i : Lemma68Config.Config68)
    (K : Constants68 γ ρ)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    -- window route (ShellOrderAe): the binders of `shellOrderAe_window`
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k x ≠ ⊤)
    -- environment inputs
    (hcurve : ∀ᵐ ω ∂S.P, Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hηc : ∀ᵐ ω ∂S.P, Continuous (S.η ω))
    (hμNull : ∀ᵐ ω ∂S.P, ∀ v : ℂ, S.μ ω {v} = 0)
    (hμFin : ∀ᵐ ω ∂S.P, IsFiniteMeasureOnCompacts (S.μ ω))
    -- leaf binders (a.s.-in-`ω`)
    (hTdom : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ D : Set ℤ, D.Finite ∧ ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w ≤ vExitTime D w)
    (hRbd : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ s' : ℝ, ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ s')
    (hRr : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ 1)
    (hL68 : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, (((↑i.A : Set ℤ) ∩ cellVertices ε (S.η ω) (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (hVolC : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)) ^ K.βm)
          ≤ S.μ ω (ball (vertexPoint ε (S.η ω)
              (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
                (winRf S ρ ζ C r ω) k w).toNat))
            (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k w))))
    (hVolY : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4),
          ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4) ^ K.βm)
            ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4)))
    (hGreen : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hWalk : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
          ε ^ K.ω ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 8 ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 8 ≤
            infDist (vertexPoint ε (S.η ω) (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k w).toNat)) (sphere 0 ρ))
    (hCountGood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hCellGood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    -- cell-control radius of chat 237 section 3: the prefix bound R/4 < rhoCell - rho (k ≤ shellCount - 1)
    (hRcell : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1 → ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r
          (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k,
        winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζ)
    (hsc :∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        4 * ε ^ α ≤ (S.μ ω (ball (vertexPoint ε (S.η ω)
            (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k w).toNat))
          (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)))).toReal)
    (hεα : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ε ^ α ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 100)
    (hεmass : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ε ^ α ≤ (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4) ^ K.βm)
    (hb : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w).toNat ∈ cellVertices ε (S.η ω)
          (sphere (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w) (4 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 3)))
    (hx1 : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ‖vertexPoint ε (S.η ω) (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k w).toNat)‖
          < 1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4)
    (hmomS : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
        ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
          exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
            ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    (hgood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (winRf S ρ ζ C r ω (shellCentre ε (S.η ω)
          (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w)) (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w))
    (hpos : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        0 < ⨅ y ∈ annulus (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w) (winRf S ρ ζ C r ω (shellCentre ε (S.η ω)
            (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w))
          (2 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)),
          S.μ ω (ball y (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w))))
    (hdbl : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        (S.μ ω (ball (vertexPoint ε (S.η ω)
            (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k w).toNat))
          (3 * K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)))).toReal
          ≤ shellDbl68 CG * (S.μ ω (ball (vertexPoint ε (S.η ω)
            (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k w).toNat))
          (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)))).toReal) :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∃ Rf : ℂ → ℝ,
        ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
          (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
        Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
          (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  have hC0 : 0 < shellChone68 CE CG := lt_of_lt_of_le one_pos (one_le_shellChone68 CE CG)
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE CG
    have hbq : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hr1 : r ≤ 1 := by linarith
  have hrz := le_trans hRA (Lemma68ChainGlue.rAmp_le_countThreshold hq0 hq1 hζ0 hζ1)
  have hShell := shellOrderAe_window (c₀ := shellC068) (C := C) hγ0 hγ2 S hS hε hs₀ hζ0 hζ1 hr0 hrz hrρ i
    hmesh hstart htest
  have hmultAe := hmult_ae_valid hγ0 hγ2 S hS hε
  filter_upwards [hShell, hmultAe, hcurve, hηc, hμNull, hμFin, hTdom, hRbd, hRr, hL68, hVolC, hVolY,
    hGreen, hWalk, hCountGood, hCellGood, hRcell, hsc, hεα, hεmass, hb, hx1, hmomS, hgood, hpos, hdbl]
    with ω hShω hmω hcω hηω hμNω hμFω hTω hRbω hRrω hLω hVCω hVYω hGω hWω hCGω hCeω hRcω hscω hεαω hεmω
      hbω hx1ω hmSω hgω hpω hdω
  intro hωE hadm
  have hμFin' : IsFiniteMeasureOnCompacts (S.μ ω) := hμFω
  have hRr' := hRrω hωE hadm
  have hRmin : ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
      (winRf S ρ ζ C r ω) k,
      K.c0 * r ^ 2 ≤ K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
        (dyadicD r ^ shortExp ζ) (dyadicD r) k w) :=
    fun k w hw => mul_le_mul_of_nonneg_left ((hRr' k w hw).1) K.hc0.le
  refine ⟨winRf S ρ ζ C r ω, ?_, hShω hadm⟩
  -- the leaf takes almost-sure prefix binders; the pointwise B1 binders give them by `Eventually.of_forall`
  exact Lemma68LeafAe.shellOneTest_of_direct_ae (K := K) (ε := ε) (η := S.η ω) (hη := hηω)
    (hprop := Lemma68Geometry.tendsto_cocompact_of_escapes (hcω)) (hε := hε) (hεc := hεc)
    (μ := S.μ ω) (hμNull := hμNω) (m := S.mult ε ω) (a := i.a) (A := (↑i.A : Set ℤ))
    (hA := i.A.finite_toSet.measurableSet) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Kset := fillCells ε (S.η ω) ↑i.Θ)
    (Rf := winRf S ρ ζ C r ω) (r := r) (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (q0 := q0) (α := α)
    (C_exit := CE) (C_good := CG) (C := shellChone68 CE CG) (N_cov := shellNcov68)
    (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0) (hCw := shellChone68_hCw CE CG) (hCg := hCG.le)
    (hlf := (hmω).1) (hcons := (hmω).2) (hTdom := hTω hωE hadm) (hRbd := hRbω hωE hadm)
    (hRr := fun k _ => Filter.Eventually.of_forall fun x hx => hRr' k x hx)
    (hL68 := hLω hωE hadm) (rmin := K.c0 * r ^ 2)
    (hRmin := fun k _ => Filter.Eventually.of_forall fun x hx => hRmin k x hx)
    (hVolC := fun k _ => Filter.Eventually.of_forall fun x hx => hVCω hωE hadm k x hx)
    (hVolY := fun k _ => Filter.Eventually.of_forall fun x hx => hVYω hωE hadm k x hx)
    (hGreen := hGω hωE hadm)
    (hWalk := fun k _ => Filter.Eventually.of_forall fun x hx => hWω hωE hadm k x hx)
    (hCountGood := hCGω hωE hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (ρcell := Lemma68HoneCellGood.rhoCell68 ρ) (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCeω hωE hadm)
    (hRcell := fun k hk => Filter.Eventually.of_forall fun x hx => hRcω hωE hadm k hk x hx)
    (hωκ := hωκ) (hεcell := hεcell)
    (hsc := fun k _ => Filter.Eventually.of_forall fun x hx => hscω hωE hadm k x hx)
    (hεα := fun k _ => Filter.Eventually.of_forall fun x hx => hεαω hωE hadm k x hx)
    (hεmass := fun k _ => Filter.Eventually.of_forall fun x hx => hεmω hωE hadm k x hx)
    (hb := fun k _ => Filter.Eventually.of_forall fun x hx => hbω hωE hadm k x hx)
    (hx1 := fun k _ => Filter.Eventually.of_forall fun x hx => hx1ω hωE hadm k x hx)
    (hmomS := fun k _ => Filter.Eventually.of_forall fun x hx => hmSω hωE hadm k x hx)
    (hgood := fun k _ => Filter.Eventually.of_forall fun x hx => hgω hωE hadm k x hx)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := fun k _ => Filter.Eventually.of_forall fun x hx => hpω hωE hadm k x hx)
    (hdbl := fun k _ => Filter.Eventually.of_forall fun x hx => hdω hωE hadm k x hx)

open Classical in
/-- **The one-test bound and the shell order at a fixed radius, almost surely, from the walk-form leaf (q4,
fp-S4S6c-B1-assembly-ae, part 2).** The same per-radius conclusion as `shellOneTest_ae_fixedR`, from the walk-form leaf
`shellOneTest_of_direct_ae` (HoneLeafAe68.lean:385), at the shell constants `K := shellK68 γ ρ ω₀ ζ …`.
Every leaf binder is an almost-sure statement in the walk form `∀ k ≤ n, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a, x ∈ leafPre … → …`.
Discharged here: the environment (`Uniform68Env.ae_envInputs`, `hmult_ae_valid`), `hb` (`hb_ae_valid_centre`), `hdbl`
(`hdbl_of_exit_geom_path`, pointwise in the walk), `hL68` (`hL68_of_clause`, with the `Admissible` clause of `FullAdmAt`),
`hεα`, `hεmass`, `hsc`, `hpos`, `hgood` (HoneGoodEventAe68 and HoneGoodEventAe68.hgood_ae), `hN` (`shellNcov68_spec`).
The rest are named hypotheses, listed in the binder table of the report. -/
theorem shellOneTest_ae_fixedR_ae {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (E : Set Ω) (i : Lemma68Config.Config68)
    (ω₀ : ℝ) (hω0 : 0 < ω₀)
    (K : Constants68 γ ρ) (hK : K = shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1)
    -- eps threshold and exponents (named; q2 checking)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- window route (ShellOrderAe): the binders of `shellOrderAe_window`
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k x ≠ ⊤)
    -- environment inputs (named: no atoms, finite on compacts)
    (hμNull : ∀ᵐ ω ∂S.P, ∀ v : ℂ, S.μ ω {v} = 0)
    (hμFin : ∀ᵐ ω ∂S.P, IsFiniteMeasureOnCompacts (S.μ ω))
    -- leaf binders at the environment ω, guarded by `ω ∈ E` and `FullAdmAt`
    (hTdom : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ D : Set ℤ, D.Finite ∧ ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w ≤ vExitTime D w)
    (hRbd : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ s' : ℝ, ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ s')
    -- radius bounds, walk form (named; blocked on the FullAdmAt version of HoneSetup68.hRr_ae_setup)
    (hRr : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    -- operator request 66b: the cluster-radius cap of the leaf `hL68`
    (hcap : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r)
    -- operator request 60d: the volume lower bounds (walk form)
    (hVolC : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
              (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    (hVolY : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)))
    -- Green lower bound and counting bound (named: needs the PolyHighProb inputs, see report)
    (hGreen : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hCountGood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    -- the cell-control event at the leaf radius rho_cell = rhoCell68 rho (chat 237 version: q1)
    (hCellGood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    (hRcell : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k x) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    -- operator request 60f, 62b, 64d: walk-form inputs of the leaf
    (hx1 : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < 1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hmomS : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    (hWalk : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ K.ω ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)) (sphere 0 ρ))
    -- the good annulus event on the short-eligible centres, and the eligibility of the shell centres (named)
    (hsel : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (winRf S ρ ζ C r ω z) z)
    (hEl : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    -- operator request 65b: the full support of the measure on balls
    (hfull : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t))
    :
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∃ Rf : ℂ → ℝ,
        ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
          (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
          (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
        Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
          (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  have hC0 : 0 < shellChone68 CE CG := lt_of_lt_of_le one_pos (one_le_shellChone68 CE CG)
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE CG
    have hbq : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hr1 : r ≤ 1 := by linarith
  have hrz := le_trans hRA (Lemma68ChainGlue.rAmp_le_countThreshold hq0 hq1 hζ0 hζ1)
  have hShell := shellOrderAe_window (c₀ := shellC068) (C := C) hγ0 hγ2 S hS hε hs₀ hζ0 hζ1 hr0 hrz hrρ i
    hmesh hstart htest
  -- the constants of `shellK68`
  have hKs1 : K.s1 = Lemma68Config.sparsityS1 γ := by subst hK; rfl
  have hKβ : K.βm = (2 + γ) ^ 2 / 2 + 1 := by subst hK; rfl
  have hKω : K.ω = ω₀ := by subst hK; rfl
  have hs1 : 0 < K.s1 := by rw [hKs1]; exact Lemma68Config.sparsityS1_pos γ
  have hβ1 : 1 ≤ K.βm := by rw [hKβ]; have := sq_nonneg (2 + γ); linarith
  have hω1 : 0 ≤ K.ω := by rw [hKω]; exact hω0.le
  have hα2 : 2 * K.ω ≤ α := le_trans (le_mul_of_one_le_right (by linarith) hβ1) hα.le
  have hαm : 2 * K.ω * K.βm ≤ α := hα.le
  -- the a.s. inputs that are discharged (no guard on the environment)
  have hmultAe := hmult_ae_valid hγ0 hγ2 S hS hε
  have hEnv := Uniform68Env.ae_envInputs hγ0 hγ2 hS
  have hd0 : 0 < dyadicD r := lt_of_lt_of_le (pow_pos hr0 2) (Lemma68ChainGlue.dyadicD_mem hr0 hr1).1
  have hd1 : dyadicD r ≤ 1 := by
    have h4 : r ≤ 1 / 4 := by linarith
    have h5 : r ^ 2 ≤ 1 / 16 := by nlinarith
    linarith [(Lemma68ChainGlue.dyadicD_mem hr0 hr1).2]
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hbAe := Lemma68HoneExitGeom.hb_ae_valid_centre_mesh hγ0 hγ2 S hS hε
    (fun ω => fillCells ε (S.η ω) ↑i.Θ) (Rf := fun ω => winRf S ρ ζ C r ω)
    (τU := fun ω => vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (A := (↑i.A : Set ℤ))
    (r := r) (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) i.a (shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (fun ω => ω ∈ E ∧ Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i) hd0 hmesh
    (by
      filter_upwards [hEl] with ω hElω hG k hk
      filter_upwards [hElω hG.1 hG.2 k hk] with x hx hxm
      exact (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd0 hd1 ha1 ω (hx hxm)).1)
  filter_upwards [hShell, hmultAe, hEnv, hμNull, hμFin, hTdom, hRbd, hRr, hcap, hVolC, hVolY, hGreen,
    hWalk, hCountGood, hCellGood, hRcell, hx1, hmomS, hsel, hfull, hEl, hbAe]
    with ω hShω hmω hEω hμNω hμFω hTω hRbω hRrω hcpω hVCω hVYω hGω hWω hCGω hCeω hRcω hx1ω hmSω hselω hfuω
      hElω hbω
  intro hωE hadm
  have hb0 := hbω ⟨hωE, hadm⟩
  have hμFin' : IsFiniteMeasureOnCompacts (S.μ ω) := hμFω
  have hRr' := hRrω hωE hadm
  have hcl : ∀ B ⊆ i.A, B.Nonempty → r ≤ cRad ε (S.η ω) B ∨
      tRad ε (Lemma68Config.sparsityS1 γ) ((2 + γ) ^ 2 / 2 + 1) B < r := by
    obtain ⟨-, hAd⟩ := hadm
    obtain ⟨-, -, hcl⟩ := hAd
    exact hcl
  have hL := Lemma68HoneSetup.hL68_of_clause (η := S.η ω) K i.A hε hr0 hs1
    (by rw [hKs1, hKβ]; exact hcl) (hcpω hωE hadm)
  have hRmin : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
        K.c0 * r ^ 2 ≤ K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) :=
    fun k hk => (hRr' k hk).mono fun x hx hxm => mul_le_mul_of_nonneg_left (hx hxm).1 K.hc0.le
  have hgood := Lemma68HoneGoodEventAe.hgood_ae K (hsel := hselω hωE hadm) (hEl := hElω hωE hadm)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hZ := fun _ _ => rfl)
  have hεα := Lemma68HoneGoodEventAe.hεα_ae K hε hε1 hα2 hrε hRr'
  have hεmass := Lemma68HoneGoodEventAe.hεmass_ae K hε hε1 hαm hrε hRr'
  have hsc := Lemma68HoneGoodEventAe.hsc_ae_threshold K (μ := S.μ ω) hε hrε hα hεs hRr' (hVCω hωE hadm)
  have hpos := Lemma68HoneGoodEventAe.hpos_ae K (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ)
    r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) (hfuω hωE hadm) hRr' hr0
  refine ⟨winRf S ρ ζ C r ω, ?_, hShω hadm⟩
  exact Lemma68LeafAe.shellOneTest_of_direct_ae (K := K) (ε := ε) (η := S.η ω) (hη := hEω.1)
    (hprop := hEω.2.1) (hε := hε) (hεc := hεc)
    (μ := S.μ ω) (hμNull := hμNω) (m := S.mult ε ω) (a := i.a) (A := (↑i.A : Set ℤ))
    (hA := i.A.finite_toSet.measurableSet) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Kset := fillCells ε (S.η ω) ↑i.Θ)
    (Rf := winRf S ρ ζ C r ω) (r := r) (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (q0 := q0) (α := α)
    (C_exit := CE) (C_good := CG) (C := shellChone68 CE CG) (N_cov := shellNcov68)
    (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0) (hCw := shellChone68_hCw CE CG) (hCg := hCG.le)
    (hlf := (hmω).1) (hcons := (hmω).2) (hTdom := hTω hωE hadm) (hRbd := hRbω hωE hadm)
    (hRr := hRr') (hL68 := hL) (rmin := K.c0 * r ^ 2) (hRmin := hRmin)
    (hVolC := hVCω hωE hadm) (hVolY := hVYω hωE hadm)
    (hGreen := hGω hωE hadm) (hWalk := hWω hωE hadm)
    (hCountGood := hCGω hωE hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (ρcell := Lemma68HoneCellGood.rhoCell68 ρ) (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCeω hωE hadm) (hRcell := hRcω hωE hadm)
    (hωκ := hωκ) (hεcell := hεcell)
    (hsc := hsc) (hεα := hεα) (hεmass := hεmass) (hb := hb0)
    (hx1 := hx1ω hωE hadm) (hmomS := hmSω hωE hadm) (hgood := hgood)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpos)
    (hdbl := fun k hk => by
      filter_upwards [hb0 k hk, hWω hωE hadm k hk, hgood k hk, hRr' k hk] with x hbx hWx hgx hRx
      intro hxm
      exact Lemma68HoneExitGeom.hdbl_of_exit_geom_path K hEω.1 hε (μ := S.μ ω)
        (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := winRf S ρ ζ C r ω) (C_good := CG) (hr := hr0) k x
        (Lemma68HoneCellGood.rhoCell68 ρ) (Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1).le (hRx hxm)
        (K.c0 * r ^ 2) (mul_le_mul_of_nonneg_left (hRx hxm).1 K.hc0.le) (hWx hxm) (hCeω hωE hadm) hεcell
        (hgx hxm) (hbx hxm))

/-- **The regular environment at one environment `ω` and one scale `ε` (q4, fp-S4S6c-goodenv-body).** The r-free
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

open Classical in
/-- **The one-test bound and the shell order at one radius, at one regular environment (q4, fp-S4S6c-goodenv-body,
operator request, chat 239 l.84-95).** The body of `shellOneTest_ae_fixedR_ae` at one fixed environment `ω` and one fixed
radius `r`: the almost-sure environment inputs are the fields of `RegularEnvAt68`, and the almost-sure leaf inputs are
the walk-form binders (`∀ k ≤ n, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a, x ∈ leafPre … → …`). The window route is the named
pointwise order `hShell` (the pointwise core of `shellOrderAe_window` is not in the repository; see the report). The
window event enters through the mesh `hmesh` at `dyadicD r` (the dyadic premise of `cellDiam_ae_dyadicD` at `ω`). -/
theorem shellOneTest_at_of_goodEnv {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (ω₀ : ℝ) (hω0 : 0 < ω₀)
    (K : Constants68 γ ρ) (hK : K = shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1)
    (ω : Ω) (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (i : Lemma68Config.Config68)
    -- eps threshold and exponents (named; q2 checking)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- the mesh at the scale `dyadicD r` (pointwise at `ω`; the dyadic premise of `cellDiam_ae_dyadicD`)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    -- the window route: the pointwise order (named; pointwise core of `shellOrderAe_window` not in the repository)
    (hShell : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r)
        (windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω)
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a)
    (hadm : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i)
    -- the shell centres are short-eligible (walk form; named, see the report)
    (hEl : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hTdom : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ D : Set ℤ, D.Finite ∧ ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w ≤ vExitTime D w)
    (hRbd : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ s' : ℝ, ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ s')
    (hRr : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    (hcap : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r)
    (hVolC : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
              (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    (hVolY : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)))
    (hGreen : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hCountGood : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hCellGood : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    (hRcell : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k x) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hx1 : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < 1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hmomS : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    (hWalk : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ K.ω ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)) (sphere 0 ρ))
    (hsel : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (winRf S ρ ζ C r ω z) z)
    (hfull : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
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
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE CG
    have hbq : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hr1 : r ≤ 1 := by linarith
  have hrz := le_trans hRA (Lemma68ChainGlue.rAmp_le_countThreshold hq0 hq1 hζ0 hζ1)
  have hKs1 : K.s1 = Lemma68Config.sparsityS1 γ := by subst hK; rfl
  have hKβ : K.βm = (2 + γ) ^ 2 / 2 + 1 := by subst hK; rfl
  have hKω : K.ω = ω₀ := by subst hK; rfl
  have hs1 : 0 < K.s1 := by rw [hKs1]; exact Lemma68Config.sparsityS1_pos γ
  have hβ1 : 1 ≤ K.βm := by rw [hKβ]; have := sq_nonneg (2 + γ); linarith
  have hω1 : 0 ≤ K.ω := by rw [hKω]; exact hω0.le
  have hα2 : 2 * K.ω ≤ α := le_trans (le_mul_of_one_le_right (by linarith) hβ1) hα.le
  have hαm : 2 * K.ω * K.βm ≤ α := hα.le
  -- the environment inputs at `ω`
  have hTend := Lemma68Geometry.tendsto_cocompact_of_escapes hcurve
  have hmω := hmult ε hε
  -- the window radius at the shell centres, from the eligibility (walk form)
  have hRw : ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
      x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
        dyadicD r ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k x) := fun k hk =>
    (hEl hadm k hk).mono fun x hx hxm =>
      (Lemma68WindowRf.windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) hd0 hd1 ha1 ω (hx hxm)).1
  -- `hb` at `ω`, from the mesh and the window radius
  have hbω := Lemma68HoneExitGeom.hb_ae_of_walk hcont (fillCells ε (S.η ω) ↑i.Θ) (S.mult ε ω) i.a
    (shellCount r (dyadicD r ^ shortExp ζ) - 1) (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ)
      r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) hdeg hadj (fun _ _ => rfl)
    (fun k hk => (hRw k hk).mono fun x hx hxm t ht =>
      Lemma68HoneExitGeom.shellHit_interior_of_mesh hε (fillCells ε (S.η ω) ↑i.Θ) (R := winRf S ρ ζ C r ω)
        hd0 hmesh k x (hx hxm) t ht)
  have hL := Lemma68HoneSetup.hL68_of_clause (η := S.η ω) K i.A hε hr0 hs1
    (by
      obtain ⟨-, hAd⟩ := hadm
      obtain ⟨-, -, hcl⟩ := hAd
      rw [hKs1, hKβ]; exact hcl) (hcap hadm)
  have hgood := Lemma68HoneGoodEventAe.hgood_ae K (hsel := hsel hadm) (hEl := hEl hadm)
    (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
    (hZ := fun _ _ => rfl)
  have hRr' := hRr hadm
  have hεα := Lemma68HoneGoodEventAe.hεα_ae K hε hε1 hα2 hrε hRr'
  have hεmass := Lemma68HoneGoodEventAe.hεmass_ae K hε hε1 hαm hrε hRr'
  have hsc := Lemma68HoneGoodEventAe.hsc_ae_threshold K (μ := S.μ ω) hε hrε hα hεs hRr' (hVolC hadm)
  have hpos := Lemma68HoneGoodEventAe.hpos_ae K (Z := fun k x => shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ)
    r (dyadicD r ^ shortExp ζ) (dyadicD r) k x) (hfull hadm) hRr' hr0
  refine ⟨winRf S ρ ζ C r ω, ?_, hShell hadm⟩
  exact Lemma68LeafAe.shellOneTest_of_direct_ae (K := K) (ε := ε) (η := S.η ω) (hη := hcont)
    (hprop := hTend) (hε := hε) (hεc := hεc)
    (μ := S.μ ω) (hμNull := hμN) (m := S.mult ε ω) (a := i.a) (A := (↑i.A : Set ℤ))
    (hA := i.A.finite_toSet.measurableSet) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Kset := fillCells ε (S.η ω) ↑i.Θ)
    (Rf := winRf S ρ ζ C r ω) (r := r) (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (q0 := q0) (α := α)
    (C_exit := CE) (C_good := CG) (C := shellChone68 CE CG) (N_cov := shellNcov68)
    (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0) (hCw := shellChone68_hCw CE CG) (hCg := hCG.le)
    (hlf := hmω.1) (hcons := hmω.2) (hTdom := hTdom hadm) (hRbd := hRbd hadm)
    (hRr := hRr') (hL68 := hL) (rmin := K.c0 * r ^ 2)
    (hRmin := fun k hk => (hRr' k hk).mono fun x hx hxm =>
      mul_le_mul_of_nonneg_left (hx hxm).1 K.hc0.le)
    (hVolC := hVolC hadm) (hVolY := hVolY hadm)
    (hGreen := hGreen hadm) (hWalk := hWalk hadm)
    (hCountGood := hCountGood hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (ρcell := Lemma68HoneCellGood.rhoCell68 ρ) (hρgap := Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1)
    (hCellGood := hCellGood hadm) (hRcell := hRcell hadm)
    (hωκ := hωκ) (hεcell := hεcell)
    (hsc := hsc) (hεα := hεα) (hεmass := hεmass) (hb := hbω)
    (hx1 := hx1 hadm) (hmomS := hmomS hadm) (hgood := hgood)
    (hN := fun _ _ => Filter.Eventually.of_forall fun _ _ R' z' hR' =>
      Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpos)
    (hdbl := fun k hk => by
      filter_upwards [hbω k hk, hWalk hadm k hk, hgood k hk, hRr' k hk] with x hbx hWx hgx hRx
      intro hxm
      exact Lemma68HoneExitGeom.hdbl_of_exit_geom_path K hcont hε (μ := S.μ ω)
        (Kset := fillCells ε (S.η ω) ↑i.Θ) (Rf := winRf S ρ ζ C r ω) (C_good := CG) (hr := hr0) k x
        (Lemma68HoneCellGood.rhoCell68 ρ) (Lemma68HoneCellGood.rhoC_lt_rhoCell68 hρ1).le (hRx hxm)
        (K.c0 * r ^ 2) (mul_le_mul_of_nonneg_left (hRx hxm).1 K.hc0.le) (hWx hxm) (hCellGood hadm) hεcell
        (hgx hxm) (hbx hxm))

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv
#print axioms MatedCRT.Lemma68HoneExitGeom.hb_ae_valid_centre_mesh

open Classical in
/-- **The one-test bound and the shell order at one radius, at one regular environment, with the pointwise shell order
derived (q4, fp-S4S6c-shell-pointwise).** This is `shellOneTest_at_of_goodEnv` with its named pointwise order `hShell`
replaced by the pointwise cores: `Lemma68ShellOrderPw.shellOrderAe_window_pw` (ShellOrderPw68.lean, the pointwise core of
`shellOrderAe_window`) and the pointwise shell hde `Lemma68ShellHdePw68.shellHde68_full_pw` (ShellHdePw68.lean, z1).
The environment facts at `ω` are fields of `RegularEnvAt68`: the continuity `Continuous (S.η ω)`, the adjacency of the open
cells at every scale (the last field, `Lemma68ShellEnvAe.map_cells_meet_ae`), and the killed exit, from the local finiteness
of the multiplicities (`Lemma68KilledExitAe.ae_killed_exit_ne_top`). The start is `hstart_of_fullAdmAt`
(HoneSetup239_68.lean). The mesh `hmesh` is the univ form, which implies the ball form used by `shellHde68_full_pw`.
The new named input is `htest`, the q3 testEnd finite-domain event of `shellOrderAe_window`, now at `ω`. The hypotheses
`hs₀` and `hrz` are binders of `shellOneTest_ae_fixedR_ae`, and they are kept. -/
theorem shellOneTest_at_of_goodEnv' {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (hrz : r ≤ countThreshold ζ) (hRA : r ≤ Lemma68Cutoff.rAmp q0 ζ)
    (ω₀ : ℝ) (hω0 : 0 < ω₀)
    (K : Constants68 γ ρ) (hK : K = shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1)
    (ω : Ω) (hreg : RegularEnvAt68 S γ ω₀ ρ CG ζ α CE ε ω)
    (i : Lemma68Config.Config68)
    -- eps threshold and exponents (named; q2 checking)
    (hεc : ε ≤ 16 * K.c0)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζ) ≤ K.c0 * r ^ 2 / 100)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζ)
    (hα : 2 * K.ω * K.βm < α)
    (hεs : ε ≤ ((100 * K.c0) ^ K.βm / 4) ^ (1 / (α - 2 * K.ω * K.βm)))
    (hrε : 10 * ε ^ K.ω ≤ r) (hε1 : ε ≤ 1)
    -- the mesh at the scale `dyadicD r` (pointwise at `ω`; the dyadic premise of `cellDiam_ae_dyadicD`)
    (hmesh : CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    -- the window route: the testEnd finite-domain event at the total window radius (named, as in `shellOrderAe_window`)
    (htest : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k x ≠ ⊤)
    (hadm : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i)
    -- the shell centres are short-eligible (walk form; named, see the report)
    (hEl : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x ∈
            shortEligible ρ (dyadicD r) (shortExp ζ))
    (hTdom : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ D : Set ℤ, D.Finite ∧ ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w ≤ vExitTime D w)
    (hRbd : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ s' : ℝ, ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ s')
    (hRr : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) ≤ 1)
    (hcap : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, cRad ε (S.η ω) (Finset.filter (fun v => v ∈ cellVertices ε (S.η ω) (Metric.ball z r)) i.A) < r)
    (hVolC : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) ^ K.βm)
            ≤ S.μ ω (ball (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat))
              (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x))))
    (hVolY : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4),
            ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4) ^ K.βm)
              ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)))
    (hGreen : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hCountGood : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hCellGood : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (Lemma68HoneCellGood.rhoCell68 ρ)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    (hRcell : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k x) / 4 < Lemma68HoneCellGood.rhoCell68 ρ - ρ)
    (hx1 : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ‖vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)‖
            < 1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 4)
    (hmomS : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
              ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
                (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                  ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    (hWalk : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)) ∧
            ε ^ K.ω ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ∧
            winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 8 ≤
              infDist (vertexPoint ε (S.η ω) (x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k x).toNat)) (sphere 0 ρ))
    (hsel : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ z ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (winRf S ρ ζ C r ω z) z)
    (hfull : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      ∀ w : ℂ, ∀ t : ℝ, 0 < t → 0 < S.μ ω (ball w t)) :
    ∃ Rf : ℂ → ℝ,
      ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
        (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
      Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
        (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a := by
  have hmult := hreg.2.2.1
  have hcont := hreg.2.2.2.1
  have hcellmeet := hreg.2.2.2.2.2.2.2.2
  have hkill := Lemma68KilledExitAe.ae_killed_exit_ne_top (hmult ε hε).1 (hmult ε hε).2 i.a ε (S.η ω) i.Θ i.F0 r
  have hmap := hcellmeet ε hε
  have hmesh' : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) ρ) :=
    fun k hk => hmesh k (by obtain ⟨x, hx, -⟩ := hk; exact ⟨x, hx, mem_univ _⟩)
  have hstart : Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty :=
    fun hFA => Lemma68HoneSetup239.hstart_of_fullAdmAt S hε hs₀ ω hcont r hr0 i hFA
  have hde := Lemma68ShellHdePw68.shellHde68_full_pw (ω := ω)
    (Rf := windowRfT S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) ω)
    (Elig := fun w => w ∈ shortEligible ρ (dyadicD r) (shortExp ζ)) S hε hs₀ hζ0 hζ1 hr0 hrz hrρ i hcont hmap hkill
    (fun w hw => windowRfT_bounds S.μ ρ (shortExp ζ) shellC068 C (dyadicD r) (dyadicD_pos r) (dyadicD_le_one r)
      (by unfold shortExp; linarith) ω hw)
    (fun _ hw => hw) hmesh' hstart htest
  have hShell := Lemma68ShellOrderPw.shellOrderAe_window_pw (c₀ := shellC068) (C := C) S ω hε hs₀ hζ0 hζ1 hr0 hrz
    hrρ i hcont hmap hkill hmesh hstart hde
  exact shellOneTest_at_of_goodEnv hγ0 hγ2 S hρ0 hρ1 hζ0 hζ1 hCG hq0 hq0c hε hr0 hrρ hRA ω₀ hω0 K hK ω hreg i
    hεc hεcell hωκ hα hεs hrε hε1 hmesh hShell hadm hEl hTdom hRbd hRr hcap hVolC hVolY hGreen hCountGood hCellGood
    hRcell hx1 hmomS hWalk hsel hfull

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_at_of_goodEnv'

open Classical in
/-- **The one-test bound and the shell order at one radius, at one regular environment, with the exit mesh localized to a ball
and the walk exponent split (q4, fp-S4S6c-goodenv-local).** This is `shellOneTest_at_of_goodEnv'` for the canonical CG route
(`ShellOneTestOrderAeCGStmt`, ShellHoneInst68.lean): the leaf constant is `K = shellKCG … CG` (`hK`), and the statement is
kept at this `K` (`K.C = CG`, `K.c0 = c₀(CG)`, `K.s1 = shellS1CG γ CG`). Changes against `shellOneTest_at_of_goodEnv'`:
* the univ mesh is replaced by the ball mesh `hmeshExit` at radius `ρ + dyadicD r / 100` (operator decision, 15:59 UTC; its
  producer is `hmeshExit_of_cellSize`, MeshExitPw68.lean);
* the walk exponent is split: `hκ2 : 2 * K.ω < κ` with `κ = 2/(2+γ)^2 - ζ` replaces `hωκ`; the second conjunct of `hWalk` is
  `ε ^ κ ≤ R/8` (the consumer leaf is q1's `_split` variant); `hα` and `hεs` keep `K.ω`;
* `hTdom` is replaced by the stopping-time finiteness `hstopFin` (q1, `shellOneTest_of_direct_ae_rcell_stopFin_rho`), and
  `hRbd` is discharged by `windowRfT_hRbd_global` (WindowRfGlobal68.lean);
* `hx1`, `hmomS`, `hVolY` are taken at the radius `ρmom = rhoCell68 ρ = (1+ρ)/2` (the leaf's `ρmom`);
* the cut `hcut : dyadicD r ^ shortExp ζ < rhoCell68 ρ - ρ` is the cut of `ShellOneTestOrderAeCGStmt`, and `hRcell` is dropped;
* the walk bound `hb` and the pointwise shell order `hShell` are the localized producers `hbLoc`, `hShellLoc` applied to
  `hmeshExit` (named until z12's WalkLoc68 and z1's pointwise localized order land);
* `hfull` is kept: `pos_iInf_annulus_ball` (HoneGoodEvent68.lean:119) needs the positivity of every ball of the annulus, not
  only `μ (ball x (c₀ R))` as chat 239 l.512-540 states. -/
theorem shellOneTest_at_of_goodEnv_loc {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ζ CG CE C α q0 s₀ ε r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hCG : 0 < CG)
    (_hq0 : 0 < q0) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE CG))
    (hε : 0 < ε) (_hs₀ : 0 < s₀) (hr0 : 0 < r) (hrρ : r ≤ ρ / 4) (_hrz : r ≤ countThreshold ζ)
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
    -- the exit mesh: the cells meeting the ball of radius `ρ + dyadicD r / 100` have diameter `≤ dyadicD r / 100`
    (hmeshExit : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (ρ + dyadicD r / 100)))
    -- named localized producers (z12 WalkLoc68: the walk bound; z1, z8: the pointwise shell order), at `hmeshExit`
    (hbLoc : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (ρ + dyadicD r / 100)) →
      ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1, ∀ᵐ x ∂srwLaw (S.mult ε ω) i.a,
        x ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r) (winRf S ρ ζ C r ω) k →
          x (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k x).toNat ∈
            cellVertices ε (S.η ω) (sphere (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k x)
              (4 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
                (dyadicD r ^ shortExp ζ) (dyadicD r) k x) / 3)))
    (hShellLoc : CellDiamLe ε (S.η ω) (dyadicD r / 100) (Metric.ball (0 : ℂ) (ρ + dyadicD r / 100)) →
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
    -- the walk second conjunct at the split exponent κ = 2/(2+γ)^2 - ζ (q1 `_split` leaf; not `K.ω`)
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
  obtain ⟨-, hcurve, hmult, hcont, hμN, hμF, -, -, -⟩ := hreg
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
  have hbω := hbLoc hmeshExit
  have hShell := hShellLoc hmeshExit hadm
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

/-- **Mesh bound on the visited set from the radius-`ρ` cell-size event (q4, fp-S4S6c-goodenv-loc).** The cells
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

/-- **Walk exponent `κ = 2/(2+γ)² - ζ` at a shell centre (q4, fp-S4S6c-goodenv-loc, q2 item 2).** The walk second
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

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_ae_fixedR

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_ae_fixedR_ae
#print axioms MatedCRT.Lemma68B1Assembly.cellDiamLe_F0_of_cellSize
#print axioms MatedCRT.Lemma68B1Assembly.rpow_kappa_le_div_eight
