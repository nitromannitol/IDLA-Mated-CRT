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

end Lemma68B1Assembly
end MatedCRT

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_ae_fixedR

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_ae_fixedR_ae
