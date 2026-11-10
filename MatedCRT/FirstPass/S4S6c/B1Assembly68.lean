import MatedCRT.FirstPass.S4S6c.HoneReduced68
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.ShellOrderWindow68
import MatedCRT.FirstPass.S4S6c.ShellConstants68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S6e.Geometry

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
    (hstart : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k x ≠ ⊤)
    -- environment inputs
    (hcurve : ∀ᵐ ω ∂S.P, Lemma68Inputs.CurveEscapesBothEnds (S.η ω))
    (hηc : ∀ᵐ ω ∂S.P, Continuous (S.η ω))
    (hμNull : ∀ᵐ ω ∂S.P, ∀ v : ℂ, S.μ ω {v} = 0)
    (hμFin : ∀ᵐ ω ∂S.P, IsFiniteMeasureOnCompacts (S.μ ω))
    -- the sphere centres and annulus centres of the leaf, as functions of the environment
    (Z : Ω → ℕ → (ℕ → ℤ) → ℂ)
    -- leaf binders (a.s.-in-`ω`)
    (hTdom : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ D : Set ℤ, D.Finite ∧ ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w ≤ vExitTime D w)
    (hRbd : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∃ s' : ℝ, ∀ w : ℕ → ℤ,
        shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w < ⊤ →
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ s')
    (hRr : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        r ^ 2 ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ∧
          winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) k w) ≤ 1)
    (hL68 : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ z : ℂ, (((↑i.A : Set ℤ) ∩ cellVertices ε (S.η ω) (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (hVolC : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ENNReal.ofReal ((K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)) ^ K.βm)
          ≤ S.μ ω (ball (vertexPoint ε (S.η ω)
              (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
                (winRf S ρ ζ C r ω) k w).toNat))
            (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k w))))
    (hVolY : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ∀ y ∈ ball (0 : ℂ) (1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4),
          ENNReal.ofReal ((winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4) ^ K.βm)
            ≤ S.μ ω (ball y (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
              (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4)))
    (hGreen : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ K.ω)), ∀ r' : ℝ, ε ^ K.ω ≤ r' →
        r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
        ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
          K.C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
              else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1
            ≤ greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hWalk : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
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
    (hCountGood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρ → ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
        ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂(S.μ ω) - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε (S.η ω) D, (1 : ℝ))
    (hCellGood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k' : ℤ, (cell ε (S.η ω) k' ∩ ball (0 : ℂ) (ρ + 3 / 8)).Nonempty →
        diam (cell ε (S.η ω) k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ))
    (hsc : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        4 * ε ^ α ≤ (S.μ ω (ball (vertexPoint ε (S.η ω)
            (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
              (winRf S ρ ζ C r ω) k w).toNat))
          (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)))).toReal)
    (hεα : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ε ^ α ≤ winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 100)
    (hεmass : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ε ^ α ≤ (winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
          (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4) ^ K.βm)
    (hb : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r)
            (winRf S ρ ζ C r ω) k w).toNat ∈ cellVertices ε (S.η ω)
          (sphere (Z ω k w) (4 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 3)))
    (hx1 : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ‖vertexPoint ε (S.η ω) (w (shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ)
            (dyadicD r) (winRf S ρ ζ C r ω) k w).toNat)‖
          < 1 - winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w) / 4)
    (hmomS : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
        ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
          exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
            ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ x in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - x‖) + 1) ∂(S.μ ω)) ^ N)
    (hgood : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        IsGoodAnnulusEvent (S.μ ω) K.c0 CG (winRf S ρ ζ C r ω (shellCentre ε (S.η ω)
          (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w)) (Z ω k w))
    (hpos : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ k : ℕ, ∀ w ∈ leafPre ε (S.η ω) i.Θ i.F0 i.A r (dyadicD r ^ shortExp ζ) (dyadicD r)
          (winRf S ρ ζ C r ω) k,
        0 < ⨅ y ∈ annulus (Z ω k w) (winRf S ρ ζ C r ω (shellCentre ε (S.η ω)
            (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k w))
          (2 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w)),
          S.μ ω (ball y (K.c0 * winRf S ρ ζ C r ω (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r
            (dyadicD r ^ shortExp ζ) (dyadicD r) k w))))
    (hdbl : ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
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
    ∀ᵐ ω ∂S.P, ω ∈ E → Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
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
    hGreen, hWalk, hCountGood, hCellGood, hsc, hεα, hεmass, hb, hx1, hmomS, hgood, hpos, hdbl]
    with ω hShω hmω hcω hηω hμNω hμFω hTω hRbω hRrω hLω hVCω hVYω hGω hWω hCGω hCeω hscω hεαω hεmω
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
  exact Lemma68HoneReduced.shellOneTest_of_direct_reduced68 (K := K) (ε := ε) (η := S.η ω) (hη := hηω)
    (hprop := Lemma68Geometry.tendsto_cocompact_of_escapes (hcω)) (hε := hε) (hεc := hεc)
    (μ := S.μ ω) (hμNull := hμNω) (m := S.mult ε ω) (a := i.a) (A := (↑i.A : Set ℤ))
    (hA := i.A.finite_toSet.measurableSet) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    (τU := vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) (Kset := fillCells ε (S.η ω) ↑i.Θ)
    (Rf := winRf S ρ ζ C r ω) (r := r) (s := dyadicD r ^ shortExp ζ) (d := dyadicD r) (q0 := q0) (α := α)
    (C_exit := CE) (C_good := CG) (Dbl := shellDbl68 CG) (C := shellChone68 CE CG) (N_cov := shellNcov68)
    (hr := hr0) (hr1 := hr1) (hq0c := hq0c) (hC := hC0) (hCw := shellChone68_hCw CE CG) (hCg := hCG.le)
    (hlf := (hmω).1) (hcons := (hmω).2) (hTdom := hTω hωE hadm) (hRbd := hRbω hωE hadm) (hRr := hRr')
    (hL68 := hLω hωE hadm) (rmin := K.c0 * r ^ 2) (hRmin := hRmin) (hVolC := hVCω hωE hadm)
    (hVolY := hVYω hωE hadm) (hGreen := hGω hωE hadm) (hWalk := hWω hωE hadm)
    (hCountGood := hCGω hωE hadm) (ζc := ζ) (hζc0 := hζ0) (hζc1 := by linarith)
    (hCellGood := hCeω hωE hadm) (hεcell := hεcell) (hsc := hscω hωE hadm) (Z := Z ω)
    (hεα := hεαω hωE hadm) (hεmass := hεmω hωE hadm) (hb := hbω hωE hadm) (hx1 := hx1ω hωE hadm)
    (hmomS := hmSω hωE hadm) (hgood := hgω hωE hadm)
    (hN := fun _ _ _ R' z' hR' => Lemma68ConstOrder.shellNcov68_spec R' z' hR')
    (hpos := hpω hωE hadm) (hdbl := hdω hωE hadm)

end Lemma68B1Assembly
end MatedCRT

#print axioms MatedCRT.Lemma68B1Assembly.shellOneTest_ae_fixedR
