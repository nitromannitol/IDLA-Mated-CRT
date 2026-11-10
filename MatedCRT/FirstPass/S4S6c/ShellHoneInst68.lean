import MatedCRT.FirstPass.S4S6c.HoneInputsDirect
import MatedCRT.FirstPass.S4S6c.HspRepair68
import MatedCRT.FirstPass.S4S6c.ShellChainGlue68
import MatedCRT.FirstPass.S4S6c.ShellChainCore68

/-!
# The Lemma 6.8 one-test bound at the shell times, and the reduction of `ShellChainCoreStmt` (q2, fp-S4S6c-hU-chain)

* `ShellOneTestAt m a A η ε K τU r s d Rf n q`: the walk-centred one-test bound on the shells `k ≤ n`, i.e. the hypothesis
  `hone` of `exitQ_le_pow_shell_walk` (S4S6c/ShellWire68.lean:29). The test end of shell `k` is taken at the shell exit
  `T_k = shellExit k` with radius `Rf(z_k)` at the grid centre `z_k = shellCentre k` (`shellWalkParam`, ShellIdent68).
* `shellOneTest_of_direct`: `ShellOneTestAt` from `hone_exitQ_walk_of_env_direct_repaired` (S4S6c/HspRepair68.lean:501) at the
  shell stopping times. The binders `hT` and `hR` of the direct hone are discharged for shells (`isStoppingTime_shellExit`,
  `measurable_shellRadius_stopped`). Every other binder is kept as a named hypothesis with the exact type obtained by the
  substitution `T k := shellExit k`, `R k := Rf(shellCentre k)`.
* `ShellOneTestOrderAeStmt 𝒮`: NAMED INPUT (the Q2 form, routed to the operator): the almost-sure, uniform-in-r pointwise
  statement of `ShellChainCoreStmt`, where for each good `(ω, r, i)` some radius configuration `Rf` gives the one-test
  bound and the shell order `ShellOrderAe` on the shells `k ≤ shellCount r s - 1`.
* `shellChainCoreStmt_of_oneTestOrder`: `ShellChainCoreStmt 𝒮` from `ShellOneTestOrderAeStmt 𝒮`, through `exitQ_core_step`.

Terminology: Armstrong-Kuusi-Mourrat (shells, good annuli, one-test bound), Armitage-Gardiner (exit times of balls).
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68ShellHoneInst

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The walk-centred one-test bound on the shells `k ≤ n`** (the hypothesis `hone` of `exitQ_le_pow_shell_walk`):
for each shell `k`, on the event that the walk reaches the prefix set `A` before the killed exit `τU`, the conditional
probability of the shell test failure is at most `1 - q`. -/
def ShellOneTestAt (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (η : ℝ → ℂ) (ε : ℝ) (Kset : Set ℂ) (τU : (ℕ → ℤ) → ℕ∞)
    (r s d : ℝ) (Rf : ℂ → ℝ) (n : ℕ) (q : ℝ) : Prop :=
  ∀ k ≤ n, ∀ᵐ x ∂(srwLaw m a), x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A
      (shellExit ε η Kset r s d Rf k) τU →
    (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (shellExit ε η Kset r s d Rf k)
      (Lemma68Window.testEndExit ε η (shellWalkParam ε η Kset r s d Rf k) (shellExit ε η Kset r s d Rf k))).indicator
      (fun _ => (1 : ℝ)) | (isStoppingTime_shellExit ε η Kset r s d Rf k).measurableSpace] x ≤ 1 - q

/-- **The one-test bound at the shell times, from the direct hone.** `hone_exitQ_walk_of_env_direct` at
`T k = shellExit k` and `R k = Rf ∘ shellCentre k`. The stopping-time and measurability binders are discharged;
the remaining binders are named with their exact substituted types (the source of each one is recorded in
`HoneInputsDirect.lean` and in the operator's list of open inputs). -/
theorem shellOneTest_of_direct {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    (Kset : Set ℂ) (Rf : ℂ → ℝ) (r s d q0 α C_exit C_good Dbl C : ℝ) {N_cov : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C))
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    -- NAMED (unsourced, routed 51b): integrability of the ball-exit radius moments on the shells
    (hmom1 : ∀ k, Integrable ({w | shellExit ε η Kset r s d Rf k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (shellWalkParam ε η Kset r s d Rf k w)
        (postTimePath (fun n w => w n) (shellExit ε η Kset r s d Rf k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | shellExit ε η Kset r s d Rf k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (shellWalkParam ε η Kset r s d Rf k w)
        (postTimePath (fun n w => w n) (shellExit ε η Kset r s d Rf k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    -- NAMED (configuration, Elig check on the walk): the shell radius lies in `[r², 1]` on the prefix set
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    -- NAMED (mass-relative sparsity of the configuration A in the test balls: `hsp` of
    -- `hone_exitQ_walk_of_env_direct_repaired`, HspRepair68.lean:501; z9, committed 9eb2a41)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ∀ w : ℂ, ε * ((A ∩ cellVertices ε η (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal)
    -- NAMED (scale range of the walk tests, and the volume lower bound of the good event)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    -- NAMED (volume lower bounds at the random radii `c₀ R` and `R/4`: `hVolC`, `hVolY` of the repaired hone)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ^ K.βm)
        ≤ μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω))))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - Rf (shellCentre ε η Kset r s d k ω) / 4),
        ENNReal.ofReal ((Rf (shellCentre ε η Kset r s d k ω) / 4) ^ K.βm)
          ≤ μ (ball y (Rf (shellCentre ε η Kset r s d k ω) / 4)))
    -- NAMED (lower Green bound, second conjunct of `GreenKernelLowerBoundStmt`)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    -- NAMED (the walk state lies in the domain of the Green bound, margin `R/8` to `∂B_ρc`)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
        ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
        Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
          infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    -- NAMED (lower half of Lemma 2.9 at `f ≡ 1`, for `D ⊆ B_ρc`)
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    -- NAMED (upper half of Lemma 2.8 at radius `ρc + 3/8`, P2 of the repaired hone)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) (ρc + 3 / 8)).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (Rf (shellCentre ε η Kset r s d k ω) / 4))) (ω (shellExit ε η Kset r s d Rf k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ε ^ α ≤ Rf (shellCentre ε η Kset r s d k ω) / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ε ^ α ≤ (Rf (shellCentre ε η Kset r s d k ω) / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈
        cellVertices ε η (sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ‖vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)‖
        < 1 - Rf (shellCentre ε η Kset r s d k ω) / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
        (2 * Rf (shellCentre ε η Kset r s d k ω)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k ω))))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal) :
    ShellOneTestAt m a A η ε Kset τU r s d Rf n (q0 / (1 + Real.log (1 / r)) ^ 2) := by
  exact hone_exitQ_walk_of_env_direct_repaired (T := fun k => shellExit ε η Kset r s d Rf k)
    (R := fun k w => Rf (shellCentre ε η Kset r s d k w)) K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c
    rfl hC hCw hCg (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) hmom1 hmom2 hRr hsp rmin hRmin hVolC hVolY hGreen
    hWalk hCountGood ζc hζc0 hζc1 hCellGood hεcell hfinE hsc hεα hεmass hb hx1 hmomS hgood hN hpos hdbl

/-- **NAMED INPUT (Q2 form, routed to the operator): the almost-sure, uniform-in-r shell chain.** This is
`ShellChainCoreStmt 𝒮` (ShellChainCore68.lean) with its conclusion replaced by the two pointwise inputs of
`exitQ_core_step`: the one-test bound `ShellOneTestAt` and the shell order `ShellOrderAe`, for some radius configuration
`Rf` at each good `(ω, r, i)`. The uniformity in `r` inside the almost-sure quantifier is the open point Q2. -/
def ShellOneTestOrderAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE R q0 s₀ : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 → 0 < q0 → q0 ≤ 1 → 0 < R → R ≤ ρ / 4 →
    R ≤ Lemma68Cutoff.rAmp q0 ζ → 0 < s₀ → s₀ < 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ < 1 / 5 ∧
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) c₀ C C' →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) c₀ C δ) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **`ShellChainCoreStmt` from the pointwise shell inputs.** Through `exitQ_core_step` (ShellChainGlue68.lean): the
count-indexed exit bound `∃ N, c_N r^{-ζ} ≤ N ∧ exitQ ≤ (1 - q₀/(1+log(1/r))²)^N` at each good `(ω, r, i)`, with the
radius range `r ≤ R ≤ rAmp q₀ ζ` and `0 < r ≤ 1` from the core hypotheses. -/
theorem shellChainCoreStmt_of_oneTestOrder {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeStmt 𝒮) :
    ShellChainCoreStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE R q0 s₀ hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 hq0 hq1 hR0 hRρ hRA hs₀ hs₁
  obtain ⟨c₀, hc0, hc1, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE R q0 s₀ hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 hq0 hq1 hR0 hRρ hRA hs₀ hs₁
  refine ⟨c₀, hc0, hc1, ?_⟩
  intro C C' hC hC' hP Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε
  refine (hcl C C' hC hC' hP Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε).mono ?_
  intro ω hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

end Lemma68ShellHoneInst
end MatedCRT
