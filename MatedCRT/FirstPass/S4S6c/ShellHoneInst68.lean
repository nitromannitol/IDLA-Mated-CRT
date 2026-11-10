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
open MatedCRT.Lemma68ConstOrder
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
    -- NAMED (sparsity of the configuration A at scale r, the clause `s₁ r^{2β}/ε` of the Lemma 6.8 event `E_ε`;
    -- `hL68` of `hone_exitQ_walk_of_env_direct_repaired`, HspRepair68.lean:502 at HEAD)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
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
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) hmom1 hmom2 hRr hL68 rmin hRmin hVolC hVolY hGreen
    hWalk hCountGood ζc hζc0 hζc1 hCellGood hεcell hfinE hsc hεα hεmass hb hx1 hmomS hgood hN hpos hdbl

/-- **NAMED INPUT (Q2 form, routed to the operator): the almost-sure, uniform-in-r shell chain.** This is
`ShellChainCoreStmt 𝒮` (ShellChainCore68.lean) with its conclusion replaced by the two pointwise inputs of
`exitQ_core_step`: the one-test bound `ShellOneTestAt` and the shell order `ShellOrderAe`, for some radius configuration
`Rf` at each good `(ω, r, i)`. The uniformity in `r` inside the almost-sure quantifier is the open point Q2. -/
def ShellOneTestOrderAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) shellC068 C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C δ) →
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
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
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε
  refine (hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε).mono ?_
  intro ω hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **`hrle` is derived, not a new input (q2, fp-S4S6c-core-side-hyps, item (c)).** For `0 < q₀ ≤ 1`, `0 < ζ < 1/2` and
`r ≤ R ≤ rAmp q₀ ζ`, the radius lies under the count threshold: `r ≤ countThreshold ζ`, by
`Lemma68ChainGlue.rAmp_le_countThreshold` (ShellChainGlue68.lean:53). The output `q₀ ≤ (1/4)²/(4 shellChone68 CE C) ≤ 1` of
`ShellOneTestOrderAeStmt` gives `q₀ ≤ 1`, so `ShellOneTestOrderAeStmt` needs no extra antecedent for it. -/
theorem radius_le_countThreshold_of_oneTest {q0 ζ R r : ℝ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1 / 2) (hRA : R ≤ Lemma68Cutoff.rAmp q0 ζ) (hr : r ≤ R) : r ≤ countThreshold ζ :=
  hr.trans (hRA.trans (Lemma68ChainGlue.rAmp_le_countThreshold hq0 hq1 hζ0 hζ1))

/-- **The leaf constants at the B1 parameters (q2, fp-S4S6c-core-side-hyps, item (d)).** `K = shellK68 γ ρ ω₀ ζ` has
`K.s1 = sparsityS1 γ` (the coefficient of `FullAdmAt`), `K.βm = chosenBetaMinus γ = (2+γ)²/2+1`, `K.c0 = shellC068 = exp(-2)/32`
and `K.ω = ω₀`. All four are definitional, so `K` is determined by the binders of `ShellOneTestOrderAeStmt`. -/
theorem shellK68_params (γ ρ ω₀ ζ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω0 : 0 < ω₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) :
    (Lemma68ShellConstants.shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).s1 = Lemma68Config.sparsityS1 γ ∧
    (Lemma68ShellConstants.shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).βm = chosenBetaMinus γ ∧
    (Lemma68ShellConstants.shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).c0 = shellC068 ∧
    (Lemma68ShellConstants.shellK68 γ ρ ω₀ ζ hγ0 hγ2 hρ0 hρ1 hω0 hζ0 hζ1).ω = ω₀ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`ShellOneTestOrderAeStmt` with the Eps antecedents (q2, fp-S4S6c-eps-chain).** The body of `ShellOneTestOrderAeStmt`, plus
`2 ω₀ β⁻ < α` and `2 ω₀ < 2/(2+γ)² - ζ` next to the `ω₀` hypotheses; `ε ≤ shellEps0 γ α ω₀` in the ε-clause; and the radius
cutoff `∀ r, 0 < r → r ≤ R → (dyadicD r)^{shortExp ζ} < rhoCell68 ρ - ρ` next to `R ≤ rAmp q0 ζ` (the cutoff of q1's hRcell).
The leaf binder `hωκ : K.ω ≤ 2/(2+γ)² - ζc` (HoneLeafAe68.lean:201) is `ω₀ ≤ 2/(2+γ)² - ζ` with `K.ω = ω₀`, `ζc = ζ`,
which is the existing `ω₀ < 2/(2+γ)² - ζ`. -/
def ShellOneTestOrderAeEpsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) shellC068 C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) shellC068 C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0Z γ α ω₀ ζ → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (Lemma68Config.sparsityS1 γ) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **`ShellOneTestOrderAeEpsStmt` at the Green constant `CG` (q2, fp-S4S6c-cg-param).** The body of
`ShellOneTestOrderAeEpsStmt` with the ball ratio `c₀(CG) = shellC0 CG` (the window constant of `WindowPrevAt` and
`badWindowOf`), the threshold `shellEps0ZCG γ α ω₀ ζ CG` and the sparsity `shellS1CG γ CG`. The leaf constant of this
statement is `shellKCG` (`K.C = CG`, `K.c0 = c₀(CG)`, `K.s1 = shellS1CG γ CG`). -/
def ShellOneTestOrderAeCGStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
    0 < ζ → ζ < 1 / 2 → 0 < ρ → ρ < 1 →
    ∀ C C' : ℝ, 0 < C → 0 < C' → WindowPrevAt γ (shortExp ζ) (shellC0 CG) C C' →
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ∧
    ∀ R : ℝ, 0 < R → R ≤ ρ / 4 → R ≤ Lemma68Cutoff.rAmp q0 ζ →
      (∀ r : ℝ, 0 < r → r ≤ R → (dyadicD r) ^ shortExp ζ < Lemma68HoneCellGood.rhoCell68 ρ - ρ) →
    ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      HarmonicBalls.PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) →
      HarmonicBalls.PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) →
      HarmonicBalls.PolyHighProb S.P (exitTimeEvent68 S α ρ CE) →
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEvent S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **Old implies Eps (q2, fp-S4S6c-eps-chain).** `ShellOneTestOrderAeStmt` specialises to `ShellOneTestOrderAeEpsStmt`: the
Eps antecedents are ignored, and the ε-clause is used for `ε ≤ shellEps0`. -/
theorem shellOneTestOrderAeEpsStmt_of_old {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeStmt 𝒮) :
    ShellOneTestOrderAeEpsStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ _ _ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA _ s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε _
  exact hcl R hR0 hRρ hRA s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε

/-- **`ShellChainCoreEpsStmt` from the Eps pointwise shell inputs (q2, fp-S4S6c-eps-chain).** Copy of
`shellChainCoreStmt_of_oneTestOrder` through `exitQ_core_step`, with the Eps antecedents and the radius cutoff passed on. -/
theorem shellChainCoreEpsStmt_of_oneTestOrderEps {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeEpsStmt 𝒮) :
    ShellChainCoreEpsStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hle
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **`ShellChainCoreCGStmt` from the CG Eps one-test order input (q2, fp-S4S6c-cg-param).** Copy of
`shellChainCoreEpsStmt_of_oneTestOrderEps` at `c₀(CG)`: the same proof, with the CG statements. -/
theorem shellChainCoreCGStmt_of_oneTestOrderCG {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeCGStmt 𝒮) :
    ShellChainCoreCGStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hle
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **`ShellOneTestOrderAeCGStmt` with the mesh-radius cell event (q2, fp-S4S6c-meshEventR; chat 252 §1).** The body of
`ShellOneTestOrderAeCGStmt`, with the cell-size hypothesis at the mesh radius `(1 + ρ)/2` (`rhoCell68 ρ`) and the almost sure
mesh clause on `meshEventR` (cell component at `(1 + ρ)/2`; Green and exit components at `ρ`). The leaf constant is
`shellKCG` as in `ShellOneTestOrderAeCGStmt`; its producer is open (q4 leaf, z5). -/
def ShellOneTestOrderAeCGRStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ω₀ α ζ ρ CG CE : ℝ,
    0 < ω₀ → ω₀ < α → 0 < α → ω₀ < 2 / (2 + γ) ^ 2 - ζ → 2 * ω₀ * chosenBetaMinus γ < α →
    2 * ω₀ < 2 / (2 + γ) ^ 2 - ζ → 0 < CG → 0 < CE →
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
    ∀ Ew : ℝ → Set Ω, (∀ δ : ℝ, MeasurableSet[S.fieldSigma] (Ew δ)) →
      HarmonicBalls.PolyHighProb S.P Ew →
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P, ω ∈ meshEventR S γ ω₀ ρ CG ζ α CE ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **`ShellChainCoreCGRStmt` from the CG mesh-radius one-test order input (q2, fp-S4S6c-meshEventR).** Copy of
`shellChainCoreCGStmt_of_oneTestOrderCG` with `ShellOneTestOrderAeCGRStmt` (cell at `(1+ρ)/2`, mesh clause `meshEventR`). -/
theorem shellChainCoreCGRStmt_of_oneTestOrderCGR {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeCGRStmt 𝒮) :
    ShellChainCoreCGRStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hle
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

/-- **The one-test order input with the counting component (q2, fp-S4S6c-goodevents-cgr).** As
`ShellOneTestOrderAeCGRStmt`, with the counting exponent `β > 0`, the counting hypothesis
`PolyHighProb (countingGoodEvent S α β ρ)` at the exit exponent `α` (named input `CountingAtExitAlphaStmt`, Guard68S10), and
the almost sure clause on `countingMeshEventR` (Green component `countingMeshEventR_green`, counting component
`countingMeshEventR_counting`, mesh component `countingMeshEventR_meshR`). This is the form the producer of the one-test hone
must have. -/
def ShellOneTestOrderAeCGRCStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
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
      (∀ δ : ℝ, ∀ᵐ ω ∂S.P, ω ∈ Ew δ → ω ∉ badWindowOf S.μ ρ (shortExp ζ) (shellC0 CG) C δ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ shellEps0ZCG γ α ω₀ ζ CG → ∀ᵐ ω ∂S.P,
        ω ∈ countingMeshEventR S γ ω₀ ρ CG ζ α CE β ε →
        Lemma68Inputs.CurveEscapesBothEnds (S.η ω) →
        (∀ ε' : ℝ, 0 < ε' → IsLocallyFiniteMult (S.mult ε' ω) ∧ ∀ k : ℤ, S.mult ε' ω k (k + 1) ≠ 0) →
        ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ R → ω ∈ Ew (dyadicD r) →
          ∀ i : Lemma68Config.Config68, Lemma68Config.FullAdmAt (shellS1CG γ CG) S ρ s₀ γ ε ω r i →
            ∃ Rf : ℂ → ℝ,
              ShellOneTestAt (S.mult ε ω) i.a (↑i.A : Set ℤ) (S.η ω) ε (fillCells ε (S.η ω) ↑i.Θ)
                (vExitTime (killed ε (S.η ω) i.Θ i.F0 r)) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (q0 / (1 + Real.log (1 / r)) ^ 2) ∧
              Lemma68ShellOrder.ShellOrderAe ε (S.η ω) i.Θ i.F0 r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf
                (shellCount r (dyadicD r ^ shortExp ζ) - 1) (S.mult ε ω) i.a

/-- **`ShellChainCoreCGRCStmt` from the counting one-test order input (q2, fp-S4S6c-goodevents-cgr).** Copy of
`shellChainCoreCGRStmt_of_oneTestOrderCGR` with `ShellOneTestOrderAeCGRCStmt` (counting exponent `β`, counting hypothesis,
mesh clause `countingMeshEventR`). -/
theorem shellChainCoreCGRCStmt_of_oneTestOrderCGRC {𝒮 : SpaceFillingSLEModel} (h : ShellOneTestOrderAeCGRCStmt 𝒮) :
    ShellChainCoreCGRCStmt 𝒮 := by
  intro γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  obtain ⟨q0, hq0, hq0c, hcl⟩ :=
    h γ hγ0 hγ2 ω₀ α ζ ρ CG CE β hω₀ hωα hα0 hωζ hexp1 hexp2 hCG hCE hβ hζ0 hζ1 hρ0 hρ1 C C' hC hC' hP
  have hq1 : q0 ≤ 1 := by
    have hC1 := one_le_shellChone68 CE C
    have hb : (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE C) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨q0, hq0, hq0c, ?_⟩
  intro R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω _ S hS hGp hCp hEp hKp Ew hEwm hEwp hav ε hε hle
  refine (hcl R hR0 hRρ hRA hcut s₀ hs₀ hs₁ Ω S hS hGp hCp hEp hKp Ew hEwm hEwp hav ε hε hle).mono ?_
  intro ω hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  obtain ⟨Rf, hone, hsh⟩ := hω hmesh hcurve hmult r hr1 hr2 hωE i hi
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hr1' : r ≤ 1 := by linarith
  exact Lemma68ChainGlue.exitQ_core_step S ε ω ζ q0 r Rf i hζ0 hζ1 hq0 hq1 hr0 hr1' (hr2.trans hRA) hone hsh
    (hmult ε hε).1 (hmult ε hε).2

end Lemma68ShellHoneInst
end MatedCRT

#print axioms MatedCRT.Lemma68ShellHoneInst.shellChainCoreCGRStmt_of_oneTestOrderCGR
#print axioms MatedCRT.Lemma68ShellHoneInst.shellChainCoreCGRCStmt_of_oneTestOrderCGRC
#print axioms MatedCRT.Lemma68ShellHoneInst.shellChainCoreStmt_of_oneTestOrder
#print axioms MatedCRT.Lemma68ShellHoneInst.shellOneTest_of_direct
#print axioms MatedCRT.Lemma68ShellHoneInst.radius_le_countThreshold_of_oneTest
#print axioms MatedCRT.Lemma68ShellHoneInst.shellK68_params
#print axioms MatedCRT.Lemma68ShellHoneInst.shellOneTestOrderAeEpsStmt_of_old
#print axioms MatedCRT.Lemma68ShellHoneInst.shellChainCoreEpsStmt_of_oneTestOrderEps
