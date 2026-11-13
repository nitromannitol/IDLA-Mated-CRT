import MatedCRT.FirstPass.S4S6c.HoneMomS68
import MatedCRT.FirstPass.SLERef.BG20
import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.S4S6c.BallExitMeas68
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68

/-!
# The rho_mom form of the exit-moment input

Chat 239 section 4 asks for the leaf binder `hmomS` at a deterministic radius `ρmom < 1`:
`S3cBridge.ExitMomentClause m μ η ε α C_exit ρmom`, with the test balls contained in `ball 0 ρmom`.

* The pathwise clause at `ρmom` is the first conjunct of the event in `ExitTimeUpperBoundStmt` (Draft
  `ExitTimeUpperBoundStmt`, MatedCRT/Draft/Section2.lean). It holds with polynomially high probability
  (`HarmonicBalls.PolyHighProb`), so it is extracted by monotonicity of the event (`polyHighProb_of_subset_event`).
  The bootstrap `S3cBridge.clauses_of_events` is not needed: the top-level statement already gives the clause at
  the radius `ρmom`.
* The containment of a test ball of radius `r` centred at `x` in `ball 0 ρ` follows from the margin `‖x‖ + r ≤ ρ`.
-/

namespace MatedCRT
namespace HoneMomS239

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- **The pathwise exit-moment clause at a deterministic radius `ρmom < 1`, with high probability.** From the
top-level statement `ExitTimeUpperBoundStmt 𝒮` (Draft), for every valid mated-CRT environment `S` the event
`{ω | ExitMomentClause (S.mult ε ω) (S.μ ω) (S.η ω) ε α C ρmom}` has polynomially high probability, with the
exponent `α` and the constant `C = C_exit(ρmom)` chosen before the environment. The constant depends on `ρmom`
only, so it is fixed before the scale `s₀` of the hone. -/
theorem exitMomentClause_rhoMom_polyHighProb {𝒮 : SpaceFillingSLEModel} (hE : ExitTimeUpperBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρmom : ℝ} (hρ0 : 0 < ρmom) (hρ1 : ρmom < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        HarmonicBalls.PolyHighProb S.P fun ε =>
          {ω | S3cBridge.ExitMomentClause (S.mult ε ω) (S.μ ω) (S.η ω) ε α C ρmom} := by
  obtain ⟨α, hα, hρ⟩ := hE γ hγ0 hγ2
  obtain ⟨C, hC, hPHP⟩ := hρ ρmom hρ0 hρ1
  exact ⟨α, hα, C, hC, fun Ω _ S hS =>
    polyHighProb_of_subset_event (hPHP Ω S hS) (fun _ _ hω => hω.1)⟩

/-- **Test-ball containment with a radius margin.** If `‖x‖ + r ≤ ρ`, the test ball `ball x r` lies in `ball 0 ρ`.
The margin is the input of the containment step: the centre `x` is a vertex of the exit cell,
and the cell diameter plus the test radius is below `ρmom`. -/
theorem testBall_sub_ballRho {x : ℂ} {r ρ : ℝ} (h : ‖x‖ + r ≤ ρ) : ball x r ⊆ ball (0 : ℂ) ρ :=
  Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)

namespace Shell

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68ShellIdent MatedCRT.Lemma68OmegaStop

/-- **Test-ball containment at the exit vertex.** The margin `hx1` at the
deterministic radius `ρmom` (ShellHoneInst68 `hx1` at `ρmom`) gives
`ball (vertexPoint ε η v) (R/4) ⊆ ball 0 ρmom`, where `v` is the exit vertex and `R = Rf (shellCentre k)`. -/
theorem exitBall_sub_ballRho {ε : ℝ} {η : ℝ → ℂ} {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d ρmom : ℝ} (k : ℕ)
    (ω : ℕ → ℤ)
    (hx1 : ‖vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)‖ <
      ρmom - Rf (shellCentre ε η Kset r s d k ω) / 4) :
    ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (Rf (shellCentre ε η Kset r s d k ω) / 4) ⊆ ball (0 : ℂ) ρmom := by
  apply testBall_sub_ballRho
  linarith

/-- **`hmomS` at the deterministic radius `ρmom`, in the binder form (`D ⊆ ball 0 ρmom`).** The pathwise clause
`ExitMomentClause m μ η ε α C_exit ρmom` of the environment (the event of `exitMomentClause_rhoMom_polyHighProb`) gives,
for every index `k ≤ n` and `P`-almost every walk `x` in `prefixSet` of the shell exit, the conclusion of the leaf
binder `hmomS` (ShellHoneInst68.lean:127) with the test sets in `ball 0 ρmom` in place of `ball 0 1`. -/
theorem hmomS_rhoMom {m : ℤ → ℤ → ℕ} {μ : Measure ℂ} {η : ℝ → ℂ} {ε α C_exit ρmom : ℝ}
    (hclause : S3cBridge.ExitMomentClause m μ η ε α C_exit ρmom)
    (A : Set ℤ) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞} (Kset : Set ℂ) (Rf : ℂ → ℝ) (r s d : ℝ) (a : ℤ) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a' ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a' N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N := by
  intro k _
  exact Filter.Eventually.of_forall fun x hx =>
    MatedCRT.HoneMomS68.hmomS_ballRho_of_clause
      (fun k' => prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k') τU)
      hclause k x hx

end Shell

end HoneMomS239
end MatedCRT
