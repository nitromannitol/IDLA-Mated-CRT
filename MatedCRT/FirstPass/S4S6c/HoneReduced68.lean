import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.BallExitMeas68
import MatedCRT.FirstPass.S4S6c.FiniteExitMoment68
import MatedCRT.Audit.StatementsSec3Sec5M1

/-!
# Lemma 6.8, one-test leaf with the committed dischargers plugged in

`shellOneTest_of_direct_reduced68` is `shellOneTest_of_direct` (ShellHoneInst68.lean:53) with the binders that a committed
lemma discharges removed, and the discharging lemma's own binders added. Conclusion unchanged.

Binder table (outer binder : status)
* `hmom1`, `hmom2` : DISCHARGED by `hmom_pair_of_finiteDomain_meas` (BallExitMeas68.lean:49), at `T k = shellExit k`,
  `R k = Rf ∘ shellCentre k`. Its own binders become binders of this theorem: `hlf`, `hcons`, `hTdom`, `hRbd`
  (routed 60e).
* `hfinE` : DISCHARGED by `MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime` (Audit/StatementsSec3Sec5M1.lean:441)
  on the interior cell set of the test ball, which is finite by `TraceInputs68.cellVertices_finite_of_tendsto`
  (TraceInputs68.lean:76). Uses the shared binders `hlf`, `hcons`.
* All other binders stay as binders.
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneReduced

open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst

/-- **The one-test bound at the shell times, reduced.** The discharged binders `hmom1`, `hmom2`, `hfinE` of
`shellOneTest_of_direct` are replaced by their committed dischargers; `hlf`, `hcons`, `hTdom`, `hRbd` are the binders of
`hmom_pair_of_finiteDomain_meas`. -/
theorem shellOneTest_of_direct_reduced68 {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    (Kset : Set ℂ) (Rf : ℂ → ℝ) (r s d q0 α C_exit C_good Dbl C : ℝ) {N_cov : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C))
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    -- Own binders of `hmom_pair_of_finiteDomain_meas`: the walk multiplicity is locally finite and has positive edges
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    -- Own binders of `hmom_pair_of_finiteDomain_meas`: the shell exit time is dominated by a finite exit time,
    -- and the shell radius is bounded on `{T < ⊤}`
    (hTdom : ∀ k, ∃ D : Set ℤ, D.Finite ∧ ∀ w, shellExit ε η Kset r s d Rf k w < ⊤ →
      shellExit ε η Kset r s d Rf k w ≤ vExitTime D w)
    (hRbd : ∀ k, ∃ s' : ℝ, ∀ w, shellExit ε η Kset r s d Rf k w < ⊤ →
      Rf (shellCentre ε η Kset r s d k w) ≤ s')
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ^ K.βm)
        ≤ μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω))))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - Rf (shellCentre ε η Kset r s d k ω) / 4),
        ENNReal.ofReal ((Rf (shellCentre ε η Kset r s d k ω) / 4) ^ K.βm)
          ≤ μ (ball y (Rf (shellCentre ε η Kset r s d k ω) / 4)))
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
        ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
        Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
          infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) (ρc + 3 / 8)).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
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
  -- the walk-centred hmom pair at the shell times (BallExitMeas68.lean:49)
  have hpair := fun k : ℕ => BallExitMeas68.hmom_pair_of_finiteDomain_meas hlf hcons hη hprop hε a
    (T := fun k => shellExit ε η Kset r s d Rf k) (R := fun k w => Rf (shellCentre ε η Kset r s d k w))
    (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) hTdom hRbd k
  -- the finite-domain expected exit time (Audit/StatementsSec3Sec5M1.lean:441) on the interior cells of the test ball
  have hfinD : ∀ (x : ℂ) (ρ : ℝ), (interiorCellVertices ε η (ball x ρ)).Finite := fun x ρ =>
    (TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball).subset fun _ hk => hk.1
  exact MatedCRT.Lemma68ShellHoneInst.shellOneTest_of_direct K ε η hη hprop hε hεc hμNull m a A hA n Kset Rf r s d q0 α
    C_exit C_good Dbl C hr hr1 hq0c hC hCw hCg (fun k => (hpair k).1) (fun k => (hpair k).2) hRr hL68 rmin hRmin hVolC
    hVolY hGreen hWalk hCountGood ζc hζc0 hζc1 hCellGood hεcell
    (fun k ω _ => MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons
      (hfinD _ _) _)
    hsc hεα hεmass hb hx1 hmomS hgood hN hpos hdbl

#print axioms shellOneTest_of_direct_reduced68

end Lemma68HoneReduced
end MatedCRT
