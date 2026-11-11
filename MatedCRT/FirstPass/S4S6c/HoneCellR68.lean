import MatedCRT.FirstPass.S4S6c.HoneReduced68
import MatedCRT.FirstPass.S4S6c.HspRepair68
import MatedCRT.FirstPass.S4S6c.HoneCellGood68
import MatedCRT.FirstPass.S4S6c.HspRepairSplit68

/-!
# Walk-level one-test chain with the cell-control radius `ρcell`

`hone_exitQ_walk_of_env_cellR` is `hone_exitQ_walk_of_env_direct_repaired` (HspRepair68.lean:502) with the
cell-control binder moved from the radius `ρc + 3/8` to the radius `ρcell := (1 + ρc)/2`
 (HoneCellGood68.lean: `rhoCell68`). The test-ball diameter bound `hdiam` is `hdiam_test_ball_of_walk`
(HoneCellGood68.lean:110) instead of `hdiam_of_rmin68`, which needs `ρc + 3/8 ≤ ρ'`. The new prefix binder `hRcell`
(`R/4 < ρcell - ρc`) keeps the test balls `B(v, R/4)`, `v ∈ B_{ρc}`, inside `B_{ρcell}`. The exponent relation
`hωκ : K.ω ≤ κ` (`κ = 2/(2+γ)² - ζc`) is the one exponent input; `ε ≤ 1` follows from `ε ≤ 16 c₀` and `c₀ ≤ 1/24`.
Everything else is the body of `direct_repaired`, unchanged.
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68CellR

open Lemma68WalkBridge (coordFiltration)
open Lemma68ShellParam (measurable_coord_toNat_stop)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst

/-- Radius-`ρmom` generalization of `hone_exitQ_walk_of_env_cellR`: the radius `1` of the walk
chain is the parameter `ρmom` (`hx1`, `hVolY`/`hvol2`, `hmomS`, `hρS` read `ρmom` in place of `1`).
The radius-1 name is the wrapper at `ρmom := 1`. -/
theorem hone_exitQ_walk_of_env_cellR_rho {ρmom : ℝ} {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ENNReal.ofReal ((K.c0 * R k ω) ^ K.βm) ≤ μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (ρmom - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      R k ω / 4 < ρcell - ρc)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < ρmom - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  classical
  have hWalkNE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (cell ε η (ω (T k ω).toNat) ∩ ball (0 : ℂ) ρc).Nonempty := by
    intro k ω hω
    obtain ⟨⟨x, hxc, hxb⟩, -, -⟩ := hWalk k ω hω
    have h1 := mem_ball_zero_iff.mp hxb
    have h0 := Real.rpow_pos_of_pos hε K.ω
    exact ⟨x, hxc, mem_ball_zero_iff.mpr (by linarith)⟩
  have hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω := by
    intro k ω hω
    have hε1 : ε ≤ 1 := by linarith [K.hc0']
    exact MatedCRT.Lemma68HoneCellGood.hdiam_test_ball_of_walk (e := K.ω) (c0 := K.c0) (R := R k ω) hη hε hε1
      hωκ hρgap hCellGood (hWalk k ω hω).1 (hRcell k ω hω)
      (MatedCRT.Lemma68HoneCellGood.rpow_le_of_rmin hεcell (hRmin k ω hω)
        (mul_nonneg K.hc0.le (le_of_lt (lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1))))
  have hcellD : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) := by
    intro k ω hω p hp q hq
    obtain ⟨⟨x, hxc, hxb⟩, -, -⟩ := hWalk k ω hω
    have hxρ : x ∈ ball (0 : ℂ) ρcell := by
      have h1 := mem_ball_zero_iff.mp hxb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      exact mem_ball_zero_iff.mpr (by linarith)
    exact (dist_le_diam_cell_direct hη _ hp hq).trans (hCellGood _ ⟨x, hxc, hxρ⟩)
  have hsmallAll : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R k ω / 100 := by
    intro k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hrmin : rmin ≤ R k ω :=
      le_trans (hRmin k ω hω) (mul_le_of_le_one_left hRpos.le (by linarith [K.hc0']))
    linarith
  have hL29' : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
    intro k ω hω
    obtain ⟨⟨p, hpc, hpb⟩, -, hW3⟩ := hWalk k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hpnorm : ‖p‖ < ρc := by
      have h1 := mem_ball_zero_iff.mp hpb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      linarith
    have hvp : dist (vertexPoint ε η (ω (T k ω).toNat)) p < R k ω / 8 := by
      have h1 := hcellD k ω hω _ (vertexPoint_mem_cell_direct hε _) p hpc
      have h2 := hsmallAll k ω hω
      linarith
    have hfar : ∀ x ∈ sphere (0 : ℂ) ρc, R k ω / 8 ≤ dist (vertexPoint ε η (ω (T k ω).toNat)) x :=
      fun x hx => le_trans hW3 (infDist_le_dist_of_mem hx)
    have hD : ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω) ⊆ ball (0 : ℂ) ρc :=
      (ball_subset_ball (by nlinarith [K.hc0'])).trans
        (ball_subset_ball0_of_sphere_far hfar hpnorm hvp)
    obtain ⟨w, hw⟩ := exists_cellPoint_choice_direct (ε := ε) (η := η)
      (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))
    have hfinD : (cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).Finite :=
      (cellVertices_finite_of_isCompact hη hprop hε (isCompact_closedBall (0 : ℂ) ρc)).subset
        (fun k' hk' => Set.Nonempty.mono (inter_subset_inter_right _ (hD.trans ball_subset_closedBall)) hk')
    have hc := hCountGood _ hD w hw
    have hint : ∫ _ in ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω), (1 : ℝ) ∂μ
        = (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have hsum : ∑' _ : cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)), (1 : ℝ)
        = ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
      have := hfinD.fintype
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [hint, hsum] at hc
    exact hc
  have hβ2 : (2 : ℝ) ≤ K.βm := by nlinarith [K.hγ0, K.hβ, sq_nonneg γ]
  have hβ1 : (1 : ℝ) ≤ K.βm := by linarith
  have hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε * ((A ∩ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
    intro k ω hω
    exact Lemma68Centre.hsp_centre_of_lemma68 hη hprop hε K.hs1 hβ1 hβ2 K.hc0 K.hc0'
      (lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1) hr hr1 K.hs1small (hRr k ω hω).1 hL68
      ((ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top (μ := μ)).ne).mp (hVolC k ω hω))
  exact hone_exitQ_walk_of_env_repaired_rho K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2
    hRr hdiam hsp rmin hRmin hVolC hVolY hGreen hWalk hfinE hL29' hsc hεα hεmass hb (H := fun _ _ => ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (fun k ω hω p hp q hq => hcellD k ω hω p hp q hq) (fun k ω hω => hsmallAll k ω hω) hx1 hmomS hgood hN hpos hdbl

theorem hone_exitQ_walk_of_env_cellR {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ENNReal.ofReal ((K.c0 * R k ω) ^ K.βm) ≤ μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      R k ω / 4 < ρcell - ρc)
    (hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q
    := hone_exitQ_walk_of_env_cellR_rho (ρmom := 1) K ε η hη hprop hε hεc hμNull m a A hA n hr hr1
    hq0c hq hC hCw hCg hT hR hmom1 hmom2 hRr hL68 rmin hRmin hVolC hVolY hGreen hWalk hCountGood ζc
    hζc0 hζc1 ρcell hρgap hCellGood hRcell hωκ hεcell hfinE hsc hεα hεmass hb hx1 hmomS hgood hN
    hpos hdbl


-- ## Exponent-split variants
-- Hypotheses: hWalk second conjunct `ε ^ κ ≤ R k ω / 8` (κ = 2/(2+γ)^2 - ζc), hGreen at scale κ,
-- and `hκ2 : 2 * K.ω < κ` in place of `hωκ : K.ω ≤ κ`. The old declarations are unchanged.

/-- Radius-`ρmom` generalization of `hone_exitQ_walk_of_env_cellR_split`: the radius `1` of the walk
chain is the parameter `ρmom` (`hx1`, `hVolY`/`hvol2`, `hmomS`, `hρS` read `ρmom` in place of `1`).
The radius-1 name is the wrapper at `ρmom := 1`. -/
theorem hone_exitQ_walk_of_env_cellR_rho_split {ρmom : ℝ} {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ENNReal.ofReal ((K.c0 * R k ω) ^ K.βm) ≤ μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (ρmom - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      R k ω / 4 < ρcell - ρc)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < ρmom - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  classical
  have hωκ : K.ω ≤ 2 / (2 + γ) ^ 2 - ζc := by linarith [K.hω]
  have hWalkNE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (cell ε η (ω (T k ω).toNat) ∩ ball (0 : ℂ) ρc).Nonempty := by
    intro k ω hω
    obtain ⟨⟨x, hxc, hxb⟩, -, -⟩ := hWalk k ω hω
    have h1 := mem_ball_zero_iff.mp hxb
    have h0 := Real.rpow_pos_of_pos hε K.ω
    exact ⟨x, hxc, mem_ball_zero_iff.mpr (by linarith)⟩
  have hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω := by
    intro k ω hω
    have hε1 : ε ≤ 1 := by linarith [K.hc0']
    exact MatedCRT.Lemma68HoneCellGood.hdiam_test_ball_of_walk (e := K.ω) (c0 := K.c0) (R := R k ω) hη hε hε1
      hωκ hρgap hCellGood (hWalk k ω hω).1 (hRcell k ω hω)
      (MatedCRT.Lemma68HoneCellGood.rpow_le_of_rmin hεcell (hRmin k ω hω)
        (mul_nonneg K.hc0.le (le_of_lt (lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1))))
  have hcellD : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) := by
    intro k ω hω p hp q hq
    obtain ⟨⟨x, hxc, hxb⟩, -, -⟩ := hWalk k ω hω
    have hxρ : x ∈ ball (0 : ℂ) ρcell := by
      have h1 := mem_ball_zero_iff.mp hxb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      exact mem_ball_zero_iff.mpr (by linarith)
    exact (dist_le_diam_cell_direct hη _ hp hq).trans (hCellGood _ ⟨x, hxc, hxρ⟩)
  have hsmallAll : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R k ω / 100 := by
    intro k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hrmin : rmin ≤ R k ω :=
      le_trans (hRmin k ω hω) (mul_le_of_le_one_left hRpos.le (by linarith [K.hc0']))
    linarith
  have hL29' : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
    intro k ω hω
    obtain ⟨⟨p, hpc, hpb⟩, -, hW3⟩ := hWalk k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hpnorm : ‖p‖ < ρc := by
      have h1 := mem_ball_zero_iff.mp hpb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      linarith
    have hvp : dist (vertexPoint ε η (ω (T k ω).toNat)) p < R k ω / 8 := by
      have h1 := hcellD k ω hω _ (vertexPoint_mem_cell_direct hε _) p hpc
      have h2 := hsmallAll k ω hω
      linarith
    have hfar : ∀ x ∈ sphere (0 : ℂ) ρc, R k ω / 8 ≤ dist (vertexPoint ε η (ω (T k ω).toNat)) x :=
      fun x hx => le_trans hW3 (infDist_le_dist_of_mem hx)
    have hD : ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω) ⊆ ball (0 : ℂ) ρc :=
      (ball_subset_ball (by nlinarith [K.hc0'])).trans
        (ball_subset_ball0_of_sphere_far hfar hpnorm hvp)
    obtain ⟨w, hw⟩ := exists_cellPoint_choice_direct (ε := ε) (η := η)
      (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))
    have hfinD : (cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).Finite :=
      (cellVertices_finite_of_isCompact hη hprop hε (isCompact_closedBall (0 : ℂ) ρc)).subset
        (fun k' hk' => Set.Nonempty.mono (inter_subset_inter_right _ (hD.trans ball_subset_closedBall)) hk')
    have hc := hCountGood _ hD w hw
    have hint : ∫ _ in ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω), (1 : ℝ) ∂μ
        = (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have hsum : ∑' _ : cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)), (1 : ℝ)
        = ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
      have := hfinD.fintype
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [hint, hsum] at hc
    exact hc
  have hβ2 : (2 : ℝ) ≤ K.βm := by nlinarith [K.hγ0, K.hβ, sq_nonneg γ]
  have hβ1 : (1 : ℝ) ≤ K.βm := by linarith
  have hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε * ((A ∩ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
    intro k ω hω
    exact Lemma68Centre.hsp_centre_of_lemma68 hη hprop hε K.hs1 hβ1 hβ2 K.hc0 K.hc0'
      (lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1) hr hr1 K.hs1small (hRr k ω hω).1 hL68
      ((ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top (μ := μ)).ne).mp (hVolC k ω hω))
  exact hone_exitQ_walk_of_env_repaired_rho_split K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2
    hRr hdiam hsp rmin hRmin hVolC hVolY ζc hζc0 hζc1 hGreen hWalk hfinE hL29' hsc hεα hεmass hb (H := fun _ _ => ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (fun k ω hω p hp q hq => hcellD k ω hω p hp q hq) (fun k ω hω => hsmallAll k ω hω) hx1 hmomS hgood hN hpos hdbl

theorem hone_exitQ_walk_of_env_cellR_split {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ENNReal.ofReal ((K.c0 * R k ω) ^ K.βm) ≤ μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      R k ω / 4 < ρcell - ρc)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q
    := hone_exitQ_walk_of_env_cellR_rho_split (ρmom := 1) K ε η hη hprop hε hεc hμNull m a A hA n hr hr1
    hq0c hq hC hCw hCg hT hR hmom1 hmom2 hRr hL68 rmin hRmin hVolC hVolY ζc hζc0 hζc1 hGreen hWalk hCountGood ρcell hρgap hCellGood hRcell hκ2 hεcell hfinE hsc hεα hεmass hb hx1 hmomS hgood hN
    hpos hdbl

end Lemma68CellR
end MatedCRT

#print axioms MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR


#print axioms MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR_rho

#print axioms MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR_rho_split
#print axioms MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR_split
