import MatedCRT.FirstPass.S4S6c.HoneLeafAe68

/-!
# Free Green exponent variants of the exponent-split walk chain (fp-S4S6c-green-exp-generic, q1)

Variants (suffix `_gexp`) of `hone_exitQ_walk_of_env_repaired_rho_split` (HspRepairSplit68),
`hone_exitQ_walk_of_env_cellR_rho_split` (HoneCellR68), `hone_exitQ_walk_of_env_direct_ae_rho_split` and
`shellOneTest_of_direct_ae_rcell_stopFin_rho_split` (HoneLeafAe68). The old declarations are unchanged.

The Green exponent is a free real `ωg`: `hGreen` quantifies over radii `ε ^ ωg ≤ r` (the radius condition of
`greenLowEvent68 S ωg ρ CG`, UniformEvents.lean:32), and the second conjunct of `hWalk` is `ε ^ ωg ≤ R k ω / 8`.
The exponent `κ = 2/(2+γ)^2 - ζc` stays in `hCellGood`, `hεcell` and the cell bounds (`hκ2 : 2 * K.ω < κ`).
The vertex ball of `hGreen` and of the first conjunct of `hWalk` stays at `ε ^ K.ω`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
open Lemma68WalkBridge (coordFiltration)
open Lemma68ShellParam (measurable_coord_toNat_stop)
namespace Lemma68Window

/-- Radius-`ρmom` generalization of `hone_exitQ_walk_of_env_repaired` (fp-S4S6c-hsp-rhomom): the radius `1` of the walk
chain is the parameter `ρmom` (`hx1`, `hVolY`/`hvol2`, `hmomS`, `hρS` read `ρmom` in place of `1`).
The radius-1 name is the wrapper at `ρmom := 1`. -/
theorem hone_exitQ_walk_of_env_repaired_rho_gexp {ρmom : ℝ} {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
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
    (hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε * ((A ∩ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ)
        ≤ (1 / 16 : ℝ) * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    (rmin : ℝ)
    (_hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ENNReal.ofReal ((K.c0 * R k ω) ^ K.βm) ≤ μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (ρmom - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
    (ζc : ℝ) (_hζc0 : 0 < ζc) (_hζc1 : ζc < 1)
    (ωg : ℝ)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ ωg ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ ωg ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hL29 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ))
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ} {H : ℕ → (ℕ → ℤ) → ℝ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hcell : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ H k ω)
    (hh : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, H k ω ≤ R k ω / 100)
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
  have hρS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4) ⊆ ball 0 ρmom := by
    intro k ω hω u hu
    have hx := hx1 k ω hω
    have hd : ‖u - vertexPoint ε η (ω (T k ω).toNat)‖ < R k ω / 4 := by
      simpa [dist_eq_norm] using hu
    have htri := norm_add_le (vertexPoint ε η (ω (T k ω).toNat)) (u - vertexPoint ε η (ω (T k ω).toNat))
    have hsum : vertexPoint ε η (ω (T k ω).toNat) + (u - vertexPoint ε η (ω (T k ω).toNat)) = u := by ring
    rw [hsum] at htri
    rw [mem_ball_zero_iff]
    linarith
  have hRpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, 0 < R k ω :=
    fun k ω hω => lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
  have hcR : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      K.c0 * R k ω ≤ R k ω / 24 := fun k ω hω => by
    have h := mul_le_mul_of_nonneg_right K.hc0' (hRpos k ω hω).le
    linarith
  obtain ⟨hvol, hvol2⟩ := hvol_of_direct_rho K ε η hVolC hVolY
  have hGrLow : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)),
      K.C⁻¹ * Real.log (if vertexPoint ε η (ω (T k ω).toNat) = vertexPoint ε η b then ε⁻¹
            else min ((R k ω / 8) / ‖vertexPoint ε η (ω (T k ω).toNat) - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
            (ω (T k ω).toNat) b := by
    intro k ω hω b hb
    obtain ⟨hA1, hA2, hA3⟩ := hWalk k ω hω
    have hsub : ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω) ⊆
        ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8 / 3) :=
      ball_subset_ball (by linarith [hcR k ω hω])
    exact hGreen (ω (T k ω).toNat) hA1 (R k ω / 8) hA2 hA3 b
      (Set.Nonempty.mono (Set.inter_subset_inter_right _ hsub) hb)
  exact hone_exitQ_walk_massRel_rho K ε η hη hprop hε hεc m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2 hRr hdiam hsp
    hvol (fun k ω hω b hb => ⟨HcGreen68.greenKernel_le_greenFn m _ _ b, hGrLow k ω hω b hb⟩)
    hfinE hL29 hsc (Z := Z) (H := H) (Rb := fun _ _ => ρmom) hεα hεmass hb hcell hh hx1 hvol2 hρS hmomS hgood hN hpos
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) (fun k ω _ v _ => hμNull v)
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) hdbl

end Lemma68Window
end MatedCRT

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

/-- Radius-`ρmom` generalization of `hone_exitQ_walk_of_env_cellR_split` (fp-S4S6c-hsp-rhomom): the radius `1` of the walk
chain is the parameter `ρmom` (`hx1`, `hVolY`/`hvol2`, `hmomS`, `hρS` read `ρmom` in place of `1`).
The radius-1 name is the wrapper at `ρmom := 1`. -/
theorem hone_exitQ_walk_of_env_cellR_rho_gexp {ρmom : ℝ} {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
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
    (ωg : ℝ)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ ωg ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ ωg ≤ R k ω / 8 ∧
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
  exact hone_exitQ_walk_of_env_repaired_rho_gexp K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2
    hRr hdiam hsp rmin hRmin hVolC hVolY ζc hζc0 hζc1 ωg hGreen hWalk hfinE hL29' hsc hεα hεmass hb (H := fun _ _ => ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (fun k ω hω p hp q hq => hcellD k ω hω p hp q hq) (fun k ω hω => hsmallAll k ω hω) hx1 hmomS hgood hN hpos hdbl

end Lemma68CellR
end MatedCRT

namespace MatedCRT
namespace Lemma68LeafAe
open Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent
open MatedCRT.Lemma68ShellHoneInst

/-- Radius-`ρmom` generalization of `hone_exitQ_walk_of_env_direct_ae` (fp-S4S6c-hsp-rhomom): the radius `1` of the walk
chain is the parameter `ρmom` (`hx1`, `hVolY`/`hvol2`, `hmomS`, `hρS` read `ρmom` in place of `1`).
The radius-1 name is the wrapper at `ρmom := 1`. -/
theorem hone_exitQ_walk_of_env_direct_ae_rho_gexp {ρmom : ℝ} {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k ≤ n, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k ≤ n, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      r ^ 2 ≤ R k x ∧ R k x ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      rmin ≤ K.c0 * R k x)
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ENNReal.ofReal ((K.c0 * R k x) ^ K.βm) ≤ μ (ball (vertexPoint ε η (x (T k x).toNat)) (K.c0 * R k x)))
    (hVolY : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ y ∈ ball (0 : ℂ) (ρmom - R k x / 4), ENNReal.ofReal ((R k x / 4) ^ K.βm) ≤ μ (ball y (R k x / 4)))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ωg : ℝ)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ ωg ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      x (T k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ ωg ≤ R k x / 8 ∧
        R k x / 8 ≤ infDist (vertexPoint ε η (x (T k x).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hRcell : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
        R k x / 4 < ρcell - ρc)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (x (T k x).toNat)) (R k x / 4)))
        (x (T k x).toNat) ≠ ⊤)
    (hsc : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (T k x).toNat)) (K.c0 * R k x))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ε ^ α ≤ R k x / 100)
    (hεmass : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ε ^ α ≤ (R k x / 4) ^ K.βm)
    (hb : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      x (T k x).toNat ∈ cellVertices ε η (sphere (Z k x) (4 * R k x / 3)))
    (hx1 : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ‖vertexPoint ε η (x (T k x).toNat)‖ < ρmom - R k x / 4)
    (hmomS : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      IsGoodAnnulusEvent μ K.c0 C_good (R k x) (Z k x))
    (hN : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      0 < ⨅ w ∈ annulus (Z k x) (R k x) (2 * R k x), μ (ball w (K.c0 * R k x)))
    (hdbl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU →
      (μ (ball (vertexPoint ε η (x (T k x).toNat)) (3 * K.c0 * R k x))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (x (T k x).toNat)) (K.c0 * R k x))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ))
          | (hT k).measurableSpace] x ≤ 1 - q := by
  classical
  obtain ⟨B1, hB1a, hB1⟩ := exists_bad_walks n (srwLaw m a) hRr
  obtain ⟨B2, hB2a, hB2⟩ := exists_bad_walks n (srwLaw m a) hRmin
  obtain ⟨B3, hB3a, hB3⟩ := exists_bad_walks n (srwLaw m a) hVolC
  obtain ⟨B4, hB4a, hB4⟩ := exists_bad_walks n (srwLaw m a) hVolY
  obtain ⟨B5, hB5a, hB5⟩ := exists_bad_walks n (srwLaw m a) hWalk
  obtain ⟨B6, hB6a, hB6⟩ := exists_bad_walks n (srwLaw m a) hfinE
  obtain ⟨B7, hB7a, hB7⟩ := exists_bad_walks n (srwLaw m a) hsc
  obtain ⟨B8, hB8a, hB8⟩ := exists_bad_walks n (srwLaw m a) hεα
  obtain ⟨B9, hB9a, hB9⟩ := exists_bad_walks n (srwLaw m a) hεmass
  obtain ⟨B10, hB10a, hB10⟩ := exists_bad_walks n (srwLaw m a) hb
  obtain ⟨B11, hB11a, hB11⟩ := exists_bad_walks n (srwLaw m a) hx1
  obtain ⟨B12, hB12a, hB12⟩ := exists_bad_walks n (srwLaw m a) hmomS
  obtain ⟨B13, hB13a, hB13⟩ := exists_bad_walks n (srwLaw m a) hgood
  obtain ⟨B14, hB14a, hB14⟩ := exists_bad_walks n (srwLaw m a) hN
  obtain ⟨B15, hB15a, hB15⟩ := exists_bad_walks n (srwLaw m a) hpos
  obtain ⟨B16, hB16a, hB16⟩ := exists_bad_walks n (srwLaw m a) hdbl
  obtain ⟨B17, hB17a, hB17⟩ := exists_bad_walks n (srwLaw m a) hRcell
  obtain ⟨B, hBeq⟩ : ∃ B : Set (ℕ → ℤ), B = B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ B8 ∪ B9 ∪ B10 ∪ B11 ∪ B12 ∪ B13 ∪ B14 ∪ B15 ∪ B16 ∪ B17 :=
    ⟨_, rfl⟩
  have hBa : ∀ᵐ x ∂srwLaw m a, x ∉ B := by
    filter_upwards [hB1a, hB2a, hB3a, hB4a, hB5a, hB6a, hB7a, hB8a, hB9a, hB10a, hB11a, hB12a, hB13a, hB14a,
      hB15a, hB16a, hB17a] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [hBeq]
    intro hx
    simp only [Set.mem_union] at hx
    tauto
  have sub1 : B1 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub2 : B2 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub3 : B3 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub4 : B4 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub5 : B5 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub6 : B6 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub7 : B7 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub8 : B8 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub9 : B9 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub10 : B10 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub11 : B11 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub12 : B12 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub13 : B13 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub14 : B14 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub15 : B15 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub16 : B16 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have sub17 : B17 ⊆ B := by rw [hBeq]; intro x hx; simp [hx]
  have hRcell' := trim_binder sub17 hB17 (Φ' := fun k x => Rn R n k x / 4 < ρcell - ρc)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hRr' := trim_binder sub1 hB1 (Φ' := fun k x => r ^ 2 ≤ Rn R n k x ∧ Rn R n k x ≤ 1)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hRmin' := trim_binder sub2 hB2 (Φ' := fun k x => rmin ≤ K.c0 * Rn R n k x)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hVolC' := trim_binder sub3 hB3
    (Φ' := fun k x => ENNReal.ofReal ((K.c0 * Rn R n k x) ^ K.βm) ≤
      μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (K.c0 * Rn R n k x)))
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hVolY' := trim_binder sub4 hB4
    (Φ' := fun k x => ∀ y ∈ ball (0 : ℂ) (ρmom - Rn R n k x / 4),
      ENNReal.ofReal ((Rn R n k x / 4) ^ K.βm) ≤ μ (ball y (Rn R n k x / 4)))
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hWalk' := trim_binder sub5 hB5
    (Φ' := fun k x => x (Tn T n k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
      ε ^ ωg ≤ Rn R n k x / 8 ∧
        Rn R n k x / 8 ≤ infDist (vertexPoint ε η (x (Tn T n k x).toNat)) (sphere 0 ρc))
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hfinE' := trim_binder sub6 hB6
    (Φ' := fun k x => expectedExitTime m
      (interiorCellVertices ε η (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (Rn R n k x / 4)))
      (x (Tn T n k x).toNat) ≠ ⊤)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hsc' := trim_binder sub7 hB7
    (Φ' := fun k x => 4 * ε ^ α ≤
      (μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (K.c0 * Rn R n k x))).toReal)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hεα' := trim_binder sub8 hB8 (Φ' := fun k x => ε ^ α ≤ Rn R n k x / 100)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hεmass' := trim_binder sub9 hB9 (Φ' := fun k x => ε ^ α ≤ (Rn R n k x / 4) ^ K.βm)
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hb' := trim_binder sub10 hB10
    (Φ' := fun k x => x (Tn T n k x).toNat ∈ cellVertices ε η (sphere (Z k x) (4 * Rn R n k x / 3)))
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hx1' := trim_binder sub11 hB11
    (Φ' := fun k x => ‖vertexPoint ε η (x (Tn T n k x).toNat)‖ < ρmom - Rn R n k x / 4)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hmomS' := trim_binder sub12 hB12 (Φ' := fun k x => ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom →
      ENNReal.ofReal (ε ^ α) ≤ μ D → ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (fun k hk x h => h)
  have hgood' := trim_binder sub13 hB13
    (Φ' := fun k x => IsGoodAnnulusEvent μ K.c0 C_good (Rn R n k x) (Z k x))
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hN' := trim_binder sub14 hB14 (Φ' := fun k x => ∀ (R' : ℝ) (z' : ℂ), 0 < R' →
      ∃ t : Finset ℂ, t.card ≤ N_cov ∧ (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧
        annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (fun k hk x h => h)
  have hpos' := trim_binder sub15 hB15
    (Φ' := fun k x => 0 < ⨅ w ∈ annulus (Z k x) (Rn R n k x) (2 * Rn R n k x), μ (ball w (K.c0 * Rn R n k x)))
    (fun k hk x h => by simpa only [Rn_of_le hk] using h)
  have hdbl' := trim_binder sub16 hB16
    (Φ' := fun k x => (μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (3 * K.c0 * Rn R n k x))).toReal
      ≤ Dbl * (μ (ball (vertexPoint ε η (x (Tn T n k x).toNat)) (K.c0 * Rn R n k x))).toReal)
    (fun k hk x h => by simpa only [Rn_of_le hk, Tn_of_le hk] using h)
  have hmom1' : ∀ k, Integrable ({w | Tn T n k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (Rn R n k) (Tn T n k) w)
        (postTimePath (fun n w => w n) (Tn T n k) w) : ℕ) : ℝ))) (srwLaw m a) := by
    intro k
    by_cases hk : k ≤ n
    · simp only [Tn_of_le hk, Rn_of_le hk]; exact hmom1 k hk
    · simp only [Tn_of_not_le hk]; simp
  have hmom2' : ∀ k, Integrable ({w | Tn T n k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (Rn R n k) (Tn T n k) w)
        (postTimePath (fun n w => w n) (Tn T n k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a) := by
    intro k
    by_cases hk : k ≤ n
    · simp only [Tn_of_le hk, Rn_of_le hk]; exact hmom2 k hk
    · simp only [Tn_of_not_le hk]; simp
  have hone := MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR_rho_gexp K ε η hη hprop hε hεc hμNull m a A hA n
    (τU := Bᶜ.indicator τU) hr hr1 hq0c hq hC hCw hCg (T := Tn T n) (hT := isStoppingTime_Tn n hT)
    (R := Rn R n) (hR := measurable_Rn n hT hR) (hmom1 := hmom1') (hmom2 := hmom2') (hRr := hRr')
    (hL68 := hL68) (rmin := rmin) (hRmin := hRmin') (hVolC := hVolC') (hVolY := hVolY') (ωg := ωg) (hGreen := hGreen)
    (hWalk := hWalk') (hCountGood := hCountGood) (ζc := ζc) (hζc0 := hζc0) (hζc1 := hζc1)
    (ρcell := ρcell) (hρgap := hρgap) (hCellGood := hCellGood) (hRcell := hRcell') (hκ2 := hκ2)
    (hεcell := hεcell) (hfinE := hfinE') (hsc := hsc') (Z := Z)
    (hεα := hεα') (hεmass := hεmass') (hb := hb') (hx1 := hx1') (hmomS := hmomS') (hgood := hgood')
    (hN := hN') (hpos := hpos') (hdbl := hdbl')
  intro k hk
  filter_upwards [hone k hk, hBa] with x hx hxB hP
  have hxT : x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (Tn T n k) (Bᶜ.indicator τU) := by
    rw [Tn_of_le hk]; exact (mem_prefix_indicator x).2 ⟨hP, hxB⟩
  have hc := hx hxT
  have hcong := condExp_testInd_congr m a A ε η (isStoppingTime_Tn n hT k) (hT k)
    (Tn_of_le (T := T) (n := n) hk) (Rn_of_le (R := R) (n := n) hk) x
  calc (srwLaw m a)[testInd A ε η (T k) (R k) | (hT k).measurableSpace] x
      = (srwLaw m a)[testInd A ε η (Tn T n k) (Rn R n k) | (isStoppingTime_Tn n hT k).measurableSpace] x :=
        hcong.symm
    _ ≤ 1 - q := hc

theorem shellOneTest_of_direct_ae_rcell_stopFin_rho_gexp (ρmom : ℝ) (_hρmom0 : 0 < ρmom) (_hρmom1 : ρmom < 1) {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    (Kset : Set ℂ) (Rf : ℂ → ℝ) (r s d q0 α C_exit C_good C : ℝ) {N_cov : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C))
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * (shellDbl68 C_good) ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hstopFin : ∀ k ≤ n, ∃ F : Set ℤ, F.Finite ∧ ∀ᵐ x ∂srwLaw m a,
      shellExit ε η Kset r s d Rf k x < ⊤ → x (shellExit ε η Kset r s d Rf k x).toNat ∈ F)
    (hRbd : ∀ k ≤ n, ∃ s' : ℝ, ∀ᵐ x ∂srwLaw m a,
      shellExit ε η Kset r s d Rf k x < ⊤ → Rf (shellCentre ε η Kset r s d k x) ≤ s')
    (hRr : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k x) ∧ Rf (shellCentre ε η Kset r s d k x) ≤ 1)
    (hL68 : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (rmin : ℝ)
    (hRmin : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k x))
    (hVolC : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ENNReal.ofReal ((K.c0 * Rf (shellCentre ε η Kset r s d k x)) ^ K.βm)
          ≤ μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x))))
    (hVolY : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ y ∈ ball (0 : ℂ) (ρmom - Rf (shellCentre ε η Kset r s d k x) / 4),
          ENNReal.ofReal ((Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm)
            ≤ μ (ball y (Rf (shellCentre ε η Kset r s d k x) / 4)))
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (ωg : ℝ)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ ωg ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    (hWalk : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
          ε ^ ωg ≤ Rf (shellCentre ε η Kset r s d k x) / 8 ∧
          Rf (shellCentre ε η Kset r s d k x) / 8 ≤
            infDist (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat)) (sphere 0 ρc))
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    (ρcell : ℝ) (hρgap : ρc < ρcell)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρcell).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hd : 0 < d) (aW : ℝ)
    (hRf : ∀ z ∈ shortEligible ρc d aW, Rf z ≤ d ^ aW)
    (hEl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        shellCentre ε η Kset r s d k x ∈ shortEligible ρc d aW)
    (hcut : d ^ aW < ρcell - ρc)
    (hκ2 : 2 * K.ω < 2 / (2 + γ) ^ 2 - ζc)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hsc : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal)
    (hεα : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ Rf (shellCentre ε η Kset r s d k x) / 100)
    (hεmass : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ε ^ α ≤ (Rf (shellCentre ε η Kset r s d k x) / 4) ^ K.βm)
    (hb : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈
          cellVertices ε η (sphere (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)))
    (hx1 : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ‖vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat)‖
          < ρmom - Rf (shellCentre ε η Kset r s d k x) / 4)
    (hmomS : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρmom → ENNReal.ofReal (ε ^ α) ≤ μ D →
        ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
          exitTimeMoment m (interiorCellVertices ε η D) a N ≤
            ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
              (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k x)) (shellCentre ε η Kset r s d k x))
    (hN : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
          (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        0 < ⨅ w ∈ annulus (shellCentre ε η Kset r s d k x) (Rf (shellCentre ε η Kset r s d k x))
          (2 * Rf (shellCentre ε η Kset r s d k x)), μ (ball w (K.c0 * Rf (shellCentre ε η Kset r s d k x))))
    (hdbl : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal
          ≤ shellDbl68 C_good * (μ (ball (vertexPoint ε η (x (shellExit ε η Kset r s d Rf k x).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k x)))).toReal) :
    ShellOneTestAt m a A η ε Kset τU r s d Rf n (q0 / (1 + Real.log (1 / r)) ^ 2) := by
  have hpair := fun (k : ℕ) (hk : k ≤ n) => BallExitMeasAe68.hmom_pair_stopFin_ae hlf hcons hη hprop hε a
    (T := fun k => shellExit ε η Kset r s d Rf k) (R := fun k w => Rf (shellCentre ε η Kset r s d k w))
    (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) k (hstopFin k hk) (hRbd k hk)
  have hfinD : ∀ (x : ℂ) (ρ : ℝ), (interiorCellVertices ε η (ball x ρ)).Finite := fun x ρ =>
    (TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball).subset fun _ hk => hk.1
  exact hone_exitQ_walk_of_env_direct_ae_rho_gexp (T := fun k => shellExit ε η Kset r s d Rf k)
    (R := fun k w => Rf (shellCentre ε η Kset r s d k w)) K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c rfl
    hC hCw hCg (fun k => isStoppingTime_shellExit ε η Kset r s d Rf k)
    (fun k => measurable_shellRadius_stopped ε η Kset r s d Rf k) (fun k hk => (hpair k hk).1) (fun k hk => (hpair k hk).2)
    hRr hL68 rmin hRmin hVolC hVolY ζc hζc0 hζc1 ωg hGreen hWalk hCountGood ρcell hρgap hCellGood (Lemma68RcellDischarge.hRcell_of_eligible hd hRf hEl hcut) hκ2 hεcell
    (fun k _ => Filter.Eventually.of_forall fun x _ =>
      MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons (hfinD _ _) _)
    hsc hεα hεmass hb hx1 hmomS hgood hN hpos hdbl

end Lemma68LeafAe
end MatedCRT

#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_of_env_repaired_rho_gexp
#print axioms MatedCRT.Lemma68CellR.hone_exitQ_walk_of_env_cellR_rho_gexp
#print axioms MatedCRT.Lemma68LeafAe.hone_exitQ_walk_of_env_direct_ae_rho_gexp
#print axioms MatedCRT.Lemma68LeafAe.shellOneTest_of_direct_ae_rcell_stopFin_rho_gexp
