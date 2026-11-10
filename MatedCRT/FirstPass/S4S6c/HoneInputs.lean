import MatedCRT.FirstPass.S4S6c.HoneWalk
import MatedCRT.FirstPass.S4S6c.HcGreen68

/-!
# Inputs of the walk hone `hone_exitQ_walk`, discharged where the repository gives them (q4, task fp-S4S6c-hone-inputs)

`hone_exitQ_walk` (`FirstPass/S4S6c/HoneWalk.lean:37`) takes 26 named side conditions. `hone_exitQ_walk_of_env` below
removes those with a deterministic source for the configuration of q2 (shell exit `T k = shellExit k`, test radius
`R k` at the walk state). The removed inputs and their sources:

* `hfin`, `hfinD` (`μ (ball _ _) ≠ ⊤`): `measure_ball_lt_top` from the local finiteness `[IsFiniteMeasureOnCompacts μ]`,
  the environment clause `IsLocallyFiniteMeasure` of `LQGMeasurePropertiesStmt` (Draft/Section2.lean:~39, item 1).
* `hatom` (`μ {v} = 0`): the null-singleton clause `hμNull : ∀ v, μ {v} = 0` of the same statement (`NullSingletonClass`).
* `hρS` (`ball (vertex) (R/4) ⊆ ball 0 (Rb)`): with `Rb := 1`, from `hx1` (`‖vertex‖ < 1 - R/4`) and `hRr` (`R ≥ r²`).
* `hGr` (first conjunct `greenKernel ≤ greenFn`): deterministic `HcGreen68.greenKernel_le_greenFn` (HcGreen68.lean:23).
  Only the lower Green bound `hGrLow` stays named.

Terminology: LQG measure `μ` (Duplantier-Sheffield), Green function and kernel (Armitage-Gardiner), Armitage-Gardiner annulus.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
open Lemma68WalkBridge (coordFiltration)

namespace Lemma68Window

/-- **The hone of `exitQ_le_pow` at the walk-centred test end, with the discharged environment inputs removed.**
Same conclusion as `hone_exitQ_walk`. The finiteness, null-singleton and `ρS` inputs are derived; the Green lower bound
`hGrLow`, the moment and parameter inputs, and the side conditions of the walk state stay named. -/
theorem hone_exitQ_walk_of_env {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
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
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ w : ℂ,
      ((A ∩ cellVertices ε η (ball w (K.c0 * R k ω))).ncard : ℝ)
        < K.s1 * (K.c0 * R k ω) ^ (2 * K.βm) / ε)
    (hvol : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (K.c0 * R k ω) ^ K.βm ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    (hGrLow : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)),
      K.C⁻¹ * Real.log (if vertexPoint ε η (ω (T k ω).toNat) = vertexPoint ε η b then ε⁻¹
            else min ((R k ω / 8) / ‖vertexPoint ε η (ω (T k ω).toNat) - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
            (ω (T k ω).toNat) b)
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
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hvol2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)))
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
        ≤ 1 - q := by
  -- `ρS` with `Rb := 1`: a ball of radius `R/4` about a point of norm `< 1 - R/4` lies in the unit ball.
  have hρS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4) ⊆ ball 0 1 := by
    intro k ω hω u hu
    have hx := hx1 k ω hω
    have hd : ‖u - vertexPoint ε η (ω (T k ω).toNat)‖ < R k ω / 4 := by
      simpa [dist_eq_norm] using hu
    have htri := norm_add_le (vertexPoint ε η (ω (T k ω).toNat)) (u - vertexPoint ε η (ω (T k ω).toNat))
    have hsum : vertexPoint ε η (ω (T k ω).toNat) + (u - vertexPoint ε η (ω (T k ω).toNat)) = u := by ring
    rw [hsum] at htri
    rw [mem_ball_zero_iff]
    linarith
  exact hone_exitQ_walk K ε η hη hprop hε hεc m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2 hRr hdiam hsp
    hvol (fun k ω hω b hb => ⟨HcGreen68.greenKernel_le_greenFn m _ _ b, hGrLow k ω hω b hb⟩)
    hfinE hL29 hsc (Z := Z) (H := H) (Rb := fun _ _ => 1) hεα hεmass hb hcell hh hx1 hvol2 hρS hmomS hgood hN hpos
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) (fun k ω _ v _ => hμNull v)
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) hdbl

#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_of_env

end Lemma68Window

end MatedCRT
