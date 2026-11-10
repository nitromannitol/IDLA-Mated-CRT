import MatedCRT.FirstPass.S6r.OneTest.Concrete
import MatedCRT.FirstPass.S6r.OneTest.WalkStateFirst
import MatedCRT.FirstPass.S6r.OneTest.WalkStateSecond
import MatedCRT.FirstPass.S6r.Shells.ChoiceStopped
import MatedCRT.FirstPass.S4S6c.WalkBridge68

/-!
# The walk-centred hone of `exitQ_le_pow` (q2, fp-S4S6c-rename-hone; z8 draft notes/z8-hone-walk-draft.lean)

Landed from z8's draft unchanged in its statement and proof. It instantiates `hone_exitQ_concrete`
(S6r/OneTest/Concrete.lean:408) at the walk-centred parameter `walkParam ε η (R k) (T k)`, with `hstep1`, `hstep2`
from `firstMoment_walkState` and `secondMoment_walkState`. The named inputs are the finite exit-time moments, the
parameter range, the first- and second-moment side conditions over the prefix set, and the mass comparison `hdbl`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
open Lemma68WalkBridge (coordFiltration)
open Lemma68ShellParam (measurable_coord_toNat_stop)

namespace Lemma68Window

/-- The walk-centred parameter is `𝓕_T`-measurable when its radius is (the walk state `X_T` is `𝓕_T`-measurable). -/
theorem measurable_walkParam {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T) {R : (ℕ → ℤ) → ℝ}
    (hR : Measurable[hT.measurableSpace] R) (ε : ℝ) (η : ℝ → ℂ) :
    Measurable[hT.measurableSpace] (walkParam ε η R T) :=
  hR.prodMk (measurable_coord_toNat_stop hT (vertexPoint ε η))

/-- **The hone of `exitQ_le_pow` at the walk-centred test end** (family over `k ≤ n`). The parameter is
`ρ_k = walkParam (R k) (T k)`, the test end is `L_k = testEndExit ε η ρ_k (T k)`, the count is `σ_D` for
`D = B_{R_k/4}(η(ε X_{T_k}))`. `hstep1` and `hstep2` are derived (`firstMoment_walkState`,
`secondMoment_walkState`); their omega-wise side conditions are named over the prefix set. `hmom1`, `hmom2`
(finite exit-time moments), `hRr` (parameter range), and the mass comparison `hdbl` stay named. -/
theorem hone_exitQ_walk {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
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
    -- first-moment side conditions at the walk state `y = ω (T k ω).toNat`
    (hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ w : ℂ,
      ((A ∩ cellVertices ε η (ball w (K.c0 * R k ω))).ncard : ℝ)
        < K.s1 * (K.c0 * R k ω) ^ (2 * K.βm) / ε)
    (hvol : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (K.c0 * R k ω) ^ K.βm ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    (hGr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
          (ω (T k ω).toNat) b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 8)))
            (ω (T k ω).toNat) b ∧
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
    -- second-moment side conditions at the walk state `b = ω (T k ω).toNat`, centre `vertexPoint ε η b`,
    -- shell centre `Z k ω`, mesh `H k ω`, outer radius `Rb k ω`
    {Z : ℕ → (ℕ → ℤ) → ℂ} {H Rb : ℕ → (ℕ → ℤ) → ℝ}
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
    (hρS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4) ⊆ ball 0 (Rb k ω))
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 (Rb k ω) → ENNReal.ofReal (ε ^ α) ≤ μ D →
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
    (hfin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      μ (ball (Z k ω) (3 * R k ω)) ≠ ⊤)
    (hatom : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ v ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ {v} = 0)
    (hfinD : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω)) ≠ ⊤)
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  have hc : (0 : ℝ) < 1 / 4 := by norm_num
  have hc0' : K.c0 < 1 / 5 := by linarith [K.hc0']
  have hstep1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (1 / 4 : ℝ) * ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal
        ≤ ∫ w, occCount A (ballExitSigma ε η (walkParam ε η (R k) (T k) ω)) w
            ∂(srwLaw m (ω (T k ω).toNat)) := by
    intro k ω hω
    have hR0 : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    exact firstMoment_walkState K hη hprop hε hεc hR0 (hRr k ω hω).2 (hdiam k ω hω) (hsp k ω hω)
      (hvol k ω hω) (hGr k ω hω) (hfinE k ω hω) (hL29 k ω hω) (hsc k ω hω)
  have hstep2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∫ w, occCount A (ballExitSigma ε η (walkParam ε η (R k) (T k) ω)) w ^ 2
          ∂(srwLaw m (ω (T k ω).toNat))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2
          * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal ^ 2 := by
    intro k ω hω
    have hR0 : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hS := secondMoment_walkState (μ := μ) (η := η) (m := m) (A := A) (ε := ε) (R := R k ω)
      (α := α) (ρ := Rb k ω) (C_exit := C_exit) (c₀ := K.c0) (C_good := C_good) (βm := K.βm)
      (h := H k ω) (N_cov := N_cov) (z := Z k ω) (b := ω (T k ω).toNat) (Dbl := Dbl)
      hε hR0 (hRr k ω hω).2 K.hc0 hc0' hCg (hεα k ω hω) (hεmass k ω hω) (hb k ω hω) (hcell k ω hω)
      (hh k ω hω) (hx1 k ω hω) (hvol2 k ω hω) (hρS k ω hω) (hmomS k ω hω) (hgood k ω hω) (hN k ω hω)
      (hpos k ω hω) (hfin k ω hω) (hatom k ω hω) (hfinD k ω hω) (hdbl k ω hω)
    have hX : 0 ≤ ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2
        * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCw hX
    exact hS.trans (le_trans (le_of_eq (by ring)) (h3.trans (le_of_eq (by ring))))
  have hm : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := fun k ω hω =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (mul_pos K.hc0 (lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1)) _)
      (hvol k ω hω)
  exact hone_exitQ_concrete ε η hη hε m a A hA n hc hC hr hr1 hq0c hq hT
    (ρ := fun k => walkParam ε η (R k) (T k)) (fun k => measurable_walkParam (hT k) (hR k) ε η)
    hmom1 hmom2 (mm := fun k ω => (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    (R := R) hm hRr hstep1 hstep2


end Lemma68Window

end MatedCRT
