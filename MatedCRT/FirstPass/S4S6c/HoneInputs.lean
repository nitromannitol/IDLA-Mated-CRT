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
* `hvol`, `hvol2` (volume lower bound `μ(B_δ(z)) ≥ δ^{β⁻}` for `z ∈ B_{1-δ}`): the lower half of `VolumeGrowthStmt`
  (Draft/Section2.lean:121; paper Lemma 2.7 = `lemma:volume-growth`), taken on the good event `hVol` at the scales
  `δ ∈ [rmin, 1/4]`. The all-scales form is not written in the paper (per-scale PolyHighProb only); see the report.
* `hGrLow` (lower Green bound): the second conjunct of `GreenKernelLowerBoundStmt` (Draft/Section2.lean:212; paper
  Lemma 2.16 = `lemma:greens-kernel-lower-bound`) on the good event `hGreen`. Its domain `b ∈ B(v, r/3)` with `r = R/8`
  contains `B(v, c₀R)` because `c₀ ≤ 1/24` (Constants68.hc0').

Terminology: LQG measure `μ` (Duplantier-Sheffield), Green function and kernel (Armitage-Gardiner), Armitage-Gardiner annulus.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open HarmonicBalls (annulus)

namespace MatedCRT
open Lemma68WalkBridge (coordFiltration)

namespace Lemma68Window

/-- **The hone of `exitQ_le_pow` at the walk-centred test end, with the discharged environment inputs removed.**
Same conclusion as `hone_exitQ_walk`. The finiteness, null-singleton, `ρS`, `hvol`, `hvol2` and `hGrLow` inputs are derived
from the good-event hypotheses `hVol` (volume lower bound at all scales in `[rmin, 1/4]`), `hGreen` (lower Green bound)
and `hWalk` (walk state in its domain). The moment, parameter, sparsity and configuration inputs stay named. -/
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
    -- scale range of the good event: every walk test radius satisfies `rmin ≤ c₀ R` (configuration input, q2)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    -- good event of the volume lower bound (lower half of `VolumeGrowthStmt`, all scales in `[rmin, 1/4]`)
    (hVol : ∀ δ : ℝ, rmin ≤ δ → δ ≤ 1 / 4 → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ K.βm) ≤ μ (ball z δ))
    -- good event of the lower Green bound (second conjunct of `GreenKernelLowerBoundStmt`, exponent `K.ω`,
    -- constant `K.C`, radius `ρc`)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    -- the walk state lies in the domain of the good Green bound, with margin `R/8` to `∂B_ρ` (configuration input, q2)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k ω / 8 ∧
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
  -- scale bookkeeping: `c₀ ≤ 1/24` gives `c₀R ≤ R/24 ≤ R/4` and `c₀R ≤ R/24`, and `R > 0` from `r² ≤ R`
  have hRpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, 0 < R k ω :=
    fun k ω hω => lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
  have hcR : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      K.c0 * R k ω ≤ R k ω / 24 := fun k ω hω => by
    have h := mul_le_mul_of_nonneg_right K.hc0' (hRpos k ω hω).le
    linarith
  -- `hvol`: the good volume bound at `δ = c₀R`, centre `v` with `‖v‖ < 1 - R/4 ≤ 1 - c₀R`
  have hvol : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (K.c0 * R k ω) ^ K.βm ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
    intro k ω hω
    have hR1 := (hRr k ω hω).2
    have hc := hcR k ω hω
    have hR0 := hRpos k ω hω
    have hz : vertexPoint ε η (ω (T k ω).toNat) ∈ ball (0 : ℂ) (1 - K.c0 * R k ω) := by
      rw [mem_ball_zero_iff]
      linarith [hx1 k ω hω]
    have hlow := hVol (K.c0 * R k ω) (hRmin k ω hω) (by linarith) _ hz
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top (μ := μ)).ne).mp hlow
  -- `hvol2`: the good volume bound at `δ = R/4`, centres `y ∈ B_{1-R/4}`
  have hvol2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4)) := by
    intro k ω hω y hy
    exact hVol (R k ω / 4) (by linarith [hRmin k ω hω, hcR k ω hω, hRpos k ω hω])
      (by linarith [(hRr k ω hω).2]) y hy
  -- `hGrLow`: the good Green bound at the walk state with `r = R/8`; `B(v, c₀R) ⊆ B(v, R/8/3)` since `c₀ ≤ 1/24`
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
  exact hone_exitQ_walk K ε η hη hprop hε hεc m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2 hRr hdiam hsp
    hvol (fun k ω hω b hb => ⟨HcGreen68.greenKernel_le_greenFn m _ _ b, hGrLow k ω hω b hb⟩)
    hfinE hL29 hsc (Z := Z) (H := H) (Rb := fun _ _ => 1) hεα hεmass hb hcell hh hx1 hvol2 hρS hmomS hgood hN hpos
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) (fun k ω _ v _ => hμNull v)
    (fun k ω _ => (measure_ball_lt_top (μ := μ)).ne) hdbl

#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_of_env

end Lemma68Window

end MatedCRT
