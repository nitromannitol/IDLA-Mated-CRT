import MatedCRT.FirstPass.S6r.Window
import MatedCRT.FirstPass.S6j.StateLocal

/-!
# S4: the local A-budget from the radius-`r` sparsity, and the per-state bound in the short window (fp-S6r)

Written argument: `notes/fp-gaps/CHATGPT-idla-6-8-redesign.md` §6 `S4_localABudget` (lines 246-302).

Let `x = η(b)` and `R = R_z(d)` with `R` in the short window of `r` (`Window.lean`). Since `c₀R < r`, the ball
`B_{c₀R}(x)` lies in `B_r(x)`, so the Lemma 6.8 sparsity hypothesis at the centre `x` and radius `r` bounds the local
count directly (S4.1), with no covering: `s₁ r^{2β} ≤ s₁ R^β ≤ (c₀R)^β/4` by `r² ≤ R` (S4.2) and `44 s₁ ≤ c₀^β`
(S0). The volume lower bound `(c₀R)^β ≤ μ(B_{c₀R}(x))` (Lemma 2.7) closes (S4.4).

`perState_local_bound_window` is `perState_local_bound` (S6j/StateLocal.lean) for `R` in the window: `r² ≤ R`, `R ≤ 1`
and `c₀R < r` are DERIVED from the window, and the local count is `localCount_of_ball`. The old theorem
`perState_local_bound` is kept (it uses the covering count `hA_local_of_sparse` and needs `r² ≤ R` as an input).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

/-- The ball inclusion `V^ε(D) ⊆ V^ε(D')` for `D ⊆ D'` (the vertex set is `{k | cell_k ∩ D ≠ ∅}`). -/
lemma cellVertices_mono_win {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun k hk => (show (cell ε η k ∩ D).Nonempty from hk).mono (Set.inter_subset_inter_right _ h)

/-- **S4: the local A-count from the radius-`r` sparsity.** For `c₀R < r`, `r² ≤ R`, `44 s₁ ≤ c₀^β`, the sparsity
`|A ∩ V^ε(B_r(z))| < s₁ r^{2β}/ε` at every centre `z`, and `(c₀R)^β ≤ μ(B_{c₀R}(x))`, the count of `A`-vertices in
`V^ε(B_{c₀R}(x))` is at most `μ(B_{c₀R}(x))/(4ε)` (the `hloc` of `perState_local_bound_of_count`). -/
theorem localCount_of_ball {μ : Measure ℂ} {ε : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {x : ℂ}
    {R r s1 β c0 : ℝ}
    (hε : 0 < ε) (hs0 : 0 ≤ s1) (hβ0 : 0 ≤ β) (hr : 0 < r) (hR : 0 < R) (hc0 : 0 < c0)
    (hcR : c0 * R ≤ r) (hr2 : r ^ 2 ≤ R) (hs1 : 44 * s1 ≤ c0 ^ β)
    (hfin : ∀ z : ℂ, (cellVertices ε η (ball z r)).Finite)
    (hglob : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hvol : (c0 * R) ^ β ≤ (μ (ball x (c0 * R))).toReal) :
    ((A ∩ cellVertices ε η (ball x (c0 * R))).ncard : ℝ) ≤ (μ (ball x (c0 * R))).toReal / (4 * ε) := by
  have hsub : cellVertices ε η (ball x (c0 * R)) ⊆ cellVertices ε η (ball x r) :=
    cellVertices_mono_win (Metric.ball_subset_ball hcR)
  have hfinA : (A ∩ cellVertices ε η (ball x r)).Finite := (hfin x).subset inter_subset_right
  have hncard : (A ∩ cellVertices ε η (ball x (c0 * R))).ncard
      ≤ (A ∩ cellVertices ε η (ball x r)).ncard :=
    Set.ncard_le_ncard (inter_subset_inter_right _ hsub) hfinA
  have hcast : ((A ∩ cellVertices ε η (ball x (c0 * R))).ncard : ℝ)
      ≤ ((A ∩ cellVertices ε η (ball x r)).ncard : ℝ) := by
    exact_mod_cast hncard
  have hlt : ((A ∩ cellVertices ε η (ball x r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε := hglob x
  -- S4.2: `r^{2β} ≤ R^β` from `r² ≤ R`
  have hpow : r ^ (2 * β) ≤ R ^ β := by
    have e : r ^ (2 * β) = (r ^ 2) ^ β := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
      congr 1
    rw [e]
    exact Real.rpow_le_rpow (by positivity) hr2 hβ0
  -- S4.4: `s₁ r^{2β} ≤ (c₀R)^β/4` from `44 s₁ ≤ c₀^β`
  have hRβ : 0 ≤ R ^ β := by positivity
  have hmain : s1 * r ^ (2 * β) ≤ (c0 * R) ^ β / 4 := by
    rw [Real.mul_rpow hc0.le hR.le]
    have h1 : s1 * r ^ (2 * β) ≤ s1 * R ^ β := mul_le_mul_of_nonneg_left hpow hs0
    have h44 : 44 * s1 * R ^ β ≤ c0 ^ β * R ^ β := mul_le_mul_of_nonneg_right hs1 hRβ
    have h2 : 0 ≤ c0 ^ β * R ^ β := by positivity
    linarith
  have hdiv : s1 * r ^ (2 * β) / ε ≤ (c0 * R) ^ β / (4 * ε) := by
    calc s1 * r ^ (2 * β) / ε ≤ ((c0 * R) ^ β / 4) / ε :=
          div_le_div_of_nonneg_right hmain hε.le
      _ = (c0 * R) ^ β / (4 * ε) := by rw [div_div]
  have hvol' : (c0 * R) ^ β / (4 * ε) ≤ (μ (ball x (c0 * R))).toReal / (4 * ε) :=
    div_le_div_of_nonneg_right hvol (by positivity)
  linarith [hcast, hlt, hdiv, hvol']

/-- **Per-state local test bound in the short window** (`perState_local_bound` for `R` in the window of `r`). The
hypotheses `r² ≤ R` (S3.1), `R ≤ 1` and `c₀R < r` (S3.2–S3.3, from the cutoff `2c₀r^ζ < 1`) are derived from
`R ∈ [d(r), d(r)^a]`; the local count is `localCount_of_ball` (S4) from the radius-`r` sparsity `hsp`. Conclusion as in
`perState_local_bound`: `P(stay in A until exit | v) ≤ 1 - q₀/(1 + log(1/R))²`, `q₀ = 1/(288 C_d² K²)`. -/
theorem perState_local_bound_window {μ : Measure ℂ} [SFinite μ] [IsFiniteMeasureOnCompacts μ] {η : ℝ → ℂ}
    {γ ρ : ℝ} (K : Constants68 γ ρ)
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {ε δ r R : ℝ} {z : ℂ} {v : ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hr : 0 < r) (hr1 : r ≤ 1) (hcut : 2 * K.c0 * r ^ K.ζ < 1)
    (hRw : InWindow r K.ζ R)
    (hεc : ε ≤ 16 * K.c0) (hδ : δ ≤ R / 100)
    (hmeet : (cell ε η v ∩ sphere z (4 * R / 3)).Nonempty)
    (hsp : ∀ w : ℂ, ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (hvol : (K.c0 * R) ^ K.βm ≤ (μ (ball (vertexPoint ε η v) (K.c0 * R))).toReal)
    (hdy : diam (cell ε η v) ≤ R / 100)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η v) (R / 4)).Nonempty →
      diam (cell ε η k) ≤ K.c0 * R)
    (hGreenLow : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η v) (K.c0 * R)),
      K.C⁻¹ * Real.log (if vertexPoint ε η v = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η v - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 8))) v b)
    (hexit : exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η v) (R / 4))) v 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * K.Cd ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ w ∈ ball (vertexPoint ε η v) (R / 4),
          ∫⁻ u in thickening δ (ball (vertexPoint ε η v) (R / 4)),
            ENNReal.ofReal (Real.log (1 / ‖w - u‖) + 1) ∂μ) ^ (2 : ℕ))
    (hann : IsGoodAnnulusEvent μ K.c0 K.Cg R z) :
    srwLaw m v (TestBound68.stayIn
      (fun u => interiorCellVertices ε η (ball (vertexPoint ε η u) (R / 4))) A v) ≤
      ENNReal.ofReal (1 - (1 / (288 * K.Cd ^ 2 * (K.Cg * (1 + (Real.log 4 - 1)) / (1 - Real.log 2)) ^ 2)) /
        (1 + Real.log (1 / R)) ^ 2) := by
  have hr2 : r ^ 2 ≤ R := hRw.sq_le hr hr1
  have hR0 : 0 < R := hRw.pos
  have hR1 : R ≤ 1 := hRw.le_one K.hζ0.le
  have hζ1 : K.ζ ≤ 1 := by linarith [K.hζ1]
  have hcR : K.c0 * R < r :=
    c0_mul_lt_of_le_two_mul_rpow K.hc0 hr hcut (hRw.le_two_mul_rpow hr hr1 K.hζ0.le hζ1)
  have hloc := localCount_of_ball (μ := μ) (x := vertexPoint ε η v) hε K.hs1.le
    (by linarith [K.one_le_βm]) hr hR0 K.hc0 hcR.le hr2 K.hs1small
    (fun w => S6j.perState_cellVertices_ball_finite hη hprop hε w r) hsp hvol
  exact S6j.perState_local_bound_of_count hap hη hprop hε hR0 hR1 K.hC K.hCd K.hCg K.hc0 K.c0_lt_eighth K.hc0C
    hεc hδ hmeet hloc hvol hdy hdiam hGreenLow hexit hann

end Lemma68Window
end MatedCRT
