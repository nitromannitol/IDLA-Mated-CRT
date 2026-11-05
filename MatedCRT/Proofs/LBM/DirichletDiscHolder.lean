import MatedCRT.Proofs.LBM.DirichletDiscBarrier
import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder continuity of the Poisson extension up to the boundary of a disc

For `α`-Hölder boundary data `φ` on `∂B_r(z)` (`0 < α < 1`), the Poisson extension `u` (Poisson integral in
`B_r(z)`, `φ` outside) is `α`-Hölder on `cl B_r(z)` (Gilbarg-Trudinger, Lemma 4.2 for the disc).

The proof avoids derivative estimates near the boundary:
1. the barrier of `DirichletDiscBarrier.lean` gives `|u(x) - φ(ζ₀)| ≤ K |x - ζ₀|^α` for `x ∈ cl B_r(z)`,
   `ζ₀ ∈ ∂B_r(z)`;
2. for `|c| ≤ 1`, `w ↦ u(z + c(w - z)) - u(w)` is harmonic in `B_r(z)` (a complex-affine change of variables
   preserves harmonicity), continuous on `cl B_r(z)`, and bounded on `∂B_r(z)` by `K (|c - 1| r)^α` by step 1;
   the maximum principle propagates the bound inside;
3. for `|x - z| ≤ |y - z|` with `|y - z| ≥ r/2`, `x = z + c(y - z)` with `c = (x - z)/(y - z)` and
   `|c - 1| r ≤ 2|x - y|`; if both points lie in `cl B_{r/2}(z)`, `u` is smooth there, hence Lipschitz.
-/

namespace MatedCRT

open Metric Filter Topology Set MeasureTheory InnerProductSpace HarmonicBalls
open scoped NNReal ENNReal

/-- A complex-affine contraction `w ↦ z + c (w - z)`, `|c| ≤ 1`, maps `B_r(z)` into itself. -/
theorem homothety_mem_ball {z c w : ℂ} {r : ℝ} (hc : ‖c‖ ≤ 1) (hw : w ∈ ball z r) :
    z + c * (w - z) ∈ ball z r := by
  rw [mem_ball, dist_eq_norm] at hw ⊢
  rw [add_sub_cancel_left, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hw

theorem homothety_mem_closedBall {z c w : ℂ} {r : ℝ} (hc : ‖c‖ ≤ 1) (hw : w ∈ closedBall z r) :
    z + c * (w - z) ∈ closedBall z r := by
  rw [mem_closedBall, dist_eq_norm] at hw ⊢
  rw [add_sub_cancel_left, norm_mul]
  exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hc) hw

theorem continuous_homothety (z c : ℂ) : Continuous fun w : ℂ => z + c * (w - z) :=
  continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))

/-- Harmonicity in a disc is preserved by a complex-affine contraction about its centre. -/
theorem harmonicOnNhd_comp_homothety {f : ℂ → ℝ} {z c : ℂ} {r : ℝ}
    (hf : HarmonicOnNhd f (ball z r)) (hc : ‖c‖ ≤ 1) :
    HarmonicOnNhd (fun w => f (z + c * (w - z))) (ball z r) := by
  obtain ⟨F, hF, hFeq⟩ := hf.exists_analyticOnNhd_ball_re_eq
  intro w hw
  have hAan : AnalyticAt ℂ (fun y : ℂ => z + c * (y - z)) w :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
  have hcomp : AnalyticAt ℂ (F ∘ fun y : ℂ => z + c * (y - z)) w :=
    AnalyticAt.comp (f := fun y : ℂ => z + c * (y - z)) (hF _ (homothety_mem_ball hc hw)) hAan
  have hev : (fun y => ((F ∘ fun y : ℂ => z + c * (y - z)) y).re) =ᶠ[𝓝 w]
      fun y => f (z + c * (y - z)) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with y hy
    exact hFeq (homothety_mem_ball hc hy)
  exact (harmonicAt_congr_nhds hev).1 hcomp.harmonicAt_re

/-- Hölder continuity from a `dist` bound. -/
theorem holderOnWith_of_dist_le {f : ℂ → ℝ} {s : Set ℂ} {C β : ℝ≥0}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (β : ℝ)) : HolderOnWith C β f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg β),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

theorem discPoissonIntegral_neg (φ : ℂ → ℝ) (z : ℂ) (r : ℝ) (x : ℂ) :
    discPoissonIntegral (fun y => -φ y) z r x = -discPoissonIntegral φ z r x := by
  have h : (poissonKernel z x • fun y => -φ y) = (-1 : ℝ) • (poissonKernel z x • φ) := by
    ext y
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  rw [discPoissonIntegral, h, Real.circleAverage_smul, smul_eq_mul, neg_one_mul, discPoissonIntegral]

section Holder

variable {φ : ℂ → ℝ} {z : ℂ} {r α C : ℝ}

/-- **Boundary Hölder estimate** for the Poisson extension. -/
theorem abs_discPoissonExtension_sub_le (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (hφc : ContinuousOn φ (sphere z r))
    (hφ : ∀ ζ ∈ sphere z r, ∀ ζ' ∈ sphere z r, |φ ζ - φ ζ'| ≤ C * ‖ζ - ζ'‖ ^ α)
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere z r) {x : ℂ} (hx : x ∈ closedBall z r) :
    |discPoissonExtension φ z r x - φ ζ₀| ≤
      C / Real.cos (α * (Real.pi / 2)) * ‖x - ζ₀‖ ^ α := by
  have hκ0 := cos_half_pi_mul_pos hα0.le hα1
  by_cases hxb : x ∈ ball z r
  · rw [discPoissonExtension_of_mem hxb, abs_le]
    have hφi : CircleIntegrable φ z r := hφc.circleIntegrable hr.le
    constructor
    · have hneg : CircleIntegrable (fun y => -φ y) z r := (hφc.neg).circleIntegrable hr.le
      have h := discPoissonIntegral_le_add_rpow (φ := fun y => -φ y) (a := -φ ζ₀) hr hζ₀ hα0 hα1 hC
        hneg (fun ζ hζ => by
          have := (abs_le.1 (hφ ζ hζ ζ₀ hζ₀)).1
          linarith) hxb
      rw [discPoissonIntegral_neg] at h
      linarith
    · have h := discPoissonIntegral_le_add_rpow (a := φ ζ₀) hr hζ₀ hα0 hα1 hC hφi
        (fun ζ hζ => by
          have := (abs_le.1 (hφ ζ hζ ζ₀ hζ₀)).1
          have := (abs_le.1 (hφ ζ hζ ζ₀ hζ₀)).2
          linarith) hxb
      linarith
  · have hxs := mem_sphere_of_mem_closedBall_of_notMem_ball hx hxb
    rw [discPoissonExtension_of_notMem hxb]
    refine (hφ x hxs ζ₀ hζ₀).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [le_div_iff₀ hκ0]
    exact mul_le_of_le_one_right hC (Real.cos_le_one _)

/-- The Poisson extension moves by at most `K (|c - 1| r)^α` under `w ↦ z + c(w - z)`, `|c| ≤ 1`. -/
theorem abs_discPoissonExtension_homothety_sub_le (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1)
    (hC : 0 ≤ C) (hφc : ContinuousOn φ (sphere z r))
    (hφ : ∀ ζ ∈ sphere z r, ∀ ζ' ∈ sphere z r, |φ ζ - φ ζ'| ≤ C * ‖ζ - ζ'‖ ^ α)
    {c : ℂ} (hc : ‖c‖ ≤ 1) {w : ℂ} (hw : w ∈ closedBall z r) :
    |discPoissonExtension φ z r (z + c * (w - z)) - discPoissonExtension φ z r w| ≤
      C / Real.cos (α * (Real.pi / 2)) * (‖c - 1‖ * r) ^ α := by
  set u := discPoissonExtension φ z r with hu
  have huh : HarmonicOnNhd u (ball z r) :=
    harmonicOnNhd_discPoissonExtension (hφc.circleIntegrable hr.le)
  have huc : ContinuousOn u (closedBall z r) := continuousOn_discPoissonExtension hr hφc
  have hgh : HarmonicOnNhd (fun w => u (z + c * (w - z)) - u w) (ball z r) :=
    (harmonicOnNhd_comp_homothety huh hc).sub huh
  have hgc : ContinuousOn (fun w => u (z + c * (w - z)) - u w) (closedBall z r) :=
    (huc.comp (continuous_homothety z c).continuousOn
      fun w hw => homothety_mem_closedBall hc hw).sub huc
  refine abs_le_of_harmonicOnNhd hgh hgc (fun ζ hζ => ?_) hw
  have hζr : ‖ζ - z‖ = r := by simpa [dist_eq_norm] using hζ
  show |u (z + c * (ζ - z)) - u ζ| ≤ _
  rw [hu, discPoissonExtension_of_notMem (notMem_ball_of_mem_sphere hζ)]
  have h := abs_discPoissonExtension_sub_le hr hα0 hα1 hC hφc hφ hζ
    (homothety_mem_closedBall hc (sphere_subset_closedBall hζ))
  have hd : ‖z + c * (ζ - z) - ζ‖ = ‖c - 1‖ * r := by
    rw [show z + c * (ζ - z) - ζ = (c - 1) * (ζ - z) by ring, norm_mul, hζr]
  rwa [hd] at h

/-- **Hölder continuity of the Poisson extension** on the closed disc. -/
theorem exists_holderOnWith_discPoissonExtension (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1)
    (hC : 0 ≤ C) (hφc : ContinuousOn φ (sphere z r))
    (hφ : ∀ ζ ∈ sphere z r, ∀ ζ' ∈ sphere z r, |φ ζ - φ ζ'| ≤ C * ‖ζ - ζ'‖ ^ α) :
    ∃ M : ℝ≥0, HolderOnWith M (Real.toNNReal α) (discPoissonExtension φ z r) (closedBall z r) := by
  set u := discPoissonExtension φ z r with hu
  have huh : HarmonicOnNhd u (ball z r) :=
    harmonicOnNhd_discPoissonExtension (hφc.circleIntegrable hr.le)
  have hκ0 := cos_half_pi_mul_pos hα0.le hα1
  set K := C / Real.cos (α * (Real.pi / 2)) with hK
  have hK0 : 0 ≤ K := div_nonneg hC hκ0.le
  have hsub : closedBall z (r / 2) ⊆ ball z r := closedBall_subset_ball (by linarith)
  have hcd : ContDiffOn ℝ 2 u (closedBall z (r / 2)) := fun y hy =>
    (huh y (hsub hy)).1.contDiffWithinAt
  obtain ⟨L, hL⟩ := hcd.exists_lipschitzOnWith (by norm_num) (convex_closedBall z (r / 2))
    (isCompact_closedBall z (r / 2))
  set M : ℝ := max (K * 2 ^ α) (L * r ^ (1 - α)) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (mul_nonneg hK0 (by positivity))
  have key : ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r, ‖x - z‖ ≤ ‖y - z‖ →
      dist (u x) (u y) ≤ M * dist x y ^ α := by
    intro x hx y hy hxy
    rw [Real.dist_eq, dist_eq_norm]
    by_cases hyr : r / 2 ≤ ‖y - z‖
    · have hyz : y - z ≠ 0 := fun h => by
        rw [h, norm_zero] at hyr
        linarith
      have hyzn : 0 < ‖y - z‖ := norm_pos_iff.2 hyz
      set c : ℂ := (x - z) / (y - z) with hcdef
      have hc : ‖c‖ ≤ 1 := by
        rw [hcdef, norm_div, div_le_one hyzn]
        exact hxy
      have hcx : z + c * (y - z) = x := by
        rw [hcdef]
        field_simp
        ring
      have h := abs_discPoissonExtension_homothety_sub_le hr hα0 hα1 hC hφc hφ hc hy
      rw [hcx] at h
      have hc1 : ‖c - 1‖ * r ≤ 2 * ‖x - y‖ := by
        have : c - 1 = (x - y) / (y - z) := by
          rw [hcdef]
          field_simp
          ring
        rw [this, norm_div, div_mul_eq_mul_div, div_le_iff₀ hyzn]
        nlinarith [norm_nonneg (x - y)]
      calc |u x - u y| ≤ K * (‖c - 1‖ * r) ^ α := h
        _ ≤ K * (2 * ‖x - y‖) ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hc1 hα0.le) hK0
        _ = K * 2 ^ α * ‖x - y‖ ^ α := by
          rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]; ring
        _ ≤ M * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · replace hyr : ‖y - z‖ < r / 2 := not_le.1 hyr
      have hy2 : y ∈ closedBall z (r / 2) := by
        rw [mem_closedBall, dist_eq_norm]; exact hyr.le
      have hx2 : x ∈ closedBall z (r / 2) := by
        rw [mem_closedBall, dist_eq_norm]; exact hxy.trans hyr.le
      have hlip := hL.dist_le_mul x hx2 y hy2
      rw [Real.dist_eq, dist_eq_norm] at hlip
      have hdr : ‖x - y‖ ≤ r := by
        calc ‖x - y‖ = ‖(x - z) - (y - z)‖ := by ring_nf
          _ ≤ ‖x - z‖ + ‖y - z‖ := norm_sub_le _ _
          _ ≤ r := by linarith
      have hsplit : ‖x - y‖ = ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by
        rw [← Real.rpow_add' (norm_nonneg _) (by norm_num), sub_add_cancel, Real.rpow_one]
      calc |u x - u y| ≤ L * ‖x - y‖ := hlip
        _ = L * ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by rw [mul_assoc, ← hsplit]
        _ ≤ L * r ^ (1 - α) * ‖x - y‖ ^ α := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
            (by positivity)
          exact Real.rpow_le_rpow (norm_nonneg _) hdr (by linarith)
        _ ≤ M * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  refine ⟨Real.toNNReal M, holderOnWith_of_dist_le fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ hM0, Real.coe_toNNReal _ hα0.le]
  rcases le_total ‖x - z‖ ‖y - z‖ with h | h
  · exact key x hx y hy h
  · rw [dist_comm (u x), dist_comm x]
    exact key y hy x hx h

end Holder

end MatedCRT
