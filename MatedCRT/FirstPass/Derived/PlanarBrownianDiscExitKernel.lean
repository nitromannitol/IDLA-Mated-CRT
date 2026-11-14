import MatedCRT.Proofs.LBM.DirichletDiscExit
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-!
# Exit averages of the Newtonian kernel on a disc

Let `D = B_r(z)`, `y ∈ D`, and let `𝓑_τ` be the exit position from `D` of planar Brownian motion
started at `y`. For a pole `x ∉ ∂D` with `x ≠ y`,

  `E_y N(𝓑_τ, x) = N(y, x) - G_D(y, x)`,

where `N(w, x) = -(2π)⁻¹ log |w - x|` is the Newtonian kernel and `G_D` the Green function of `D`
(`G_D(y, x) = 0` for `x ∉ D`). For `x ∈ D` the right side is the greatest harmonic minorant of
`N(x, ·)` on `D` (Armitage-Gardiner §4.1), which is harmonic near the closed disc and equals
`N(x, ·)` on the circle; for `x ∉ cl D` the kernel `N(·, x)` itself is harmonic near the closed
disc. In both cases the bounded harmonic representation at the exit time applies to a bounded
continuous modification (composition with the radial retraction onto the closed disc).
-/

open MeasureTheory Set Filter Metric Topology InnerProductSpace MarkovProcess HarmonicBalls
  ComplexConjugate

namespace MatedCRT.KilledOccupation

/-- **Exit representation on a disc.** If `a` is continuous on `cl B_r(z)` and harmonic on
`B_r(z)`, and `φ = a` on the circle `∂B_r(z)`, then `E_y φ(𝓑_τ) = a(y)` for `y ∈ B_r(z)`, where
`τ` is the exit time of planar Brownian motion from `B_r(z)`. -/
theorem integral_exitTime_ball_eq_of_harmonicOnNhd {z : ℂ} {r : ℝ} (hr : 0 < r) {a φ : ℂ → ℝ}
    (ha : ContinuousOn a (closedBall z r)) (hh : HarmonicOnNhd a (ball z r))
    (hφ : ∀ w ∈ sphere z r, φ w = a w) {y : ℂ} (hy : y ∈ ball z r) :
    ∫ p, φ (p ((ContinuousPath.exitTime (ball z r) p).toNNReal)) ∂(planarBrownianMotion y) =
      a y := by
  set q : ℂ → ℝ := a ∘ ballRetraction z r with hqdef
  have hq : Continuous q :=
    ha.comp_continuous (continuous_ballRetraction z hr) (ballRetraction_mem z hr)
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn ha
  have hqM : ∀ w, ‖q w‖ ≤ M := fun w => hM _ (ballRetraction_mem z hr w)
  have hqa : ∀ w ∈ closedBall z r, q w = a w := fun w hw => by
    simp only [hqdef, Function.comp_apply, ballRetraction_of_mem z hr hw]
  have hqh : HarmonicOnNhd q (ball z r) := by
    intro w hw
    have heq : q =ᶠ[𝓝 w] a := by
      filter_upwards [isOpen_ball.mem_nhds hw] with u hu
      exact hqa u (ball_subset_closedBall hu)
    exact (harmonicAt_congr_nhds heq).2 (hh w hw)
  have he := Section6.harmonic_eq_integral_planarBrownian_exitTime isOpen_ball isBounded_ball
    hq hqh hqM hy
  rw [hqa y (ball_subset_closedBall hy)] at he
  rw [he]
  refine integral_congr_ae ?_
  filter_upwards [ae_planarBrownianMotion_pathExitPosition_mem_sphere hy] with p hp
  rw [pathExitPosition_eq_eval_exitTime] at hp
  rw [hφ _ hp, hqa _ (sphere_subset_closedBall hp)]

/-- The translated greatest harmonic minorant `u ↦ h_x(u - z)` of the disc `B_r(0)` is harmonic
wherever `r² - x̄ (u - z) ≠ 0`. -/
theorem harmonicAt_greatestHarmonicMinorantBall_sub {r : ℝ} {x z w : ℂ}
    (hw : (r : ℂ) ^ 2 - conj x * (w - z) ≠ 0) :
    HarmonicAt (fun u => greatestHarmonicMinorantBall r x (u - z)) w := by
  have ha : AnalyticAt ℂ (fun u => (r : ℂ) ^ 2 - conj x * (u - z)) w := by fun_prop
  have h1 := ((ha.harmonicAt_log_norm hw).sub (harmonicAt_const (Real.log r))).const_smul
    (c := -(2 * Real.pi)⁻¹)
  convert h1 using 1
  funext u
  simp [greatestHarmonicMinorantBall, smul_eq_mul]

/-- **Exit average of the Newtonian kernel, pole inside the disc.** For `x, y ∈ B_r(z)`, `x ≠ y`,
`E_y N(𝓑_τ, x) = N(y, x) - G_{B_r(z)}(y, x)`. -/
theorem integral_newtonKernel_exitTime_ball_of_mem {z x y : ℂ} {r : ℝ} (hx : x ∈ ball z r)
    (hy : y ∈ ball z r) (hxy : x ≠ y) :
    ∫ p, newtonKernel (p ((ContinuousPath.exitTime (ball z r) p).toNNReal)) x
        ∂(planarBrownianMotion y) = newtonKernel y x - greenFunction (ball z r) y x := by
  have hx' : ‖x - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hx
  have hr : 0 < r := (norm_nonneg _).trans_lt hx'
  have hne : ∀ w ∈ closedBall z r, (r : ℂ) ^ 2 - conj (x - z) * (w - z) ≠ 0 := fun w hw =>
    norm_pos_iff.1 (norm_sub_conj_mul_pos hr hx' (by rwa [mem_closedBall, dist_eq_norm] at hw))
  set a : ℂ → ℝ := fun u => greatestHarmonicMinorantBall r (x - z) (u - z) with hadef
  have ha : ContinuousOn a (closedBall z r) := fun w hw =>
    (harmonicAt_greatestHarmonicMinorantBall_sub (hne w hw)).1.continuousAt.continuousWithinAt
  have hh : HarmonicOnNhd a (ball z r) := fun w hw =>
    harmonicAt_greatestHarmonicMinorantBall_sub (hne w (ball_subset_closedBall hw))
  have hval : ∀ w ∈ closedBall z r, w ≠ x →
      a w = newtonKernel w x - greenBall r (x - z) (w - z) := by
    intro w hw hwx
    have h := newtonKernel_sub_greenBall hr (x := x - z) (z := w - z)
      (fun h => hwx (sub_left_inj.1 h).symm) (norm_ne_zero_iff.2 (hne w hw))
    have hN : newtonKernel (x - z) (w - z) = newtonKernel w x := by
      rw [newtonKernel_comm]
      simp only [newtonKernel, sub_sub_sub_cancel_right]
    rw [hN] at h
    show greatestHarmonicMinorantBall r (x - z) (w - z) = _
    linarith
  have hφ : ∀ w ∈ sphere z r, newtonKernel w x = a w := by
    intro w hw
    have hw' : ‖w - z‖ = r := by rwa [mem_sphere, dist_eq_norm] at hw
    have hwx : w ≠ x := fun h => by rw [h] at hw'; linarith
    have h0 : greenBall r (x - z) (w - z) = 0 :=
      le_antisymm (greenBall_nonpos hr hx'.le hw'.ge) (greenBall_nonneg hr hx'.le hw'.le)
    rw [hval w (sphere_subset_closedBall hw) hwx, h0, sub_zero]
  refine (integral_exitTime_ball_eq_of_harmonicOnNhd hr ha hh hφ hy).trans ?_
  rw [hval y (ball_subset_closedBall hy) (Ne.symm hxy)]
  congr 1
  have hx0 : x - z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.2 hx'
  have hy0 : y - z ∈ ball (0 : ℂ) r :=
    mem_ball_zero_iff.2 (by rwa [mem_ball, dist_eq_norm] at hy)
  rw [greenFunction_ball_translate, greenFunction_ball_comm,
    greenFunction_ball hx0 hy0 (fun h => hxy (sub_left_inj.1 h))]

/-- **Exit average of the Newtonian kernel, pole outside the closed disc.** For
`x ∉ cl B_r(z)` and `y ∈ B_r(z)`, `E_y N(𝓑_τ, x) = N(y, x) - G_{B_r(z)}(y, x)` (the Green function
vanishes, `N(·, x)` being harmonic near the closed disc). -/
theorem integral_newtonKernel_exitTime_ball_of_notMem_closedBall {z x y : ℂ} {r : ℝ}
    (hr : 0 < r) (hx : x ∉ closedBall z r) (hy : y ∈ ball z r) :
    ∫ p, newtonKernel (p ((ContinuousPath.exitTime (ball z r) p).toNNReal)) x
        ∂(planarBrownianMotion y) = newtonKernel y x - greenFunction (ball z r) y x := by
  have hN : (fun w => newtonKernel w x) = newtonKernel x := funext fun w => newtonKernel_comm w x
  have hh : ∀ w ∈ closedBall z r, HarmonicAt (fun w => newtonKernel w x) w := fun w hw => by
    rw [hN]
    exact harmonicAt_newtonKernel (fun h => hx (h ▸ hw))
  refine (integral_exitTime_ball_eq_of_harmonicOnNhd hr (a := fun w => newtonKernel w x)
    (φ := fun w => newtonKernel w x) (fun w hw => (hh w hw).1.continuousAt.continuousWithinAt)
    (fun w hw => hh w (ball_subset_closedBall hw)) (fun _ _ => rfl) hy).trans ?_
  rw [greenFunction_of_notMem_right (fun h => hx (ball_subset_closedBall h)), sub_zero]

/-- **Exit average of the Newtonian kernel on a disc (B5).** For `y ∈ B_r(z)` and a pole `x` off
the circle `∂B_r(z)` with `x ≠ y`, `E_y N(𝓑_τ, x) = N(y, x) - G_{B_r(z)}(y, x)`. -/
theorem integral_newtonKernel_exitTime_ball {z x y : ℂ} {r : ℝ} (hy : y ∈ ball z r)
    (hxs : x ∉ sphere z r) (hxy : x ≠ y) :
    ∫ p, newtonKernel (p ((ContinuousPath.exitTime (ball z r) p).toNNReal)) x
        ∂(planarBrownianMotion y) = newtonKernel y x - greenFunction (ball z r) y x := by
  have hr : 0 < r := dist_nonneg.trans_lt (mem_ball.1 hy)
  by_cases hx : x ∈ ball z r
  · exact integral_newtonKernel_exitTime_ball_of_mem hx hy hxy
  · refine integral_newtonKernel_exitTime_ball_of_notMem_closedBall hr (fun h => ?_) hy
    rcases (mem_closedBall.1 h).lt_or_eq with h' | h'
    · exact hx (mem_ball.2 h')
    · exact hxs (mem_sphere.2 h')

end MatedCRT.KilledOccupation
