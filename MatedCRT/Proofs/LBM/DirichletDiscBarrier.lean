import HarmonicBalls.Proofs.Potential.DiscPoisson

/-!
# The Poisson extension of boundary data on a disc, and a Hölder barrier at the boundary

For boundary data `φ` on the circle `∂B_r(z)`, the *Poisson extension* is the Poisson integral
`P_{B_r(z)}[φ]` inside the disc and `φ` outside. It is harmonic in `B_r(z)` and, for `φ` continuous on
`∂B_r(z)`, continuous on `cl B_r(z)` (HB `tendsto_discPoissonIntegral_of_continuousOn`).

For `0 < α < 1` and `ζ₀ ∈ ∂B_r(z)`, the barrier `v(x) = Re(w(x)^α)`, `w(x) = \bar{(ζ₀ - z)} (ζ₀ - x) / r²`,
is harmonic in `B_r(z)` (real part of a holomorphic function: `Re w > 0` there), continuous on `cl B_r(z)`,
and comparable to `(|x - ζ₀| / r)^α`: `cos(απ/2) (|x - ζ₀|/r)^α ≤ v(x) ≤ (|x - ζ₀|/r)^α`. With the
monotonicity of the Poisson integral it gives the boundary Hölder estimate
`|P_{B_r(z)}[φ](x) - φ(ζ₀)| ≤ C cos(απ/2)⁻¹ |x - ζ₀|^α` for `α`-Hölder data with constant `C`
(Gilbarg-Trudinger, Lemma 4.2 and Section 2.8; Armitage-Gardiner, Section 1.3).
-/

namespace MatedCRT

open Metric Filter Topology Set MeasureTheory InnerProductSpace HarmonicBalls

/-! ## The Poisson extension -/

open Classical in
/-- The **Poisson extension** of `φ` from `∂B_r(z)`: the Poisson integral `P_{B_r(z)}[φ]` in the open disc
and `φ` elsewhere. -/
noncomputable def discPoissonExtension (φ : ℂ → ℝ) (z : ℂ) (r : ℝ) (x : ℂ) : ℝ :=
  if x ∈ ball z r then discPoissonIntegral φ z r x else φ x

section Extension

variable {φ : ℂ → ℝ} {z : ℂ} {r : ℝ}

theorem discPoissonExtension_of_mem {x : ℂ} (hx : x ∈ ball z r) :
    discPoissonExtension φ z r x = discPoissonIntegral φ z r x := by
  rw [discPoissonExtension, ite_eq_left hx]

theorem discPoissonExtension_of_notMem {x : ℂ} (hx : x ∉ ball z r) :
    discPoissonExtension φ z r x = φ x := by
  rw [discPoissonExtension, ite_eq_right hx]

theorem notMem_ball_of_mem_sphere {x : ℂ} (hx : x ∈ sphere z r) : x ∉ ball z r :=
  fun h => (sphere_disjoint_ball.ne_of_mem hx h) rfl

theorem mem_sphere_of_mem_closedBall_of_notMem_ball {x : ℂ} (hx : x ∈ closedBall z r)
    (hx' : x ∉ ball z r) : x ∈ sphere z r :=
  mem_sphere.2 (le_antisymm (mem_closedBall.1 hx) (not_lt.1 fun h => hx' (mem_ball.2 h)))

theorem harmonicOnNhd_discPoissonExtension (hφ : CircleIntegrable φ z r) :
    HarmonicOnNhd (discPoissonExtension φ z r) (ball z r) := by
  intro y hy
  have heq : discPoissonExtension φ z r =ᶠ[𝓝 y] discPoissonIntegral φ z r := by
    filter_upwards [isOpen_ball.mem_nhds hy] with w hw
    exact discPoissonExtension_of_mem hw
  exact (harmonicAt_congr_nhds heq).2 (harmonicOnNhd_discPoissonIntegral hφ y hy)

/-- The Poisson extension of continuous boundary data solves the Dirichlet problem on the disc. -/
theorem continuousOn_discPoissonExtension (hr : 0 < r) (hφ : ContinuousOn φ (sphere z r)) :
    ContinuousOn (discPoissonExtension φ z r) (closedBall z r) := by
  rw [← ball_union_sphere]
  intro x hx
  rw [continuousWithinAt_union]
  rcases hx with hxb | hxs
  · have hc : ContinuousAt (discPoissonExtension φ z r) x :=
      (harmonicOnNhd_discPoissonExtension (hφ.circleIntegrable hr.le) x hxb).1.continuousAt
    exact ⟨hc.continuousWithinAt, hc.continuousWithinAt⟩
  · have hxn := notMem_ball_of_mem_sphere hxs
    constructor
    · have ht := tendsto_discPoissonIntegral_of_continuousOn hr hφ hxs
      rw [ContinuousWithinAt, discPoissonExtension_of_notMem hxn]
      refine ht.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (discPoissonExtension_of_mem hw).symm
    · exact (hφ x hxs).congr (fun w hw => discPoissonExtension_of_notMem
        (notMem_ball_of_mem_sphere hw)) (discPoissonExtension_of_notMem hxn)

/-- **Poisson representation** of a function harmonic in the disc and continuous on its closure. -/
theorem eq_discPoissonIntegral_of_harmonicOnNhd {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball z r))
    (hgc : ContinuousOn g (closedBall z r)) {x : ℂ} (hx : x ∈ ball z r) :
    g x = discPoissonIntegral g z r x :=
  ((HarmonicContOnCl.mk_ball hg hgc).circleAverage_poissonKernel_smul hx).symm

/-- **Maximum principle** on a disc, for functions harmonic inside and continuous up to the boundary. -/
theorem abs_le_of_harmonicOnNhd {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball z r))
    (hgc : ContinuousOn g (closedBall z r)) {M : ℝ} (hM : ∀ ζ ∈ sphere z r, |g ζ| ≤ M)
    {x : ℂ} (hx : x ∈ closedBall z r) : |g x| ≤ M := by
  by_cases hxb : x ∈ ball z r
  · have hr : 0 < r := dist_nonneg.trans_lt hxb
    have hgi : CircleIntegrable g z r :=
      (hgc.mono sphere_subset_closedBall).circleIntegrable hr.le
    rw [eq_discPoissonIntegral_of_harmonicOnNhd hg hgc hxb, abs_le]
    constructor
    · exact le_discPoissonIntegral hgi hxb fun ζ hζ => (abs_le.1 (hM ζ hζ)).1
    · rw [← discPoissonIntegral_const M hxb]
      exact discPoissonIntegral_mono hgi continuousOn_const.circleIntegrable' hxb
        fun ζ hζ => (abs_le.1 (hM ζ hζ)).2
  · exact hM x (mem_sphere_of_mem_closedBall_of_notMem_ball hx hxb)

end Extension

/-! ## The boundary barrier -/

section Barrier

variable {z ζ₀ : ℂ} {r α : ℝ}

/-- The affine map `w(x) = \bar{(ζ₀ - z)} (ζ₀ - x) / r²`, which sends `B_r(z)` into the right half-plane
and `ζ₀` to `0`. -/
noncomputable def discBarrierBase (z ζ₀ : ℂ) (r : ℝ) (x : ℂ) : ℂ :=
  starRingEnd ℂ (ζ₀ - z) / ((r ^ 2 : ℝ) : ℂ) * (ζ₀ - x)

/-- The **Hölder barrier** `v(x) = Re(w(x)^α)` at the boundary point `ζ₀` of `B_r(z)`. -/
noncomputable def discBarrier (z ζ₀ : ℂ) (r α : ℝ) (x : ℂ) : ℝ :=
  (discBarrierBase z ζ₀ r x ^ (α : ℂ)).re

theorem norm_discBarrierBase (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r) (x : ℂ) :
    ‖discBarrierBase z ζ₀ r x‖ = ‖x - ζ₀‖ / r := by
  have ha : ‖ζ₀ - z‖ = r := by simpa [dist_eq_norm] using hζ₀
  rw [discBarrierBase, norm_mul, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < r ^ 2), ha, norm_sub_rev]
  field_simp

theorem re_discBarrierBase_ge (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r) (x : ℂ) :
    (r - ‖x - z‖) / r ≤ (discBarrierBase z ζ₀ r x).re := by
  have ha : ‖ζ₀ - z‖ = r := by simpa [dist_eq_norm] using hζ₀
  have hsplit : discBarrierBase z ζ₀ r x =
      (starRingEnd ℂ (ζ₀ - z) * (ζ₀ - z) - starRingEnd ℂ (ζ₀ - z) * (x - z)) / ((r ^ 2 : ℝ) : ℂ) := by
    rw [discBarrierBase]; ring
  have hre : (starRingEnd ℂ (ζ₀ - z) * (x - z)).re ≤ r * ‖x - z‖ :=
    (Complex.re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj, ha])
  rw [hsplit, Complex.div_ofReal_re, Complex.sub_re, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re, ha, le_div_iff₀ (by positivity)]
  have : (r - ‖x - z‖) / r * r ^ 2 = r * r - r * ‖x - z‖ := by field_simp
  linarith

theorem re_discBarrierBase_nonneg (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r) {x : ℂ}
    (hx : x ∈ closedBall z r) : 0 ≤ (discBarrierBase z ζ₀ r x).re := by
  refine le_trans ?_ (re_discBarrierBase_ge hr hζ₀ x)
  have : ‖x - z‖ ≤ r := by simpa [dist_eq_norm] using hx
  exact div_nonneg (by linarith) hr.le

theorem re_discBarrierBase_pos (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r) {x : ℂ}
    (hx : x ∈ ball z r) : 0 < (discBarrierBase z ζ₀ r x).re := by
  refine lt_of_lt_of_le ?_ (re_discBarrierBase_ge hr hζ₀ x)
  have : ‖x - z‖ < r := by simpa [dist_eq_norm] using hx
  exact div_pos (by linarith) hr

theorem analyticAt_discBarrierBase (x : ℂ) : AnalyticAt ℂ (discBarrierBase z ζ₀ r) x :=
  analyticAt_const.mul (analyticAt_const.sub analyticAt_id)

theorem continuous_discBarrierBase : Continuous (discBarrierBase z ζ₀ r) :=
  continuous_const.mul (continuous_const.sub continuous_id)

theorem harmonicOnNhd_discBarrier (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r) :
    HarmonicOnNhd (discBarrier z ζ₀ r α) (ball z r) := by
  intro x hx
  have hslit : discBarrierBase z ζ₀ r x ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (re_discBarrierBase_pos hr hζ₀ hx))
  exact ((analyticAt_discBarrierBase x).cpow analyticAt_const hslit).harmonicAt_re

theorem continuousOn_discBarrier (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r) (hα : 0 < α) :
    ContinuousOn (discBarrier z ζ₀ r α) (closedBall z r) := by
  intro x hx
  have hc : ContinuousAt (fun w : ℂ => w ^ (α : ℂ)) (discBarrierBase z ζ₀ r x) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl (re_discBarrierBase_nonneg hr hζ₀ hx))
      (by simpa using hα)
  exact (Complex.continuous_re.continuousAt.comp
    (hc.comp continuous_discBarrierBase.continuousAt)).continuousWithinAt

theorem re_cpow_real_eq (w : ℂ) (α : ℝ) :
    (w ^ (α : ℂ)).re = ‖w‖ ^ α * Real.cos (w.arg * α) := by
  rw [Complex.cpow_ofReal]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem re_cpow_real_le (w : ℂ) (α : ℝ) : (w ^ (α : ℂ)).re ≤ ‖w‖ ^ α :=
  (Complex.re_le_norm _).trans (Complex.norm_cpow_real w α).le

theorem cos_mul_rpow_le_re_cpow {w : ℂ} (hw : 0 ≤ w.re) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Real.cos (α * (Real.pi / 2)) * ‖w‖ ^ α ≤ (w ^ (α : ℂ)).re := by
  rw [re_cpow_real_eq, mul_comm (Real.cos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg w) α)
  have harg : |w.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.2 hw
  rw [← Real.cos_abs (w.arg * α)]
  have h1 : |w.arg * α| ≤ α * (Real.pi / 2) := by
    rw [abs_mul, abs_of_nonneg hα0, mul_comm]
    exact mul_le_mul_of_nonneg_left harg hα0
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) ?_ h1
  nlinarith [Real.pi_pos]

theorem cos_half_pi_mul_pos (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < Real.cos (α * (Real.pi / 2)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- **Boundary Hölder estimate**, one-sided form: if `φ ≤ a + C|· - ζ₀|^α` on `∂B_r(z)`, then
`P_{B_r(z)}[φ] ≤ a + C cos(απ/2)⁻¹ |· - ζ₀|^α` in `B_r(z)`. -/
theorem discPoissonIntegral_le_add_rpow {φ : ℂ → ℝ} (hr : 0 < r) (hζ₀ : ζ₀ ∈ sphere z r)
    (hα0 : 0 < α) (hα1 : α < 1) {C a : ℝ} (hC : 0 ≤ C) (hφi : CircleIntegrable φ z r)
    (hφ : ∀ ζ ∈ sphere z r, φ ζ ≤ a + C * ‖ζ - ζ₀‖ ^ α) {x : ℂ} (hx : x ∈ ball z r) :
    discPoissonIntegral φ z r x ≤ a + C / Real.cos (α * (Real.pi / 2)) * ‖x - ζ₀‖ ^ α := by
  set κ := Real.cos (α * (Real.pi / 2)) with hκ
  have hκ0 : 0 < κ := cos_half_pi_mul_pos hα0.le hα1
  set K := C * r ^ α / κ with hK
  have hK0 : 0 ≤ K := by positivity
  set g : ℂ → ℝ := fun y => a + K * discBarrier z ζ₀ r α y with hg
  have hgh : HarmonicOnNhd g (ball z r) := fun y hy =>
    (harmonicAt_const a).add ((harmonicOnNhd_discBarrier hr hζ₀ y hy).const_smul (c := K))
  have hgc : ContinuousOn g (closedBall z r) :=
    continuousOn_const.add (continuousOn_const.mul (continuousOn_discBarrier hr hζ₀ hα0))
  have hgi : CircleIntegrable g z r := (hgc.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hnorm : ∀ y, ‖discBarrierBase z ζ₀ r y‖ ^ α = ‖y - ζ₀‖ ^ α / r ^ α := fun y => by
    rw [norm_discBarrierBase hr hζ₀, Real.div_rpow (norm_nonneg _) hr.le]
  have hle : ∀ ζ ∈ sphere z r, φ ζ ≤ g ζ := by
    intro ζ hζ
    have hb := cos_mul_rpow_le_re_cpow (w := discBarrierBase z ζ₀ r ζ)
      (re_discBarrierBase_nonneg hr hζ₀ (sphere_subset_closedBall hζ)) hα0.le hα1.le
    rw [hnorm] at hb
    have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
    have : C * ‖ζ - ζ₀‖ ^ α ≤ K * discBarrier z ζ₀ r α ζ := by
      rw [hK, div_mul_eq_mul_div, le_div_iff₀ hκ0]
      have h2 : κ * (‖ζ - ζ₀‖ ^ α / r ^ α) * (C * r ^ α) ≤
          discBarrier z ζ₀ r α ζ * (C * r ^ α) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      have h3 : κ * (‖ζ - ζ₀‖ ^ α / r ^ α) * (C * r ^ α) = C * ‖ζ - ζ₀‖ ^ α * κ := by
        field_simp
      linarith
    linarith [hφ ζ hζ]
  have hP := discPoissonIntegral_mono hφi hgi hx hle
  rw [← eq_discPoissonIntegral_of_harmonicOnNhd hgh hgc hx] at hP
  have hv : discBarrier z ζ₀ r α x ≤ ‖x - ζ₀‖ ^ α / r ^ α := by
    rw [← hnorm]; exact re_cpow_real_le _ _
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have : K * discBarrier z ζ₀ r α x ≤ C / κ * ‖x - ζ₀‖ ^ α := by
    calc K * discBarrier z ζ₀ r α x ≤ K * (‖x - ζ₀‖ ^ α / r ^ α) :=
          mul_le_mul_of_nonneg_left hv hK0
      _ = C / κ * ‖x - ζ₀‖ ^ α := by rw [hK]; field_simp
  simp only [hg] at hP
  linarith

end Barrier

end MatedCRT
