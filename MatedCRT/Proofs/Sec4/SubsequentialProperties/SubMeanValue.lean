import MatedCRT.Proofs.Sec4.SubsequentialProperties.Hats
import MatedCRT.Proofs.Sec4.SubsequentialProperties.MeanValue
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison
import MatedCRT.Proofs.Sec5.MeanValueInequality.CellRepresentative

/-!
# The sub-mean-value inequality of a limit of discrete subharmonic functions

The pathwise core of Step 2 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1803-1857), for a fixed
disc `B_r(z) ⋐ B_ρ`:

`le_circleAverage_of_discrete_subharmonic`: let `U_k` be discrete subharmonic on `V^{ε_k}(B_r(z)) \ V^{ε_k}(∂B_r(z))`
(for large `k`), with `m_k⁻¹ U_k(a^{ε_k}_x) → v(x)` uniformly on `cl(B_ρ)`, on maps whose adjacent cells intersect and
which satisfy the maximum principle (Lemma 2.13). If the rescaled solutions of the discrete Dirichlet problems with data
`m_k hat_p(η(b))` converge at `z` to `⨍_{∂B_r(z)} hat_p` (Lemma 3.5 and `eq_circleAverage_of_hasLaplacian_zero`), then
`v(z) ≤ ⨍_{∂B_r(z)} v`.

The proof follows the paper: the data `φ = ∑_p v(p) hat_p` approximate `v` near `∂B_r(z)` (`abs_sub_sum_hat_le`); on
`V^ε(∂B_r(z))` the discrete function is bounded by `m_k (φ(η(b)) + 3δ)` through a point of the cell of `b` whose
least cell is `b` (`exists_vertexOf_eq_of_area_parametrized`) and the smallness of the cells
(`Tightness.exists_cell_near_vertexPoint`); the maximum principle (`le_add_of_maxPrinciple`) propagates the bound to
`a^ε_z`. If `m_k = 0` infinitely often, `v = 0`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real

/-- A closed disc inside `B_ρ(0)` satisfies `|z| + s < ρ`. -/
theorem norm_add_lt_of_closedBall_subset_ball {z : ℂ} {s ρ : ℝ} (hs : 0 ≤ s) (h : closedBall z s ⊆ ball 0 ρ) :
    ‖z‖ + s < ρ := by
  have hsn : ‖((s : ℝ) : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  by_cases hz : z = 0
  · subst hz
    have hmem : ((s : ℝ) : ℂ) ∈ closedBall (0 : ℂ) s :=
      mem_closedBall.2 (le_of_eq (by rw [dist_zero_right, hsn]))
    have := h hmem
    rw [mem_ball, dist_zero_right, hsn] at this
    rw [norm_zero, zero_add]
    exact this
  · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hy : z + ((s / ‖z‖ : ℝ) : ℂ) * z ∈ closedBall z s := by
      rw [mem_closedBall, dist_eq_norm]
      refine le_of_eq ?_
      rw [show z + ((s / ‖z‖ : ℝ) : ℂ) * z - z = ((s / ‖z‖ : ℝ) : ℂ) * z by ring, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs hz'.le), div_mul_cancel₀ s hz'.ne']
    have hny : ‖z + ((s / ‖z‖ : ℝ) : ℂ) * z‖ = ‖z‖ + s := by
      rw [show z + ((s / ‖z‖ : ℝ) : ℂ) * z = ((1 + s / ‖z‖ : ℝ) : ℂ) * z by push_cast; ring, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul, one_mul,
        div_mul_cancel₀ s hz'.ne']
    have := h hy
    rw [mem_ball, dist_zero_right, hny] at this
    exact this

/-- The circle average of a combination of hats. -/
theorem circleAverage_sum_mul_hat (n : ℕ) (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℝ) (z : ℂ) (r : ℝ) :
    circleAverage (fun x => ∑ p ∈ S, c p * hat n p.1 p.2 x) z r =
      ∑ p ∈ S, c p * circleAverage (hat n p.1 p.2) z r := by
  rw [Real.circleAverage_fun_sum fun p _ =>
    (continuous_const.mul (continuous_hat n p.1 p.2)).continuousOn.circleIntegrable']
  refine Finset.sum_congr rfl fun p _ => ?_
  simpa only [smul_eq_mul] using
    (Real.circleAverage_fun_smul (f := hat n p.1 p.2) (c := z) (R := r) (a := c p))

/-- **Discrete comparison with a combination of Dirichlet solutions** (one mesh). If `U` is subharmonic on
`A = V^ε(B_r(z)) \ V^ε(∂B_r(z))` and `m⁻¹ U ≤ φ(η(·)) + β` on `V^ε(∂B_r(z))`, where `φ = ∑_p c_p hat_p`, then
`m⁻¹ U(a^ε_z) ≤ ∑_p c_p m⁻¹ f_p(a^ε_z) + β` for the solutions `f_p` of the discrete Dirichlet problems with data
`m hat_p(η(·))`. -/
theorem le_sum_dirichletData_add {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε : ℝ} (hε : 0 < ε) {M : ℤ → ℤ → ℕ}
    (hlf : ∀ a, {b | M a b ≠ 0}.Finite) (hcons : ∀ i : ℤ, M i (i + 1) ≠ 0)
    (hcells : ∀ j l : ℤ, M j l ≠ 0 → (cell ε η j ∩ cell ε η l).Nonempty)
    (hmax : ∀ A : Set ℤ, A.Nonempty → A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn M u A →
      ∀ a ∈ A, ∃ b ∈ vBoundary M A, u a ≤ u b)
    {U : ℤ → ℝ} {m : ℝ} (hm : 0 < m) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ a ∈ interiorCellVertices ε η (ball z r), 0 ≤ mLaplacian M U a)
    {S : Finset (ℤ × ℤ)} {c : ℤ × ℤ → ℝ} {n : ℕ} {φ : ℂ → ℝ}
    (hφ : φ = fun x => ∑ p ∈ S, c p * hat n p.1 p.2 x) {β : ℝ}
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), m⁻¹ * U b ≤ φ (vertexPoint ε η b) + β) :
    m⁻¹ * U (vertexOf ε η z) ≤
      ∑ p ∈ S, c p * (m⁻¹ * dirichletData M (interiorCellVertices ε η (ball z r))
        (fun b => m * hat n p.1 p.2 (vertexPoint ε η b)) (vertexOf ε η z)) + β := by
  obtain ⟨A, hAdef⟩ : ∃ A : Set ℤ, A = interiorCellVertices ε η (ball z r) := ⟨_, rfl⟩
  rw [← hAdef]
  rw [← hAdef] at hsub
  have hA : A.Finite := by
    rw [hAdef]
    exact (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset fun b hb => hb.1
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℝ,
      F = fun a => ∑ p ∈ S, c p * dirichletData M A (fun b => m * hat n p.1 p.2 (vertexPoint ε η b)) a :=
    ⟨_, rfl⟩
  have hFlap : ∀ a ∈ A, mLaplacian M F a = 0 := by
    intro a ha
    rw [hF, mLaplacian_finset_sum hlf]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [mLaplacian_const_mul, mLaplacian_dirichletData hlf hcons hA _ ha, mul_zero]
  have hFbd : ∀ b ∈ cellVertices ε η (sphere z r), F b = m * φ (vertexPoint ε η b) := by
    intro b hb
    have hbA : b ∉ A := by
      rw [hAdef]
      exact fun h => h.2 (by rwa [frontier_ball z hr.ne'])
    simp only [hF, hφ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dirichletData_of_not_mem hA _ hbA]
    ring
  have hmaxA : ∀ a ∈ interiorCellVertices ε η (ball z r),
      ∃ b ∈ vBoundary M (interiorCellVertices ε η (ball z r)), U a - F a ≤ U b - F b := by
    rw [← hAdef]
    intro a ha
    have hsubu : IsSubharmonicOn M (fun x => U x - F x) A := fun a' ha' => by
      rw [mLaplacian_sub_of_locallyFinite hlf, hFlap a' ha', sub_zero]
      exact hsub a' ha'
    exact hmax A ⟨a, ha⟩ hA _ hsubu a ha
  have hbd' : ∀ b ∈ cellVertices ε η (sphere z r), U b ≤ F b + m * β := by
    intro b hb
    rw [hFbd b hb]
    have h1 := mul_le_mul_of_nonneg_left (hbd b hb) hm.le
    rw [mul_inv_cancel_left₀ hm.ne'] at h1
    linarith
  have hvz : vertexOf ε η z ∈ cellVertices ε η (ball z r) :=
    show (cell ε η (vertexOf ε η z) ∩ ball z r).Nonempty from
      ⟨z, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε z, mem_ball_self hr⟩
  have hcomp := le_add_of_maxPrinciple harea.1 hr hcells hmaxA hbd' _ hvz
  have hFz : m⁻¹ * F (vertexOf ε η z) =
      ∑ p ∈ S, c p * (m⁻¹ * dirichletData M A (fun b => m * hat n p.1 p.2 (vertexPoint ε η b))
        (vertexOf ε η z)) := by
    simp only [hF]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [← hFz]
  calc m⁻¹ * U (vertexOf ε η z) ≤ m⁻¹ * (F (vertexOf ε η z) + m * β) :=
        mul_le_mul_of_nonneg_left hcomp (inv_nonneg.2 hm.le)
    _ = m⁻¹ * F (vertexOf ε η z) + β := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

/-- **Sub-mean-value inequality of a limit of discrete subharmonic functions** (Step 2 of the proof of Lemma 4.8,
pathwise, for one disc `B_r(z)` with `|z| + r < ρ`). -/
theorem le_circleAverage_of_discrete_subharmonic {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ρ : ℝ} {v : ℂ → ℝ} (hv : ContinuousOn v (closedBall 0 ρ))
    {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k) (hεk0 : Tendsto εk atTop (𝓝 0))
    {M : ℕ → ℤ → ℤ → ℕ} (hlf : ∀ k a, {b | M k a b ≠ 0}.Finite) (hcons : ∀ k (i : ℤ), M k i (i + 1) ≠ 0)
    (hcells : ∀ k (j l : ℤ), M k j l ≠ 0 → (cell (εk k) η j ∩ cell (εk k) η l).Nonempty)
    (hmax : ∀ k, ∀ A : Set ℤ, A.Nonempty → A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn (M k) u A →
      ∀ a ∈ A, ∃ b ∈ vBoundary (M k) A, u a ≤ u b)
    {U : ℕ → ℤ → ℝ} {m : ℕ → ℝ} (hm : ∀ k, 0 ≤ m k)
    (hconv : TendstoUniformlyOn (fun k x => (m k)⁻¹ * U k (vertexOf (εk k) η x)) v atTop (closedBall 0 ρ))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ + r < ρ)
    (hsub : ∀ᶠ k in atTop, ∀ a ∈ interiorCellVertices (εk k) η (ball z r), 0 ≤ mLaplacian (M k) (U k) a)
    (hdir : ∀ (n : ℕ) (j l : ℤ), Tendsto (fun k => (m k)⁻¹ * dirichletData (M k)
        (interiorCellVertices (εk k) η (ball z r)) (fun b => m k * hat n j l (vertexPoint (εk k) η b))
        (vertexOf (εk k) η z)) atTop (𝓝 (circleAverage (hat n j l) z r))) :
    v z ≤ circleAverage v z r := by
  have hz : z ∈ closedBall (0 : ℂ) ρ := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hsphB : ∀ y ∈ sphere z r, ‖y‖ ≤ ‖z‖ + r := by
    intro y hy
    have h := dist_triangle y z 0
    rw [dist_zero_right, dist_zero_right, mem_sphere.1 hy] at h
    linarith
  have hsphsub : sphere z r ⊆ closedBall (0 : ℂ) ρ := fun y hy => by
    rw [mem_closedBall, dist_zero_right]; linarith [hsphB y hy]
  by_cases hfreq : ∃ᶠ k in atTop, m k = 0
  · have hv0 : ∀ x ∈ closedBall (0 : ℂ) ρ, v x = 0 := fun x hx =>
      tendsto_nhds_unique_of_frequently_eq (hconv.tendsto_at hx) tendsto_const_nhds
        (hfreq.mono fun k hk => by simp [hk])
    rw [hv0 z hz]
    have h : circleAverage v z r = circleAverage (fun _ => (0 : ℝ)) z r :=
      circleAverage_congr_sphere fun y hy => by
        rw [abs_of_pos hr] at hy
        exact hv0 y (hsphsub hy)
    rw [h, circleAverage_const]
  rw [not_frequently] at hfreq
  have hmpos : ∀ᶠ k in atTop, 0 < m k := hfreq.mono fun k hk => lt_of_le_of_ne (hm k) (Ne.symm hk)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = δ / 4 := ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; positivity
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ρ - (‖z‖ + r) := ⟨_, rfl⟩
  have hdpos : 0 < d := by rw [hd]; linarith
  obtain ⟨η₁, hη₁, hη₁v⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) ρ).uniformContinuousOn_of_continuous hv) δ₀ hδ₀pos
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min η₁ (d / 2) := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; exact lt_min hη₁ (half_pos hdpos)
  have hs1 : s ≤ η₁ := by rw [hs]; exact min_le_left _ _
  have hs2 : s ≤ d / 2 := by rw [hs]; exact min_le_right _ _
  -- the scale of the hats
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / s)
  have hnpos' : (0 : ℝ) < n := lt_trans (by positivity) hn
  have hnpos : 0 < n := by exact_mod_cast hnpos'
  have h2n : 2 / (n : ℝ) < s := by
    rw [div_lt_iff₀ hnpos']
    rw [div_lt_iff₀ hspos] at hn
    linarith
  obtain ⟨N, hNbd⟩ : ∃ N : ℕ, ∀ x ∈ closedBall (0 : ℂ) ρ,
      |(n : ℝ) * x.re| + 1 ≤ N ∧ |(n : ℝ) * x.im| + 1 ≤ N := by
    refine ⟨⌈(n : ℝ) * ρ⌉₊ + 1, fun x hx => ?_⟩
    rw [mem_closedBall, dist_zero_right] at hx
    have hc : (n : ℝ) * ρ ≤ ⌈(n : ℝ) * ρ⌉₊ := Nat.le_ceil _
    have hre : |(n : ℝ) * x.re| ≤ n * ρ := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm x).trans hx) hnpos'.le
    have him : |(n : ℝ) * x.im| ≤ n * ρ := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm x).trans hx) hnpos'.le
    push_cast
    constructor <;> linarith
  -- the boundary data `φ = ∑_p v(p) hat_p`
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℝ,
      φ = fun x => ∑ p ∈ hatIndex N, v (hatPoint n p.1 p.2) * hat n p.1 p.2 x := ⟨_, rfl⟩
  have happrox : ∀ x ∈ closedBall (0 : ℂ) (ρ - d / 2), |v x - φ x| ≤ δ₀ := by
    intro x hx
    have hx' : x ∈ closedBall (0 : ℂ) ρ := closedBall_subset_closedBall (by linarith) hx
    rw [hφ]
    refine abs_sub_sum_hat_le hnpos (hNbd x hx').1 (hNbd x hx').2 fun p _ hpd => ?_
    have hpB : hatPoint n p.1 p.2 ∈ closedBall (0 : ℂ) ρ := by
      rw [mem_closedBall, dist_zero_right] at hx ⊢
      have h := dist_triangle (hatPoint n p.1 p.2) x 0
      rw [dist_zero_right, dist_zero_right, dist_comm] at h
      linarith
    have h := hη₁v x hx' _ hpB (hpd.trans (h2n.trans_le hs1))
    rw [Real.dist_eq] at h
    exact h.le
  -- cell sizes and uniform convergence
  obtain ⟨ε₀, hε₀, hcellsz⟩ := Tightness.exists_cell_near_vertexPoint harea.1 hp
    (isBounded_closedBall (x := (0 : ℂ)) (r := ρ)) (s := s / 4) (by positivity)
  have hunif := Metric.tendstoUniformlyOn_iff.1 hconv δ₀ hδ₀pos
  -- the limits
  have hlimD : Tendsto (fun k => ∑ p ∈ hatIndex N, v (hatPoint n p.1 p.2) * ((m k)⁻¹ * dirichletData (M k)
      (interiorCellVertices (εk k) η (ball z r)) (fun b => m k * hat n p.1 p.2 (vertexPoint (εk k) η b))
      (vertexOf (εk k) η z))) atTop
      (𝓝 (∑ p ∈ hatIndex N, v (hatPoint n p.1 p.2) * circleAverage (hat n p.1 p.2) z r)) :=
    tendsto_finsetSum _ fun p _ => (hdir n p.1 p.2).const_mul _
  have hlimL := hconv.tendsto_at hz
  have hev : ∀ᶠ k in atTop, (m k)⁻¹ * U k (vertexOf (εk k) η z) ≤
      ∑ p ∈ hatIndex N, v (hatPoint n p.1 p.2) * ((m k)⁻¹ * dirichletData (M k)
        (interiorCellVertices (εk k) η (ball z r)) (fun b => m k * hat n p.1 p.2 (vertexPoint (εk k) η b))
        (vertexOf (εk k) η z)) + 3 * δ₀ := by
    filter_upwards [hmpos, hsub, hεk0.eventually (gt_mem_nhds hε₀), hunif] with k hmk hsubk hεk₀ hunifk
    refine le_sum_dirichletData_add harea hp (hεk k) (hlf k) (hcons k) (hcells k) (hmax k) hmk hr hsubk hφ ?_
    intro b hb
    obtain ⟨y₀, hy₀b, hy₀s⟩ := hb
    have hy₀B : y₀ ∈ closedBall (0 : ℂ) ρ := hsphsub hy₀s
    have hbB : b ∈ cellVertices (εk k) η (closedBall 0 ρ) :=
      show (cell (εk k) η b ∩ closedBall 0 ρ).Nonempty from ⟨y₀, hy₀b, hy₀B⟩
    obtain ⟨xb, hxb, hvx⟩ := exists_vertexOf_eq_of_area_parametrized harea hp (hεk k) b
    have h1 := hcellsz (εk k) (hεk k) hεk₀ b hbB xb hxb
    have h2 := hcellsz (εk k) (hεk k) hεk₀ b hbB y₀ hy₀b
    have hy₀n := hsphB y₀ hy₀s
    have hvpn : ‖vertexPoint (εk k) η b‖ ≤ ‖z‖ + r + s / 4 := by
      have h := norm_sub_norm_le (vertexPoint (εk k) η b) y₀
      rw [norm_sub_rev] at h
      linarith
    have hxbn : ‖xb‖ ≤ ‖z‖ + r + s / 2 := by
      have h := norm_sub_norm_le xb (vertexPoint (εk k) η b)
      linarith
    have hxbB : xb ∈ closedBall (0 : ℂ) ρ := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have hvpB' : vertexPoint (εk k) η b ∈ closedBall (0 : ℂ) (ρ - d / 2) := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have hvpB : vertexPoint (εk k) η b ∈ closedBall (0 : ℂ) ρ :=
      closedBall_subset_closedBall (by linarith) hvpB'
    have hU := hunifk xb hxbB
    rw [hvx, Real.dist_eq, abs_lt] at hU
    have hc := hη₁v xb hxbB _ hvpB (by rw [dist_eq_norm]; linarith)
    rw [Real.dist_eq, abs_lt] at hc
    have ha := abs_le.1 (happrox _ hvpB')
    linarith [ha.1, ha.2, hc.1, hc.2, hU.1, hU.2]
  have hfin := le_of_tendsto_of_tendsto hlimL (hlimD.add_const (3 * δ₀)) hev
  have hφavg : ∑ p ∈ hatIndex N, v (hatPoint n p.1 p.2) * circleAverage (hat n p.1 p.2) z r =
      circleAverage φ z r := by
    rw [hφ, circleAverage_sum_mul_hat]
  have hCIv : CircleIntegrable v z r := (hv.mono hsphsub).circleIntegrable hr.le
  have hCIc : CircleIntegrable (fun _ => δ₀) z r := continuousOn_const.circleIntegrable hr.le
  have hCIφ : CircleIntegrable φ z r := by
    rw [hφ]
    exact (continuous_finsetSum _ fun p _ =>
      continuous_const.mul (continuous_hat n p.1 p.2)).continuousOn.circleIntegrable'
  have hφle : circleAverage φ z r ≤ circleAverage v z r + δ₀ := by
    calc circleAverage φ z r ≤ circleAverage (fun x => v x + δ₀) z r :=
          circleAverage_mono hCIφ (((hv.mono hsphsub).add continuousOn_const).circleIntegrable hr.le)
            fun x hx => by
              rw [abs_of_pos hr] at hx
              have hxB : x ∈ closedBall (0 : ℂ) (ρ - d / 2) := by
                rw [mem_closedBall, dist_zero_right]; linarith [hsphB x hx]
              linarith [(abs_le.1 (happrox x hxB)).1]
      _ = circleAverage v z r + δ₀ := by rw [circleAverage_fun_add hCIv hCIc, circleAverage_const]
  rw [hφavg] at hfin
  linarith

end MatedCRT
