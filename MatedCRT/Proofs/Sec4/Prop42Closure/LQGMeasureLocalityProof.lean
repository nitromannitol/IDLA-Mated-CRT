import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureFunctional
import MatedCRT.LPStaging.Analysis.DyadicMeshGeometry

/-!
# Local-measure functional: a proof of `LQGMeasureLocalityFunctionalStep`

The Step is the open input (A) of `LQGMeasureFunctional.lean:42`.

Route:
* dyadic cutoffs `f_j(z) = min {1, max {0, j·dist(z, Uᶜ) − 1}}`: continuous, `[0,1]`-valued, increasing in `j`, with
  `f_j ↑ 1_U` (`lqCutoff`);
* grid Riemann sums `R_{j,n,k}` over the `2^k × 2^k` grid of `[-2,2)²`, weights `16/4^k`, sample points the lower-left
  corners, admissibility `r_n + |z_Q| < 1` (`lqRiemann`);
* `I_{j,n} = liminf_k R_{j,n,k}` and `Λ = sup_j liminf_n I_{j,n}` (`lqInner`, `lqFunctional`). `Λ` reads only the
  circle coordinates, and it is measurable on the raw product space (`Measurable.liminf`, `Measurable.iSup`).

Deterministic identity (`lqFunctional_eq`): for a total circle array `c`, continuous in `z` at each radius `r > 0`, and a
vague limit `m` of the dyadic approximations (`IsLQGLimit γ c m`), `Λ(c restricted to B_1) = m(U)`. The Riemann sums
converge to the integral (`tendsto_lqRiemann_grid`, dominated convergence over the grid cells).

Both models supply the hypotheses: the cone by `IsQuantumCone.ae_continuousOn_circle`; the whole-plane model by
`IsWholePlaneGFF.ae_continuousOn_circle` and the Mathlib closed form `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`
of the logarithmic circle average. No literature input is used and no hypothesis is strengthened. -/

namespace MatedCRT

namespace LQGLocality

open MeasureTheory Filter Set Metric Topology HarmonicBalls
open scoped ENNReal

/-! ### 1. Dyadic cutoffs -/

/-- The cutoff `f_j(z) = min {1, max {0, j·dist(z, Uᶜ) − 1}}`. -/
noncomputable def lqCutoff (U : Set ℂ) (j : ℕ) (z : ℂ) : ℝ :=
  min 1 (max 0 ((j : ℝ) * infDist z Uᶜ - 1))

lemma lqCutoff_nonneg (U : Set ℂ) (j : ℕ) (z : ℂ) : 0 ≤ lqCutoff U j z :=
  le_min zero_le_one (le_max_left _ _)

lemma lqCutoff_le_one (U : Set ℂ) (j : ℕ) (z : ℂ) : lqCutoff U j z ≤ 1 :=
  min_le_left _ _

lemma lqCutoff_continuous (U : Set ℂ) (j : ℕ) : Continuous (lqCutoff U j) :=
  continuous_const.min (continuous_const.max
    ((continuous_const.mul (continuous_infDist_pt (s := Uᶜ))).sub continuous_const))

lemma lqCutoff_mono (U : Set ℂ) (z : ℂ) : Monotone fun j : ℕ => lqCutoff U j z := by
  intro i j hij
  have hd : 0 ≤ infDist z Uᶜ := infDist_nonneg
  have h1 : (i : ℝ) * infDist z Uᶜ ≤ (j : ℝ) * infDist z Uᶜ :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hd
  dsimp only [lqCutoff]
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

lemma lqCutoff_eq_zero_of_not_mem {U : Set ℂ} {z : ℂ} (hz : z ∉ U) (j : ℕ) :
    lqCutoff U j z = 0 := by
  have h0 : infDist z Uᶜ = 0 := infDist_zero_of_mem (Set.mem_compl hz)
  unfold lqCutoff
  rw [h0, mul_zero, zero_sub, max_eq_left (by norm_num : (-1 : ℝ) ≤ 0),
    min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma lqCutoff_hasCompactSupport {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) (j : ℕ) :
    HasCompactSupport (lqCutoff U j) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) (fun z hz => ?_)
  apply lqCutoff_eq_zero_of_not_mem _ j
  intro hzU
  exact hz (ball_subset_closedBall (hUsub hzU))

lemma one_lt_of_lqCutoff_ne_zero {U : Set ℂ} {j : ℕ} {z : ℂ} (h : lqCutoff U j z ≠ 0) :
    1 < (j : ℝ) * infDist z Uᶜ := by
  by_contra hle
  have hle' : (j : ℝ) * infDist z Uᶜ ≤ 1 := not_lt.mp hle
  apply h
  unfold lqCutoff
  rw [max_eq_left (show (j : ℝ) * infDist z Uᶜ - 1 ≤ 0 by linarith),
    min_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]

/-- Distance from `z` to the complement of `U ⊆ B_1` is at most `1 − |z|` (the unit sphere lies in `Uᶜ`). -/
lemma infDist_compl_le_one_sub_norm {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) {z : ℂ} (hz : ‖z‖ < 1) :
    infDist z Uᶜ ≤ 1 - ‖z‖ :=
  LatticeProb.DyadicMeshGeometry.infDist_compl_le_one_sub_norm hUsub hz

/-- If `f_j(z) ≠ 0` and `j·r ≤ 1`, then `r + |z| < 1` (the cutoff is supported in `B_{1-1/j}`). -/
lemma admissible_of_lqCutoff_ne_zero {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) {j : ℕ} {r : ℝ}
    (hjr : (j : ℝ) * r ≤ 1) {z : ℂ} (hz : lqCutoff U j z ≠ 0) : r + ‖z‖ < 1 := by
  have h1 := one_lt_of_lqCutoff_ne_zero hz
  have hnorm : ‖z‖ < 1 := by
    by_contra hge
    have hge' : 1 ≤ ‖z‖ := not_lt.mp hge
    have hzU : z ∉ U := fun hzU => by
      have h2 := mem_ball_zero_iff.mp (hUsub hzU)
      linarith
    rw [infDist_zero_of_mem (Set.mem_compl hzU), mul_zero] at h1
    linarith
  have h2 := infDist_compl_le_one_sub_norm hUsub hnorm
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h3 : 1 < (j : ℝ) * (1 - ‖z‖) := lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left h2 hj)
  by_contra hcon
  have hcon' : 1 ≤ r + ‖z‖ := not_lt.mp hcon
  have h4 : 1 - ‖z‖ ≤ r := by linarith
  have h5 : (j : ℝ) * (1 - ‖z‖) ≤ (j : ℝ) * r := mul_le_mul_of_nonneg_left h4 hj
  linarith

/-! ### 2. The dyadic grid on `[-2,2)²`, its cells, and the limit of the Riemann sums -/

/-- The left edge of the `a`-th column of the `2^k`-grid on `[-2, 2)`. -/
noncomputable def lqGx (k a : ℕ) : ℝ := -2 + 4 * (a : ℝ) / 2 ^ k

/-- The lower-left corner `z_Q` of the cell `Q = (a,b)` of the `2^k × 2^k` grid. -/
noncomputable def lqGridPoint (k a b : ℕ) : ℂ := ⟨lqGx k a, lqGx k b⟩

lemma lqGridPoint_re (k a b : ℕ) : (lqGridPoint k a b).re = lqGx k a := rfl

lemma lqGridPoint_im (k a b : ℕ) : (lqGridPoint k a b).im = lqGx k b := rfl

/-- The rectangle `[x,y) × [s,t)` of `ℂ`, as the preimage of a product of intervals. -/
def lqCell (x y s t : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Ico x y ×ˢ Ico s t)

/-- The square `[-2,2)²` containing all grid cells. -/
abbrev lqSquare : Set ℂ := lqCell (-2) 2 (-2) 2

lemma mem_lqCell {x y s t : ℝ} {z : ℂ} :
    z ∈ lqCell x y s t ↔ z.re ∈ Ico x y ∧ z.im ∈ Ico s t :=
  Iff.rfl

lemma measurableSet_lqCell (x y s t : ℝ) : MeasurableSet (lqCell x y s t) :=
  (measurableSet_Ico.prod measurableSet_Ico).preimage Complex.measurableEquivRealProd.measurable

lemma volume_lqCell (x y s t : ℝ) :
    volume (lqCell x y s t) = ENNReal.ofReal (y - x) * ENNReal.ofReal (t - s) := by
  unfold lqCell
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]

lemma lqGx_eq (k a : ℕ) : lqGx k a = -2 + (a : ℝ) * (4 / 2 ^ k) := by
  unfold lqGx
  ring

lemma lqGx_succ_sub (k a : ℕ) : lqGx k (a + 1) - lqGx k a = 4 / 2 ^ k := by
  rw [lqGx_eq, lqGx_eq]
  push_cast
  ring

lemma mesh_pos (k : ℕ) : (0 : ℝ) < 4 / 2 ^ k :=
  LatticeProb.DyadicMeshGeometry.mesh_pos k

lemma volume_lqGridCell (k a b : ℕ) :
    volume (lqCell (lqGx k a) (lqGx k (a + 1)) (lqGx k b) (lqGx k (b + 1))) =
      ENNReal.ofReal (4 / 2 ^ k) * ENNReal.ofReal (4 / 2 ^ k) := by
  rw [volume_lqCell, lqGx_succ_sub, lqGx_succ_sub]

lemma ofReal_sixteen (k : ℕ) :
    ENNReal.ofReal (16 / 4 ^ k) = ENNReal.ofReal (4 / 2 ^ k) * ENNReal.ofReal (4 / 2 ^ k) :=
  LatticeProb.DyadicMeshGeometry.ofReal_sixteen k

lemma lqGx_ge_neg_two (k a : ℕ) : -2 ≤ lqGx k a := by
  rw [lqGx_eq]
  have := mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (mesh_pos k).le
  linarith

lemma lqGx_succ_le_two {k a : ℕ} (ha : a < 2 ^ k) : lqGx k (a + 1) ≤ 2 := by
  rw [lqGx_eq]
  have hh := mesh_pos k
  have h1 : ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (show a + 1 ≤ 2 ^ k from ha)
  have h2 : (2 : ℝ) ^ k * (4 / 2 ^ k) = 4 := by field_simp
  have h3 := mul_le_mul_of_nonneg_right h1 hh.le
  rw [h2] at h3
  push_cast at h3 ⊢
  linarith

/-- The grid cell index: `t` lies in the `a`-th column iff `a = ⌊(t+2)/h_k⌋`, `h_k = 4/2^k`. -/
lemma mem_Ico_lqGx_iff {k a : ℕ} {t : ℝ} (ht : -2 ≤ t) :
    t ∈ Ico (lqGx k a) (lqGx k (a + 1)) ↔ a = ⌊(t + 2) / (4 / 2 ^ k)⌋₊ := by
  have hh := mesh_pos k
  rw [eq_comm, Nat.floor_eq_iff (show (0 : ℝ) ≤ (t + 2) / (4 / 2 ^ k) from
    div_nonneg (by linarith) hh.le), mem_Ico, lqGx_eq, lqGx_eq, le_div_iff₀ hh, div_lt_iff₀ hh]
  push_cast
  rw [add_mul, one_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

lemma lt_two_pow_of_floor {k : ℕ} {t : ℝ} (ht : t < 2) (ht' : -2 ≤ t) :
    ⌊(t + 2) / (4 / 2 ^ k)⌋₊ < 2 ^ k :=
  LatticeProb.DyadicMeshGeometry.lt_two_pow_of_floor ht ht'

lemma abs_lqGx_floor_sub_le {k : ℕ} {t : ℝ} (ht : -2 ≤ t) :
    |lqGx k ⌊(t + 2) / (4 / 2 ^ k)⌋₊ - t| ≤ 4 / 2 ^ k := by
  have hh := mesh_pos k
  have hx : (0 : ℝ) ≤ (t + 2) / (4 / 2 ^ k) := div_nonneg (by linarith) hh.le
  have h1 : ((⌊(t + 2) / (4 / 2 ^ k)⌋₊ : ℕ) : ℝ) ≤ (t + 2) / (4 / 2 ^ k) := Nat.floor_le hx
  have h2 : (t + 2) / (4 / 2 ^ k) < ((⌊(t + 2) / (4 / 2 ^ k)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [le_div_iff₀ hh] at h1
  rw [div_lt_iff₀ hh, add_mul, one_mul] at h2
  rw [lqGx_eq, abs_le]
  constructor <;> linarith

lemma tendsto_lqGridPoint_floor {z : ℂ} (hre : -2 ≤ z.re ∧ z.re < 2) (him : -2 ≤ z.im ∧ z.im < 2) :
    Tendsto (fun k : ℕ => lqGridPoint k ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊)
      atTop (𝓝 z) := by
  have hmesh : Tendsto (fun k : ℕ => 2 * (4 / (2 : ℝ) ^ k)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    have h2 := h.const_mul 2
    rw [mul_zero] at h2
    exact h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hmesh
  have hre_b := abs_lqGx_floor_sub_le (k := k) hre.1
  have him_b := abs_lqGx_floor_sub_le (k := k) him.1
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (lqGridPoint k ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊ - z)
  simp only [Complex.sub_re, Complex.sub_im, lqGridPoint_re, lqGridPoint_im] at hnorm
  have key : ‖lqGridPoint k ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊ - z‖
      ≤ 2 * (4 / 2 ^ k) := by
    linarith
  exact key

/-- A point outside the square `[-2,2)²` has norm at least one. -/
lemma one_le_norm_of_not_mem_lqSquare {z : ℂ} (hz : z ∉ lqSquare) : 1 ≤ ‖z‖ := by
  by_contra h
  have h' : ‖z‖ < 1 := not_le.mp h
  apply hz
  have hsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : |z.re| < 1 :=
    abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg z.im, norm_nonneg z]) zero_le_one
  have him : |z.im| < 1 :=
    abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg z.re, norm_nonneg z]) zero_le_one
  obtain ⟨hre1, hre2⟩ := abs_lt.mp hre
  obtain ⟨him1, him2⟩ := abs_lt.mp him
  exact mem_lqCell.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma lqCell_subset_lqSquare {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    lqCell (lqGx k a) (lqGx k (a + 1)) (lqGx k b) (lqGx k (b + 1)) ⊆ lqSquare := by
  intro z hz
  obtain ⟨hre, him⟩ := mem_lqCell.mp hz
  exact mem_lqCell.mpr ⟨⟨(lqGx_ge_neg_two k a).trans hre.1, hre.2.trans_le (lqGx_succ_le_two ha)⟩,
    ⟨(lqGx_ge_neg_two k b).trans him.1, him.2.trans_le (lqGx_succ_le_two hb)⟩⟩

/-- The step function `Σ_Q G(z_Q) 1_Q` of the grid; its integral is the Riemann sum. -/
noncomputable def lqStep (G : ℂ → ℝ) (k : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
    (lqCell (lqGx k a) (lqGx k (a + 1)) (lqGx k b) (lqGx k (b + 1))).indicator
      (fun _ => ENNReal.ofReal (G (lqGridPoint k a b))) z

lemma measurable_lqStep (G : ℂ → ℝ) (k : ℕ) : Measurable (lqStep G k) := by
  unfold lqStep
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
    measurable_const.indicator (measurableSet_lqCell _ _ _ _)

lemma lqStep_of_mem_square (G : ℂ → ℝ) {k : ℕ} {z : ℂ} (hre : -2 ≤ z.re ∧ z.re < 2)
    (him : -2 ≤ z.im ∧ z.im < 2) :
    lqStep G k z = ENNReal.ofReal
      (G (lqGridPoint k ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊)) := by
  have hcell : ∀ a b : ℕ, z ∈ lqCell (lqGx k a) (lqGx k (a + 1)) (lqGx k b) (lqGx k (b + 1)) ↔
      a = ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ∧ b = ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊ := by
    intro a b
    rw [mem_lqCell, mem_Ico_lqGx_iff hre.1, mem_Ico_lqGx_iff him.1]
  have hA : ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ∈ Finset.range (2 ^ k) :=
    Finset.mem_range.mpr (lt_two_pow_of_floor hre.2 hre.1)
  have hB : ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊ ∈ Finset.range (2 ^ k) :=
    Finset.mem_range.mpr (lt_two_pow_of_floor him.2 him.1)
  unfold lqStep
  rw [Finset.sum_eq_single ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊]
  · rw [Finset.sum_eq_single ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊]
    · exact Set.indicator_of_mem ((hcell _ _).mpr ⟨rfl, rfl⟩) _
    · intro b _ hb
      exact Set.indicator_of_notMem (fun h => hb ((hcell _ _).mp h).2) _
    · intro h
      exact absurd hB h
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ =>
      Set.indicator_of_notMem (fun h => ha ((hcell _ _).mp h).1) _
  · intro h
    exact absurd hA h

lemma lqStep_of_not_mem_square (G : ℂ → ℝ) {k : ℕ} {z : ℂ} (hz : z ∉ lqSquare) :
    lqStep G k z = 0 := by
  unfold lqStep
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb =>
    Set.indicator_of_notMem ?_ _
  exact fun h => hz (lqCell_subset_lqSquare (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h)

/-- **Riemann sums on the dyadic grid.** A continuous integrand vanishing off the unit disc has grid Riemann sums
`(16/4^k) Σ_Q G(z_Q)` converging to `∫ G` (dominated convergence for the step functions). -/
theorem tendsto_lqRiemann_grid (G : ℂ → ℝ) (hG : Continuous G)
    (hG1 : ∀ z, 1 ≤ ‖z‖ → G z = 0) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (16 / 4 ^ k) *
        ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
          ENNReal.ofReal (G (lqGridPoint k a b)))
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (G z))) := by
  have hcs : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) (fun z hz => hG1 z ?_)
    rw [mem_closedBall_zero_iff, not_le] at hz
    exact hz.le
  obtain ⟨C, hC⟩ := hG.bounded_above_of_compact_support hcs
  have hGC : ∀ z, G z ≤ C := fun z =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z)
  have hint : ∀ k : ℕ, ∫⁻ z, lqStep G k z = ENNReal.ofReal (16 / 4 ^ k) *
      ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
        ENNReal.ofReal (G (lqGridPoint k a b)) := by
    intro k
    have hm : ∀ a b : ℕ, Measurable (fun z => (lqCell (lqGx k a) (lqGx k (a + 1))
        (lqGx k b) (lqGx k (b + 1))).indicator (fun _ => ENNReal.ofReal (G (lqGridPoint k a b))) z) :=
      fun a b => measurable_const.indicator (measurableSet_lqCell _ _ _ _)
    unfold lqStep
    rw [lintegral_finsetSum _ fun a _ => Finset.measurable_sum _ fun b _ => hm a b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [lintegral_finsetSum _ fun b _ => hm a b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [lintegral_indicator_const (measurableSet_lqCell _ _ _ _), volume_lqGridCell, ofReal_sixteen k]
    ring
  have hsq_meas : MeasurableSet lqSquare := measurableSet_lqCell _ _ _ _
  have hsq_vol : volume lqSquare ≠ ∞ := by
    rw [volume_lqCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound_le : ∀ k z, lqStep G k z ≤ lqSquare.indicator (fun _ => ENNReal.ofReal C) z := by
    intro k z
    by_cases hz : z ∈ lqSquare
    · obtain ⟨hre, him⟩ := mem_lqCell.mp hz
      rw [Set.indicator_of_mem hz, lqStep_of_mem_square G hre him]
      exact ENNReal.ofReal_le_ofReal (hGC _)
    · rw [lqStep_of_not_mem_square G hz, Set.indicator_of_notMem hz]
  have hlim_step : ∀ z, Tendsto (fun k => lqStep G k z) atTop (𝓝 (ENNReal.ofReal (G z))) := by
    intro z
    by_cases hz : z ∈ lqSquare
    · obtain ⟨hre, him⟩ := mem_lqCell.mp hz
      have heq : (fun k => lqStep G k z) = fun k => ENNReal.ofReal
          (G (lqGridPoint k ⌊(z.re + 2) / (4 / 2 ^ k)⌋₊ ⌊(z.im + 2) / (4 / 2 ^ k)⌋₊)) :=
        funext fun k => lqStep_of_mem_square G hre him
      rw [heq]
      exact (ENNReal.continuous_ofReal.tendsto (G z)).comp
        ((hG.tendsto z).comp (tendsto_lqGridPoint_floor hre him))
    · have hz0 : (fun k => lqStep G k z) = fun _ => 0 :=
        funext fun k => lqStep_of_not_mem_square G hz
      rw [hz0, hG1 z (one_le_norm_of_not_mem_lqSquare hz), ENNReal.ofReal_zero]
      exact tendsto_const_nhds
  have key := tendsto_lintegral_of_dominated_convergence
    (lqSquare.indicator (fun _ => ENNReal.ofReal C))
    (fun k => measurable_lqStep G k) (fun k => ae_of_all _ fun z => hbound_le k z)
    (by
      rw [lintegral_indicator_const hsq_meas]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsq_vol)
    (ae_of_all _ fun z => hlim_step z)
  simp only [hint] at key
  exact key

/-! ### 3. The functional and its measurability -/

/-- A circle `(r,z)` with `r > 0` and `r + |z| < 1` has closed disc in `B_1`. -/
lemma closedBall_subset_ball_of_add_norm_lt {r : ℝ} {z : ℂ} (h : r + ‖z‖ < 1) :
    closedBall z r ⊆ ball (0 : ℂ) 1 :=
  LatticeProb.DyadicMeshGeometry.closedBall_subset_ball_of_add_norm_lt h

/-- The value of an array on `CircleB1` at an admissible circle `(r,z)`. -/
abbrev lqCircleVal (cc : CircleB1 → ℝ) (r : ℝ) (z : ℂ) (hr : 0 < r) (h : r + ‖z‖ < 1) : ℝ :=
  cc ⟨(r, z), hr, closedBall_subset_ball_of_add_norm_lt h⟩

/-- The grid Riemann sum `R_{j,n,k}(c) = (16/4^k) Σ_{Q : r_n + |z_Q| < 1} f_j(z_Q) r_n^{γ²/2} e^{γ c(r_n, z_Q)}`, with `r_n = 2^{-n}`. Only admissible circle coordinates are read. -/
noncomputable def lqRiemann (U : Set ℂ) (γ : ℝ) (j n k : ℕ) (cc : CircleB1 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (16 / 4 ^ k) * ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
    if h : dyadicScale n + ‖lqGridPoint k a b‖ < 1 then
      ENNReal.ofReal (lqCutoff U j (lqGridPoint k a b) * dyadicScale n ^ (γ ^ 2 / 2) *
        Real.exp (γ * lqCircleVal cc (dyadicScale n) (lqGridPoint k a b) (dyadicScale_pos n) h))
    else 0

/-- `I_{j,n}(c) = liminf_k R_{j,n,k}(c)`. -/
noncomputable def lqInner (U : Set ℂ) (γ : ℝ) (j n : ℕ) (cc : CircleB1 → ℝ) : ℝ≥0∞ :=
  liminf (fun k => lqRiemann U γ j n k cc) atTop

/-- The local-measure functional `Λ_{γ,U}(c) = sup_j liminf_n I_{j,n}(c)`. It is an everywhere
defined map on the raw array space; it ignores the test-pairing coordinate. -/
noncomputable def lqFunctional (U : Set ℂ) (γ : ℝ) (cc : CircleB1 → ℝ) : ℝ≥0∞ :=
  ⨆ j : ℕ, liminf (fun n => lqInner U γ j n cc) atTop

lemma measurable_dite_fixed {P : Prop} [Decidable P] {g : P → (CircleB1 → ℝ) → ℝ≥0∞}
    (hg : ∀ h : P, Measurable (g h)) : Measurable fun cc => if h : P then g h cc else 0 := by
  by_cases hP : P
  · simp only [hP, ↓reduceDIte]
    exact hg hP
  · simp only [hP, ↓reduceDIte]
    exact measurable_const

lemma measurable_lqRiemann (U : Set ℂ) (γ : ℝ) (j n k : ℕ) : Measurable (lqRiemann U γ j n k) := by
  unfold lqRiemann
  refine measurable_const.mul
    (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine measurable_dite_fixed fun h => ?_
  have hev : Measurable fun cc : CircleB1 → ℝ =>
      lqCircleVal cc (dyadicScale n) (lqGridPoint k a b) (dyadicScale_pos n) h :=
    measurable_pi_apply _
  exact (((hev.const_mul γ).exp).const_mul _).ennreal_ofReal

lemma measurable_lqInner (U : Set ℂ) (γ : ℝ) (j n : ℕ) : Measurable (lqInner U γ j n) :=
  Measurable.liminf fun k => measurable_lqRiemann U γ j n k

lemma measurable_lqFunctional (U : Set ℂ) (γ : ℝ) : Measurable (lqFunctional U γ) :=
  Measurable.iSup fun j => Measurable.liminf fun n => measurable_lqInner U γ j n

/-! ### 4. The deterministic identity `Λ = μ(U)` -/

/-- The integrand `f_j(z) r_n^{γ²/2} e^{γ c(r_n, z)}` of the `n`-th approximation. -/
noncomputable def lqIntegrand (U : Set ℂ) (γ : ℝ) (j n : ℕ) (c : ℝ → ℂ → ℝ) (z : ℂ) : ℝ :=
  lqCutoff U j z * dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * c (dyadicScale n) z)

lemma lqIntegrand_continuous (U : Set ℂ) (γ : ℝ) (j n : ℕ) {c : ℝ → ℂ → ℝ}
    (hc : ∀ r : ℝ, 0 < r → Continuous fun z => c r z) : Continuous (lqIntegrand U γ j n c) := by
  unfold lqIntegrand
  exact ((lqCutoff_continuous U j).mul continuous_const).mul
    (Real.continuous_exp.comp (continuous_const.mul (hc _ (dyadicScale_pos n))))

lemma lqIntegrand_eq_zero_of_one_le_norm {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) (γ : ℝ) (j n : ℕ)
    (c : ℝ → ℂ → ℝ) {z : ℂ} (hz : 1 ≤ ‖z‖) : lqIntegrand U γ j n c z = 0 := by
  have hzU : z ∉ U := fun h => by
    have h2 := mem_ball_zero_iff.mp (hUsub h)
    linarith
  unfold lqIntegrand
  rw [lqCutoff_eq_zero_of_not_mem hzU, zero_mul, zero_mul]

/-- The Riemann sum of the array equals the grid sum of the integrand, once `j r_n ≤ 1`: a sample point with
`f_j ≠ 0` is admissible, and the other terms vanish on both sides. -/
lemma lqRiemann_eq_integrand {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) (γ : ℝ) (c : ℝ → ℂ → ℝ)
    {j n : ℕ} (hjn : (j : ℝ) * dyadicScale n ≤ 1) (k : ℕ) :
    lqRiemann U γ j n k (fun p => c p.1.1 p.1.2) =
      ENNReal.ofReal (16 / 4 ^ k) * ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
        ENNReal.ofReal (lqIntegrand U γ j n c (lqGridPoint k a b)) := by
  unfold lqRiemann
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : dyadicScale n + ‖lqGridPoint k a b‖ < 1
  · simp only [h, ↓reduceDIte]
    rfl
  · simp only [h, ↓reduceDIte]
    have hcut : lqCutoff U j (lqGridPoint k a b) = 0 := by
      by_contra hne
      exact h (admissible_of_lqCutoff_ne_zero hUsub hjn hne)
    simp [lqIntegrand, hcut]

/-- The inner liminf is the integral of `f_j` against the `n`-th dyadic approximation, once `j r_n ≤ 1`. -/
lemma lqInner_eq_lqg {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) (γ : ℝ) (c : ℝ → ℂ → ℝ)
    (hc : ∀ r : ℝ, 0 < r → Continuous fun z => c r z) (j n : ℕ)
    (hjn : (j : ℝ) * dyadicScale n ≤ 1) :
    lqInner U γ j n (fun p => c p.1.1 p.1.2) =
      ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂(lqgApprox γ c (dyadicScale n)) := by
  have hr : 0 < dyadicScale n := dyadicScale_pos n
  have hriem := tendsto_lqRiemann_grid (lqIntegrand U γ j n c) (lqIntegrand_continuous U γ j n hc)
    (fun z hz => lqIntegrand_eq_zero_of_one_le_norm hUsub γ j n c hz)
  unfold lqInner
  rw [funext (lqRiemann_eq_integrand hUsub γ c hjn), hriem.liminf_eq]
  have hf : Measurable fun z =>
      ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * c (dyadicScale n) z)) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc _ hr)))).measurable.ennreal_ofReal
  have hg : Measurable fun z => ENNReal.ofReal (lqCutoff U j z) :=
    (lqCutoff_continuous U j).measurable.ennreal_ofReal
  unfold lqgApprox
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
  refine lintegral_congr fun z => ?_
  show ENNReal.ofReal (lqIntegrand U γ j n c z) = ENNReal.ofReal
      (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * c (dyadicScale n) z)) * ENNReal.ofReal (lqCutoff U j z)
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le)]
  congr 1
  unfold lqIntegrand
  ring

/-- The dyadic approximations of `f_j` converge to `∫ f_j dm`, in the lower-integral form. -/
lemma tendsto_lintegral_lqCutoff {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) (γ : ℝ) (c : ℝ → ℂ → ℝ)
    (hc : ∀ r : ℝ, 0 < r → Continuous fun z => c r z) (m : Measure ℂ) (hm : IsLQGLimit γ c m)
    (j : ℕ) :
    Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂(lqgApprox γ c (dyadicScale n)))
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂m)) := by
  have := hm.isLocallyFiniteMeasure
  have hf : Continuous (lqCutoff U j) := lqCutoff_continuous U j
  have hcs : HasCompactSupport (lqCutoff U j) := lqCutoff_hasCompactSupport hUsub j
  have hT := hm.tendsto_integral (lqCutoff U j) hf hcs
  have hint_m : Integrable (lqCutoff U j) m := hf.integrable_of_hasCompactSupport hcs
  have hint_n : ∀ n : ℕ, Integrable (lqCutoff U j) (lqgApprox γ c (dyadicScale n)) := by
    intro n
    have hr : 0 < dyadicScale n := dyadicScale_pos n
    have hdens : Continuous fun z =>
        dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * c (dyadicScale n) z) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc _ hr)))
    have : IsLocallyFiniteMeasure (lqgApprox γ c (dyadicScale n)) := by
      unfold lqgApprox
      exact IsLocallyFiniteMeasure.withDensity_ofReal hdens
    exact hf.integrable_of_hasCompactSupport hcs
  have e_n : ∀ n : ℕ, ENNReal.ofReal (∫ z, lqCutoff U j z ∂(lqgApprox γ c (dyadicScale n))) =
      ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂(lqgApprox γ c (dyadicScale n)) :=
    fun n => ofReal_integral_eq_lintegral_ofReal (hint_n n) (ae_of_all _ fun z => lqCutoff_nonneg U j z)
  have e_m : ENNReal.ofReal (∫ z, lqCutoff U j z ∂m) = ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂m :=
    ofReal_integral_eq_lintegral_ofReal hint_m (ae_of_all _ fun z => lqCutoff_nonneg U j z)
  rw [← e_m]
  simp only [← e_n]
  exact ENNReal.tendsto_ofReal hT

/-- Pointwise: the supremum over `j` of the cutoffs is the indicator of `U` (`f_j ↑ 1_U`). -/
lemma iSup_ofReal_lqCutoff {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1) (z : ℂ) :
    (⨆ j : ℕ, ENNReal.ofReal (lqCutoff U j z)) = U.indicator 1 z := by
  by_cases hzU : z ∈ U
  · rw [Set.indicator_of_mem hzU, Pi.one_apply]
    have hne : Uᶜ.Nonempty := ⟨1, fun h1 => by
      have := mem_ball_zero_iff.mp (hUsub h1)
      simp at this⟩
    have hd : 0 < infDist z Uᶜ := by
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hzU
      by_contra hle
      have hle' : infDist z Uᶜ ≤ 0 := not_lt.mp hle
      obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hne).mp (lt_of_le_of_lt hle' hε)
      exact hy (hball (mem_ball.mpr (by rw [dist_comm]; exact hdy)))
    obtain ⟨j, hj⟩ := exists_nat_gt (2 / infDist z Uᶜ)
    refine le_antisymm (iSup_le fun i => ENNReal.ofReal_le_one.mpr (lqCutoff_le_one U i z)) ?_
    refine le_iSup_of_le j (le_of_eq ?_)
    have h2 : 2 < (j : ℝ) * infDist z Uᶜ := (div_lt_iff₀ hd).mp hj
    have h1 : lqCutoff U j z = 1 := by
      unfold lqCutoff
      exact min_eq_left (le_max_of_le_right (by linarith))
    rw [h1, ENNReal.ofReal_one]
  · rw [Set.indicator_of_notMem hzU]
    simp [lqCutoff_eq_zero_of_not_mem hzU]

/-- `sup_j ∫ f_j dm = m(U)` by monotone convergence (`f_j ↑ 1_U`). -/
lemma lintegral_iSup_lqCutoff {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1) (m : Measure ℂ) :
    (⨆ j : ℕ, ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂m) = m U := by
  rw [← lintegral_iSup (fun j => (lqCutoff_continuous U j).measurable.ennreal_ofReal)
    (by
      intro i j hij z
      exact ENNReal.ofReal_le_ofReal (lqCutoff_mono U z hij))]
  simp_rw [iSup_ofReal_lqCutoff hU hUsub]
  exact lintegral_indicator_one hU.measurableSet

/-- **Deterministic identity.** For a total circle array `c`, continuous in `z` at each radius `r > 0`, and a vague
limit `m` of its dyadic approximations, the functional of the restricted array equals `m(U)`. -/
theorem lqFunctional_eq {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1) (γ : ℝ)
    (c : ℝ → ℂ → ℝ) (hc : ∀ r : ℝ, 0 < r → Continuous fun z => c r z) (m : Measure ℂ)
    (hm : IsLQGLimit γ c m) :
    lqFunctional U γ (fun p => c p.1.1 p.1.2) = m U := by
  unfold lqFunctional
  have hj : ∀ j : ℕ, liminf (fun n => lqInner U γ j n (fun p => c p.1.1 p.1.2)) atTop =
      ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂m := by
    intro j
    have hlim : Tendsto (fun n : ℕ => (j : ℝ) * dyadicScale n) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul (j : ℝ)
      rw [mul_zero] at h
      exact h
    have hev : ∀ᶠ n in atTop, lqInner U γ j n (fun p => c p.1.1 p.1.2) =
        ∫⁻ z, ENNReal.ofReal (lqCutoff U j z) ∂(lqgApprox γ c (dyadicScale n)) := by
      filter_upwards [hlim.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
      exact lqInner_eq_lqg hUsub γ c hc j n hn
    rw [liminf_congr hev]
    exact (tendsto_lintegral_lqCutoff hUsub γ c hc m hm j).liminf_eq
  simp only [hj]
  exact lintegral_iSup_lqCutoff hU hUsub m

/-! ### 5. The two models -/

/-- A joint circle function continuous on `(0,∞) × ℂ` is continuous in `z` at each positive radius. -/
lemma slice_continuous_of_continuousOn {c : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ∀ r : ℝ, 0 < r → Continuous fun z => c r z :=
  LatticeProb.DyadicMeshGeometry.slice_continuous_of_continuousOn hcont

/-- The whole-plane circle average `h_r(z) − γ·avg_{∂B_r(z)} log|·|` is continuous in `z` at each radius `r > 0`,
by the closed form `avg_{∂B_r(z)} log|·| = log r + log⁺(|z|/r)` (Mathlib `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). -/
lemma fieldCircleAverage_slice_continuous (γ : ℝ) {h : ℝ → ℂ → ℝ}
    (hcont : ∀ r : ℝ, 0 < r → Continuous fun z => h r z) :
    ∀ r : ℝ, 0 < r → Continuous fun z => fieldCircleAverage γ h r z := by
  intro r hr
  have hlog : ∀ z : ℂ, Real.circleAverage (fun x => Real.log ‖x‖) z r =
      Real.log r + Real.posLog (r⁻¹ * ‖z‖) := by
    intro z
    have key := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := 0) (c := z) (R := r)
      hr.ne'
    simp only [sub_zero] at key
    exact key
  have hfun : (fun z => fieldCircleAverage γ h r z) =
      fun z => h r z - γ * (Real.log r + Real.posLog (r⁻¹ * ‖z‖)) := by
    funext z
    unfold fieldCircleAverage
    rw [hlog z]
  rw [hfun]
  exact (hcont r hr).sub (continuous_const.mul (continuous_const.add
    (Real.continuous_posLog.comp (continuous_const.mul continuous_norm))))

end LQGLocality

open LQGLocality HarmonicBalls MeasureTheory Filter Set in
/-- **Proof of the locality input `LQGMeasureLocalityFunctionalStep`** (open input (A) of
`LQGMeasureFunctional.lean`). For `γ > 0` and open `U ⊆ B_1` one measurable functional `Λ` of the restricted field
gives `μ(U)` almost surely, for the cone field and for the whole-plane field with its `γ`-LQG measure. -/
theorem LQGMeasureLocalityFunctionalStep_proof : LQGMeasureLocalityFunctionalStep := by
  unfold LQGMeasureLocalityFunctionalStep
  intro γ _ _ U hU hUsub
  refine ⟨fun x => lqFunctional U γ x.2, (measurable_lqFunctional U γ).comp measurable_snd, ?_, ?_⟩
  · intro Ω _ P hC hcirc μ hcone
    obtain ⟨_, hQC, hLQG⟩ := hcone
    have hLQG' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hLQG
    filter_upwards [hQC.ae_continuousOn_circle, hLQG'] with ω hcont hlqg
    exact (lqFunctional_eq hU hUsub γ (hcirc ω) (slice_continuous_of_continuousOn hcont) (μ ω) hlqg).symm
  · intro Ω' _ P' hC' hcirc' μ' _ hWP hLQG
    have hLQG' : ∀ᵐ ω ∂P', IsLQGLimit γ (fieldCircleAverage γ (hcirc' ω)) (μ' ω) := hLQG
    filter_upwards [hWP.ae_continuousOn_circle, hLQG'] with ω hcont hlqg
    exact (lqFunctional_eq hU hUsub γ (fieldCircleAverage γ (hcirc' ω))
      (fieldCircleAverage_slice_continuous γ (slice_continuous_of_continuousOn hcont)) (μ' ω) hlqg).symm

end MatedCRT
