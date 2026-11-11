import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity
import MatedCRT.FirstPass.S3t.CellGeometry

/-!
# Pathwise Riemann-sum estimate for the truncated quenched occupation (Step 10)

Deterministic comparison of the discrete quenched occupation `m⁻¹ ∑_{k<⌊Tm⌋} 1{q_0..q_k ∈ I_ε(D)} g(η(εq_k))` with the
continuum stopped occupation `∫_{(0, T ∧ τ_D]} g(W_t) dt` of the interpolated walk `W = interpolatedWalk ε η m q`
(`τ_D` the exit time of `D = ball z r`, Armitage-Gardiner terminology). The bound proved is
`T C (2d)^χ + M/m + M · shellTime`, which implies the stated `T C (2d)^χ + 4 M/m + M · shellTime`.
-/

open Set Metric Filter MeasureTheory Topology Finset
open scoped NNReal ENNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

variable {ε mε : ℝ} {η : ℝ → ℂ} {q : ℕ → ℤ}

/-! ### Exit-time helpers (`pathExitTime U f = sInf {t | f t ∉ U}`) -/

lemma mem_of_lt_pathExitTime {U : Set ℂ} {f : ℝ≥0 → ℂ} {t : ℝ≥0}
    (h : (t : ℝ≥0∞) < pathExitTime U f) : f t ∈ U := by
  by_contra hf
  have hle : pathExitTime U f ≤ t := sInf_le (show (t : ℝ≥0∞) ∈ {s : ℝ≥0∞ | ∃ t' : ℝ≥0, s = (t' : ℝ≥0∞) ∧ f t' ∉ U}
    from ⟨t, rfl, hf⟩)
  exact absurd hle (not_le.2 h)

lemma le_pathExitTime_of_forall_mem_riemann {U : Set ℂ} {f : ℝ≥0 → ℂ} {a : ℝ}
    (h : ∀ t : ℝ≥0, (t : ℝ) ≤ a → f t ∈ U) : ENNReal.ofReal a ≤ pathExitTime U f := by
  refine le_sInf ?_
  rintro _ ⟨t, rfl, hf⟩
  rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
  by_contra hlt
  rw [not_le] at hlt
  exact hf (h t hlt.le)

lemma pathExitTime_mono {f : ℝ≥0 → ℂ} {U V : Set ℂ} (hUV : U ⊆ V) :
    pathExitTime U f ≤ pathExitTime V f := by
  unfold pathExitTime
  refine sInf_le_sInf ?_
  rintro _ ⟨t, rfl, hf⟩
  exact ⟨t, rfl, fun hv => hf (hUV hv)⟩

/-! ### Affine form of the interpolated walk on a grid segment -/

lemma interpolatedWalk_segment (hm : 0 < mε) (k : ℕ) {u : ℝ}
    (hu0 : (k : ℝ) / mε ≤ u) (hu1 : u ≤ ((k : ℝ) + 1) / mε) :
    interpolatedWalk ε η mε q u.toNNReal =
      vertexPoint ε η (q k) +
        ((mε * u - k : ℝ) : ℂ) * (vertexPoint ε η (q (k + 1)) - vertexPoint ε η (q k)) := by
  have hu : 0 ≤ u := le_trans (div_nonneg (Nat.cast_nonneg k) hm.le) hu0
  have hk : (k : ℝ) ≤ mε * u := by
    have := mul_le_mul_of_nonneg_left hu0 hm.le
    rwa [mul_div_cancel₀ _ hm.ne'] at this
  have hk1 : mε * u ≤ (k : ℝ) + 1 := by
    have := mul_le_mul_of_nonneg_left hu1 hm.le
    rwa [mul_div_cancel₀ _ hm.ne'] at this
  have hcast : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu
  rcases eq_or_lt_of_le hk1 with h | h
  · have hfl : ⌊mε * ((u.toNNReal : ℝ≥0) : ℝ)⌋₊ = k + 1 := by
      rw [hcast, h]
      have := Nat.floor_natCast (R := ℝ) (k + 1)
      push_cast at this ⊢
      exact this
    simp only [interpolatedWalk]
    rw [hfl, hcast, h]
    push_cast
    ring
  · have hfl : ⌊mε * ((u.toNNReal : ℝ≥0) : ℝ)⌋₊ = k := by
      rw [hcast, Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) hk)]
      exact ⟨hk, h⟩
    simp only [interpolatedWalk]
    rw [hfl, hcast]
    push_cast
    ring

lemma interpolatedWalk_grid (hm : 0 < mε) (k : ℕ) :
    interpolatedWalk ε η mε q ((k : ℝ) / mε).toNNReal = vertexPoint ε η (q k) := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) / mε := div_nonneg (Nat.cast_nonneg k) hm.le
  have h1 : (k : ℝ) / mε ≤ ((k : ℝ) + 1) / mε := by
    apply div_le_div_of_nonneg_right _ hm.le
    linarith
  rw [interpolatedWalk_segment hm k le_rfl h1]
  have : mε * ((k : ℝ) / mε) - k = 0 := by
    rw [mul_div_cancel₀ _ hm.ne']
    ring
  rw [this]
  simp

/-- Convex combinations `A + θ(B - A)`, `θ ∈ [0,1]`, of two points of a disk stay in the disk. -/
lemma segment_mem_ball {z : ℂ} {r : ℝ} {A B : ℂ} (hA : A ∈ ball z r) (hB : B ∈ ball z r) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : A + (θ : ℂ) * (B - A) ∈ ball z r := by
  have key := (convex_ball z r) hA hB (sub_nonneg.2 h1) h0 (by ring)
  convert key using 1
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- Walk stays in the disk on `[0, L/m]` when all vertices `q 0, …, q L` are interior (`vp ∈ D`). -/
lemma walk_mem_ball_of_le (hm : 0 < mε) {z : ℂ} {r : ℝ} (L : ℕ)
    (hint : ∀ j ≤ L, vertexPoint ε η (q j) ∈ ball z r) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ (L : ℝ) / mε → interpolatedWalk ε η mε q t ∈ ball z r := by
  induction L with
  | zero =>
    intro t ht
    have ht0 : (t : ℝ) = 0 := le_antisymm (by simpa using ht) t.2
    have : t = 0 := by exact_mod_cast ht0
    subst this
    have := interpolatedWalk_grid (ε := ε) (η := η) (q := q) hm 0
    simp only [Nat.cast_zero, zero_div, Real.toNNReal_zero] at this
    rw [this]
    exact hint 0 le_rfl
  | succ L ih =>
    intro t ht
    by_cases htL : (t : ℝ) ≤ (L : ℝ) / mε
    · exact ih (fun j hj => hint j (by omega)) t htL
    · rw [not_le] at htL
      have hu0 : (L : ℝ) / mε ≤ (t : ℝ) := htL.le
      have hu1 : (t : ℝ) ≤ ((L : ℝ) + 1) / mε := by
        have := ht
        push_cast at this
        exact this
      have hseg := interpolatedWalk_segment (ε := ε) (η := η) (q := q) hm L hu0 hu1
      have ht' : (t : ℝ≥0) = (t : ℝ).toNNReal := (Real.toNNReal_coe).symm
      have hθ0 : 0 ≤ mε * (t : ℝ) - L := by
        have h := mul_lt_mul_of_pos_left htL hm
        rw [mul_div_cancel₀ _ hm.ne'] at h
        linarith
      have hθ1 : mε * (t : ℝ) - L ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hu1 hm.le
        rw [mul_div_cancel₀ _ hm.ne'] at h
        linarith
      rw [ht', hseg]
      exact segment_mem_ball (hint L (by omega)) (hint (L + 1) le_rfl) hθ0 hθ1

/-- Hölder bound on the disk: `|g x - g y| ≤ C d^χ` when `dist x y ≤ d`. -/
lemma abs_sub_le_of_holder {C χ : ℝ≥0} {z : ℂ} {r : ℝ} {g : ℂ → ℝ} (hg : HolderOnWith C χ g (ball z r))
    {x y : ℂ} (hx : x ∈ ball z r) (hy : y ∈ ball z r) {d : ℝ} (hd : dist x y ≤ d) :
    |g x - g y| ≤ C * d ^ (χ : ℝ) := by
  have h := hg.dist_le_of_le hx hy hd
  rwa [Real.dist_eq] at h

/-- Integrability of `t ↦ g(W t)` on `[a, b]` when the walk stays in the disk on `(a, b)` (`g` is continuous on the
disk by the Hölder hypothesis, `|g| ≤ M`, and `W` is continuous). -/
lemma intervalIntegrable_g_walk {C χ : ℝ≥0} {z : ℂ} {r M : ℝ} {g : ℂ → ℝ}
    (hg : HolderOnWith C χ g (ball z r)) (hχ : 0 < χ) (hM : ∀ x, |g x| ≤ M) {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ t : ℝ, a < t → t < b → interpolatedWalk ε η mε q t.toNNReal ∈ ball z r) :
    IntervalIntegrable (fun t : ℝ => g (interpolatedWalk ε η mε q t.toNNReal)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  have hW : Continuous (fun t : ℝ => interpolatedWalk ε η mε q t.toNNReal) :=
    (continuous_interpolatedWalk ε mε η q).comp continuous_real_toNNReal
  have hcont : ContinuousOn (fun t : ℝ => g (interpolatedWalk ε η mε q t.toNNReal)) (Ioo a b) :=
    (hg.continuousOn hχ).comp hW.continuousOn (fun t ht => hmem t ht.1 ht.2)
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  refine Integrable.of_bound (hcont.aestronglyMeasurable measurableSet_Ioo) M ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t _ => ?_)
  rw [Real.norm_eq_abs]
  exact hM _

/-- One grid segment `[k/m, c]`, `c ≤ (k+1)/m`: the integral of `g ∘ W` differs from `(c - k/m) g(η(εq_k))` by at most
`(c - k/m) C d^χ`, when the walk stays in the disk on `(k/m, c]` and `dist(η(εq_k), η(εq_{k+1})) ≤ e`. -/
lemma abs_integral_sub_le_of_segment {C χ : ℝ≥0} {z : ℂ} {r M : ℝ} {g : ℂ → ℝ}
    (hg : HolderOnWith C χ g (ball z r)) (hχ : 0 < χ) (hM : ∀ x, |g x| ≤ M) (hm : 0 < mε) {k : ℕ} {c e : ℝ}
    (hc0 : (k : ℝ) / mε ≤ c) (hc1 : c ≤ ((k : ℝ) + 1) / mε)
    (hA : vertexPoint ε η (q k) ∈ ball z r)
    (hdist : dist (vertexPoint ε η (q k)) (vertexPoint ε η (q (k + 1))) ≤ e)
    (hmemW : ∀ t : ℝ, (k : ℝ) / mε < t → t < c → interpolatedWalk ε η mε q t.toNNReal ∈ ball z r) :
    |(∫ t in ((k : ℝ) / mε)..c, g (interpolatedWalk ε η mε q t.toNNReal))
        - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k))|
      ≤ (c - (k : ℝ) / mε) * (C * e ^ (χ : ℝ)) := by
  have hac : (k : ℝ) / mε ≤ c := hc0
  have hbound : ∀ t : ℝ, (k : ℝ) / mε < t → t < c →
      |g (interpolatedWalk ε η mε q t.toNNReal) - g (vertexPoint ε η (q k))| ≤ C * e ^ (χ : ℝ) := by
    intro t ht0 ht1
    have hseg := interpolatedWalk_segment (ε := ε) (η := η) (q := q) hm k (u := t) ht0.le
      (le_trans ht1.le hc1)
    have hθ0 : 0 ≤ mε * t - k := by
      have h := mul_lt_mul_of_pos_left ht0 hm
      rw [mul_div_cancel₀ _ hm.ne'] at h
      linarith
    have hθ1 : mε * t - k ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (le_trans ht1.le hc1) hm.le
      rw [mul_div_cancel₀ _ hm.ne'] at h
      linarith
    have hmemt := hmemW t ht0 ht1
    refine abs_sub_le_of_holder hg hmemt hA ?_
    rw [hseg, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hθabs : |mε * t - k| ≤ 1 := abs_le.2 ⟨by linarith, hθ1⟩
    calc |mε * t - k| * ‖vertexPoint ε η (q (k + 1)) - vertexPoint ε η (q k)‖
        ≤ 1 * ‖vertexPoint ε η (q (k + 1)) - vertexPoint ε η (q k)‖ :=
          mul_le_mul_of_nonneg_right hθabs (norm_nonneg _)
      _ = dist (vertexPoint ε η (q k)) (vertexPoint ε η (q (k + 1))) := by
          rw [one_mul, dist_eq_norm, norm_sub_rev]
      _ ≤ e := hdist
  have hint : IntervalIntegrable (fun t : ℝ => g (interpolatedWalk ε η mε q t.toNNReal))
      volume ((k : ℝ) / mε) c := by
    exact intervalIntegrable_g_walk hg hχ hM hac (fun t h1 h2 => hmemW t h1 h2)
  have hEq : (∫ t in ((k : ℝ) / mε)..c, g (interpolatedWalk ε η mε q t.toNNReal))
      - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k))
      = ∫ t in ((k : ℝ) / mε)..c, (g (interpolatedWalk ε η mε q t.toNNReal) - g (vertexPoint ε η (q k))) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  rw [hEq]
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
    refine ae_iff.2 ?_
    simp
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc ((k : ℝ) / mε) c →
      ‖g (interpolatedWalk ε η mε q t.toNNReal) - g (vertexPoint ε η (q k))‖ ≤ C * e ^ (χ : ℝ) := by
    filter_upwards [hne] with t htc htI
    rw [Set.uIoc_of_le hac] at htI
    rw [Real.norm_eq_abs]
    exact hbound t htI.1 (lt_of_le_of_ne htI.2 htc)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hac)] at hnorm
  linarith [hnorm, mul_comm (C * e ^ (χ : ℝ)) (c - (k : ℝ) / mε)]

/-- Riemann sums over the grid: `m⁻¹ ∑_{k<L} g(η(εq_k))` against `∫_0^{L/m} g(W)`, error `L · m⁻¹ C e^χ`. -/
lemma abs_sum_sub_integral_le {C χ : ℝ≥0} {z : ℂ} {r M : ℝ} {g : ℂ → ℝ}
    (hg : HolderOnWith C χ g (ball z r)) (hχ : 0 < χ) (hM : ∀ x, |g x| ≤ M) (hm : 0 < mε) {e : ℝ} (L : ℕ)
    (hint : ∀ j ≤ L, vertexPoint ε η (q j) ∈ ball z r)
    (hdist : ∀ j < L, dist (vertexPoint ε η (q j)) (vertexPoint ε η (q (j + 1))) ≤ e) :
    |mε⁻¹ * (∑ k ∈ range L, g (vertexPoint ε η (q k)))
        - ∫ t in (0 : ℝ)..((L : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal)|
      ≤ (L : ℝ) * (mε⁻¹ * (C * e ^ (χ : ℝ))) := by
  have hseg : ∀ k < L, ∀ t : ℝ, (k : ℝ) / mε < t → t < ((k : ℝ) + 1) / mε →
      interpolatedWalk ε η mε q t.toNNReal ∈ ball z r := by
    intro k hk t h1 h2
    have hθ0 : 0 ≤ mε * t - k := by
      have h := mul_lt_mul_of_pos_left h1 hm
      rw [mul_div_cancel₀ _ hm.ne'] at h
      linarith
    have hθ1 : mε * t - k ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left h2.le hm.le
      rw [mul_div_cancel₀ _ hm.ne'] at h
      linarith
    rw [interpolatedWalk_segment hm k h1.le h2.le]
    exact segment_mem_ball (hint k hk.le) (hint (k + 1) hk) hθ0 hθ1
  have hiv : ∀ k < L, IntervalIntegrable (fun t : ℝ => g (interpolatedWalk ε η mε q t.toNNReal)) volume
      ((k : ℝ) / mε) (((k + 1 : ℕ) : ℝ) / mε) := by
    intro k hk
    have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hk1]
    exact intervalIntegrable_g_walk hg hχ hM (div_le_div_of_nonneg_right (by linarith) hm.le)
      (fun t h1 h2 => hseg k hk t h1 h2)
  have hsplit : ∫ t in (0 : ℝ)..((L : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal)
      = ∑ k ∈ range L, ∫ t in ((k : ℝ) / mε)..(((k + 1 : ℕ) : ℝ) / mε),
          g (interpolatedWalk ε η mε q t.toNNReal) := by
    have key := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t : ℝ => g (interpolatedWalk ε η mε q t.toNNReal)) (a := fun k : ℕ => (k : ℝ) / mε)
      (n := L) hiv
    simp only [Nat.cast_zero, zero_div] at key
    exact key.symm
  have hterm : ∀ k ∈ range L, |mε⁻¹ * g (vertexPoint ε η (q k))
      - ∫ t in ((k : ℝ) / mε)..(((k + 1 : ℕ) : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal)|
      ≤ mε⁻¹ * (C * e ^ (χ : ℝ)) := by
    intro k hk
    have hk' : k < L := Finset.mem_range.1 hk
    have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hk1]
    have h := abs_integral_sub_le_of_segment hg hχ hM hm (k := k) (c := ((k : ℝ) + 1) / mε) (e := e)
      (div_le_div_of_nonneg_right (by linarith) hm.le) le_rfl (hint k hk'.le) (hdist k hk')
      (fun t h1 h2 => hseg k hk' t h1 h2)
    have hlen : ((k : ℝ) + 1) / mε - (k : ℝ) / mε = mε⁻¹ := by
      rw [← sub_div]
      ring
    rw [hlen] at h
    rw [abs_sub_comm]
    exact h
  have hrw : mε⁻¹ * (∑ k ∈ range L, g (vertexPoint ε η (q k)))
      - ∫ t in (0 : ℝ)..((L : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal)
      = ∑ k ∈ range L, (mε⁻¹ * g (vertexPoint ε η (q k))
        - ∫ t in ((k : ℝ) / mε)..(((k + 1 : ℕ) : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal)) := by
    rw [hsplit, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hrw]
  calc |∑ k ∈ range L, (mε⁻¹ * g (vertexPoint ε η (q k))
        - ∫ t in ((k : ℝ) / mε)..(((k + 1 : ℕ) : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal))|
      ≤ ∑ k ∈ range L, |mε⁻¹ * g (vertexPoint ε η (q k))
        - ∫ t in ((k : ℝ) / mε)..(((k + 1 : ℕ) : ℝ) / mε), g (interpolatedWalk ε η mε q t.toNNReal)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range L, mε⁻¹ * (C * e ^ (χ : ℝ)) := Finset.sum_le_sum hterm
    _ = (L : ℝ) * (mε⁻¹ * (C * e ^ (χ : ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


open Classical in
/-- Step 10 (pathwise Riemann-sum estimate). On a deterministic configuration of the walk `q` (vertices of the first
`⌊Tm⌋` steps have cells of diameter at most `d`, consecutive cells meet), the discrete quenched occupation
`m⁻¹ ∑_{k<⌊Tm⌋} 1{q_0..q_k ∈ I_ε(D)} g(η(εq_k))` and the continuum stopped occupation
`∫_{(0, T ∧ τ_D]} g(W_t) dt` of the interpolated walk `W` differ by at most
`T C (2d)^χ + 4 M/m + M · shellTime`, the shell being `D_n = ball z (r - δ)` with `2d < δ` (Hölder hypothesis
`HolderOnWith C χ g D`, `|g| ≤ M`). The bound proved is `T C (2d)^χ + M/m + M · shellTime`. -/
theorem quenched_sub_stopped_le {C χ : ℝ≥0} {z : ℂ} {r M d δ T : ℝ} {g : ℂ → ℝ}
    (hη : Continuous η) (hε : 0 < ε) (hm : 0 < mε) (hT : 0 ≤ T) (hr : 0 < r) (hd : 0 ≤ d) (hδ : 2 * d < δ)
    (hg : HolderOnWith C χ g (ball z r)) (hχ : 0 < χ) (hM : ∀ x, |g x| ≤ M)
    (hq0 : q 0 ∈ interiorCellVertices ε η (ball z r))
    (hadj : ∀ j < ⌊T * mε⌋₊, (cell ε η (q j) ∩ cell ε η (q (j + 1))).Nonempty)
    (hdiam : ∀ j ≤ ⌊T * mε⌋₊, (cell ε η (q j) ∩ ball z r).Nonempty → diam (cell ε η (q j)) ≤ d) :
    |mε⁻¹ * (∑ k ∈ range ⌊T * mε⌋₊,
        if (∀ j ≤ k, q j ∈ interiorCellVertices ε η (ball z r)) then g (vertexPoint ε η (q k)) else 0)
      - ∫ t in Ioc (0 : ℝ)
          (min (ENNReal.ofReal T) (pathExitTime (ball z r) (interpolatedWalk ε η mε q))).toReal,
          g (interpolatedWalk ε η mε q t.toNNReal)|
    ≤ T * C * (2 * d) ^ (χ : ℝ) + 4 * M * mε⁻¹
      + M * ((min (ENNReal.ofReal T) (pathExitTime (ball z r) (interpolatedWalk ε η mε q))).toReal
        - (min (ENNReal.ofReal T) (pathExitTime (ball z (r - δ)) (interpolatedWalk ε η mε q))).toReal) := by
  have hε0 : 0 ≤ ε := hε.le
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hvp : ∀ k, k ∈ interiorCellVertices ε η (ball z r) → vertexPoint ε η k ∈ ball z r :=
    fun k hk => cell_subset_of_mem_interiorCellVertices isOpen_ball hk
      (cell_isConnected_of_continuous hε0 hη k) (vertexPoint_mem_cell_of_nonneg hε0 k)
  have hmeetD : ∀ j, q j ∈ interiorCellVertices ε η (ball z r) →
      (cell ε η (q j) ∩ ball z r).Nonempty :=
    fun j hj => ⟨vertexPoint ε η (q j), vertexPoint_mem_cell_of_nonneg hε0 (q j), hvp _ hj⟩
  have hcell_sub : ∀ j, q j ∈ interiorCellVertices ε η (ball z r) → cell ε η (q j) ⊆ ball z r :=
    fun j hj => cell_subset_of_mem_interiorCellVertices isOpen_ball hj
      (cell_isConnected_of_continuous hε0 hη (q j))
  have hTm : 0 ≤ T * mε := mul_nonneg hT hm.le
  have hmN : ((⌊T * mε⌋₊ : ℕ) : ℝ) ≤ T * mε := Nat.floor_le hTm
  have hmN' : T * mε < ((⌊T * mε⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  set N := ⌊T * mε⌋₊ with hNdef
  set W : ℝ≥0 → ℂ := interpolatedWalk ε η mε q with hWdef
  have hne_min : min (ENNReal.ofReal T) (pathExitTime (ball z r) W) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  set s := (min (ENNReal.ofReal T) (pathExitTime (ball z r) W)).toReal with hsdef
  set sn := (min (ENNReal.ofReal T) (pathExitTime (ball z (r - δ)) W)).toReal with hsndef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hsT : s ≤ T := ENNReal.toReal_le_of_le_ofReal hT (min_le_left _ _)
  have hsn_le_s : sn ≤ s := by
    apply ENNReal.toReal_mono hne_min
    exact min_le_min_left _ (pathExitTime_mono (ball_subset_ball (by linarith)))
  have hsn0 : 0 ≤ sn := ENNReal.toReal_nonneg
  rw [← intervalIntegral.integral_of_le hs0]
  have hsT_mem : ∀ t : ℝ, 0 ≤ t → t < s → W t.toNNReal ∈ ball z r := by
    intro t ht0 hts
    apply mem_of_lt_pathExitTime (t := t.toNNReal)
    have h1 : ENNReal.ofReal t < min (ENNReal.ofReal T) (pathExitTime (ball z r) W) :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht0 hne_min).2 hts
    exact lt_of_lt_of_le h1 (min_le_right _ _)
  have hlow : ∀ a : ℝ, 0 ≤ a → a ≤ T → (∀ t : ℝ≥0, (t : ℝ) ≤ a → W t ∈ ball z r) → a ≤ s := by
    intro a ha0 haT hW
    have h1 : ENNReal.ofReal a ≤ pathExitTime (ball z r) W := le_pathExitTime_of_forall_mem_riemann hW
    have h2 : ENNReal.ofReal a ≤ min (ENNReal.ofReal T) (pathExitTime (ball z r) W) :=
      le_min (ENNReal.ofReal_le_ofReal haT) h1
    have h3 := ENNReal.toReal_mono hne_min h2
    rwa [ENNReal.toReal_ofReal ha0] at h3
  have hsn_le : ∀ a : ℝ, 0 ≤ a → W a.toNNReal ∉ ball z (r - δ) → sn ≤ a := by
    intro a ha0 hnot
    have h1 : pathExitTime (ball z (r - δ)) W ≤ ENNReal.ofReal a := by
      unfold pathExitTime
      exact sInf_le ⟨a.toNNReal, rfl, hnot⟩
    exact ENNReal.toReal_le_of_le_ofReal ha0 (le_trans (min_le_right _ _) h1)
  have hlen : ∀ k : ℕ, ((k : ℝ) + 1) / mε - (k : ℝ) / mε = mε⁻¹ := fun k => by
    rw [← sub_div]
    ring
  by_cases hkill : ∃ j, j ≤ N ∧ q j ∉ interiorCellVertices ε η (ball z r)
  · have hex : ∃ j, q j ∉ interiorCellVertices ε η (ball z r) := by
      obtain ⟨j, -, hj⟩ := hkill
      exact ⟨j, hj⟩
    obtain ⟨K, hKdef⟩ : ∃ K, K = Nat.find hex := ⟨_, rfl⟩
    have hKnot : q K ∉ interiorCellVertices ε η (ball z r) := by
      rw [hKdef]
      exact Nat.find_spec hex
    have hKmin : ∀ j < K, q j ∈ interiorCellVertices ε η (ball z r) := by
      intro j hj
      rw [hKdef] at hj
      exact not_not.1 (Nat.find_min hex hj)
    have hKN : K ≤ N := by
      obtain ⟨j, hjN, hj⟩ := hkill
      have h := Nat.find_min' hex hj
      rw [← hKdef] at h
      exact h.trans hjN
    have hK0 : K ≠ 0 := by
      rintro rfl
      exact hKnot hq0
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    have hkI : ∀ j ≤ k, q j ∈ interiorCellVertices ε η (ball z r) := fun j hj => hKmin j (by omega)
    have hkN : k + 1 ≤ N := hKN
    have hzero : ∀ i ∈ range N, i ∉ range (k + 1) →
        (if (∀ j ≤ i, q j ∈ interiorCellVertices ε η (ball z r)) then g (vertexPoint ε η (q i)) else 0) = 0 := by
      intro i _ hi
      have hi' : ¬ i < k + 1 := fun h => hi (Finset.mem_range.2 h)
      split_ifs with hc
      · exact absurd (hc (k + 1) (by omega)) hKnot
      · rfl
    have hsub := Finset.sum_subset (Finset.range_mono hkN) hzero
    have hQ : ∑ i ∈ range N, (if (∀ j ≤ i, q j ∈ interiorCellVertices ε η (ball z r)) then
        g (vertexPoint ε η (q i)) else 0)
        = ∑ i ∈ range k, g (vertexPoint ε η (q i)) + g (vertexPoint ε η (q k)) := by
      rw [← hsub, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < k := Finset.mem_range.1 hi
        have h : (∀ j ≤ i, q j ∈ interiorCellVertices ε η (ball z r)) := fun j hj => hkI j (by omega)
        split_ifs
        rfl
      · split_ifs
        rfl
    rw [hQ]
    have ha0 : 0 ≤ (k : ℝ) / mε := div_nonneg (Nat.cast_nonneg k) hm.le
    have hkN' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkN
    have hakT : (k : ℝ) / mε ≤ T := (div_le_iff₀ hm).2 (by linarith)
    have hint_k : ∀ j ≤ k, vertexPoint ε η (q j) ∈ ball z r := fun j hj => hvp _ (hkI j hj)
    have hdist_k : ∀ j < k, dist (vertexPoint ε η (q j)) (vertexPoint ε η (q (j + 1))) ≤ 2 * d :=
      fun j hj => dist_vertexPoint_le_two_mul_of_cells_meet hε0 hη (hadj j (by omega))
        (hdiam j (by omega) (hmeetD j (hkI j (by omega))))
        (hdiam (j + 1) (by omega) (hmeetD (j + 1) (hkI (j + 1) (by omega))))
    have h1 := abs_sum_sub_integral_le hg hχ hM hm (e := 2 * d) k hint_k hdist_k
    rw [← hWdef] at h1
    have hWk : ∀ t : ℝ≥0, (t : ℝ) ≤ (k : ℝ) / mε → W t ∈ ball z r := walk_mem_ball_of_le hm k hint_k
    have hks : (k : ℝ) / mε ≤ s := hlow _ ha0 hakT hWk
    have hmeetK1 : (cell ε η (q (k + 1)) ∩ ball z r).Nonempty := by
      obtain ⟨x, hx1, hx2⟩ := hadj k (by omega)
      exact ⟨x, hx2, hcell_sub k (hkI k le_rfl) hx1⟩
    obtain ⟨w, hwf, hdw⟩ := exists_frontier_within_two_mul_of_first_exit isOpen_ball hε0 hη hkI hKnot
      (hadj k (by omega)) (hdiam k (by omega) (hmeetD k (hkI k le_rfl))) (hdiam (k + 1) hkN hmeetK1)
    have hAfar : vertexPoint ε η (q k) ∉ ball z (r - δ) := by
      intro hmem
      have h2 := sub_le_dist_center_of_near_frontier hr.ne' hwf hdw
      rw [mem_ball] at hmem
      linarith
    have hWa : W (((k : ℝ) / mε).toNNReal) = vertexPoint ε η (q k) := interpolatedWalk_grid hm k
    have hsn_a : sn ≤ (k : ℝ) / mε := hsn_le _ ha0 (by rw [hWa]; exact hAfar)
    have hab : (k : ℝ) / mε ≤ ((k : ℝ) + 1) / mε := div_le_div_of_nonneg_right (by linarith) hm.le
    have has' : (k : ℝ) / mε ≤ min s (((k : ℝ) + 1) / mε) := le_min hks hab
    have hI1 : IntervalIntegrable (fun t : ℝ => g (W t.toNNReal)) volume 0 ((k : ℝ) / mε) :=
      intervalIntegrable_g_walk hg hχ hM ha0 (fun t h1 h2 => hWk t.toNNReal (by
        rw [Real.coe_toNNReal _ h1.le]; exact h2.le))
    have hI2 : IntervalIntegrable (fun t : ℝ => g (W t.toNNReal)) volume ((k : ℝ) / mε) s :=
      intervalIntegrable_g_walk hg hχ hM hks (fun t h1 h2 => hsT_mem t (by linarith) h2)
    have hI2a : IntervalIntegrable (fun t : ℝ => g (W t.toNNReal)) volume ((k : ℝ) / mε)
        (min s (((k : ℝ) + 1) / mε)) :=
      intervalIntegrable_g_walk hg hχ hM has' (fun t h1 h2 =>
        hsT_mem t (by linarith) (lt_of_lt_of_le h2 (min_le_left _ _)))
    have hI2b : IntervalIntegrable (fun t : ℝ => g (W t.toNNReal)) volume (min s (((k : ℝ) + 1) / mε)) s :=
      intervalIntegrable_g_walk hg hχ hM (min_le_left _ _) (fun t h1 h2 => hsT_mem t (by linarith) h2)
    set c := min s (((k : ℝ) + 1) / mε) with hcdef
    have hsplit3 : (∫ t in (0 : ℝ)..s, g (W t.toNNReal)) = (∫ t in (0 : ℝ)..((k : ℝ) / mε), g (W t.toNNReal))
        + ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) + (∫ t in c..s, g (W t.toNNReal))) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hI2a hI2b,
        intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    have hseg := abs_integral_sub_le_of_segment hg hχ hM hm (k := k) (c := c) (e := 2 * d) has'
      (min_le_right _ _) (hint_k k le_rfl)
      (dist_vertexPoint_le_two_mul_of_cells_meet hε0 hη (hadj k (by omega))
        (hdiam k (by omega) (hmeetD k (hkI k le_rfl))) (hdiam (k + 1) hkN hmeetK1))
      (fun t h1 h2 => hsT_mem t (by linarith) (lt_of_lt_of_le h2 (min_le_left _ _)))
    rw [← hWdef] at hseg
    have hc_le : c - (k : ℝ) / mε ≤ mε⁻¹ := by
      have h3 := min_le_right s (((k : ℝ) + 1) / mε)
      have h4 := hlen k
      linarith
    have htail : |∫ t in c..s, g (W t.toNNReal)| ≤ M * (s - c) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := s) (C := M)
        (f := fun t : ℝ => g (W t.toNNReal))
        (fun t ht => by
          rw [Set.uIoc_of_le (min_le_left _ _)] at ht
          rw [Real.norm_eq_abs]
          exact hM _)
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (min_le_left _ _))] at h
    have hshell_tail : s - c ≤ s - sn := by
      have h5 := le_min hsn_le_s (hsn_a.trans hab)
      linarith
    have hfirst : |(mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k))| ≤ mε⁻¹ * M := by
      rw [abs_mul]
      refine mul_le_mul ?_ (hM _) (abs_nonneg _) (inv_nonneg.2 hm.le)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hY : 0 ≤ (C : ℝ) * (2 * d) ^ (χ : ℝ) := mul_nonneg C.2 (Real.rpow_nonneg (by linarith) _)
    have hA2 : |(∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k))|
        ≤ mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ)) :=
      hseg.trans (mul_le_mul_of_nonneg_right hc_le hY)
    have hXb : |∫ t in c..s, g (W t.toNNReal)| ≤ M * (s - sn) :=
      htail.trans (mul_le_mul_of_nonneg_left hshell_tail hM0)
    have hNC2 : ((k : ℝ) + 1) * (mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ))) ≤ T * C * (2 * d) ^ (χ : ℝ) := by
      have hk1T : ((k : ℝ) + 1) * mε⁻¹ ≤ T := by
        rw [← div_eq_mul_inv, div_le_iff₀ hm]
        linarith
      calc ((k : ℝ) + 1) * (mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ)))
          = (((k : ℝ) + 1) * mε⁻¹) * ((C : ℝ) * (2 * d) ^ (χ : ℝ)) := by ring
        _ ≤ T * ((C : ℝ) * (2 * d) ^ (χ : ℝ)) := mul_le_mul_of_nonneg_right hk1T hY
        _ = T * C * (2 * d) ^ (χ : ℝ) := by ring
    have hid : (mε⁻¹ * (∑ i ∈ range k, g (vertexPoint ε η (q i)) + g (vertexPoint ε η (q k))))
        - (∫ t in (0 : ℝ)..s, g (W t.toNNReal))
        = (mε⁻¹ * (∑ i ∈ range k, g (vertexPoint ε η (q i))) - (∫ t in (0 : ℝ)..((k : ℝ) / mε), g (W t.toNNReal)))
          + (((mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k)))
            - ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k)))
            - (∫ t in c..s, g (W t.toNNReal))) := by
      rw [hsplit3]
      ring
    rw [hid]
    have hX2 : |((mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k)))
          - ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k)))
          - (∫ t in c..s, g (W t.toNNReal))|
        ≤ |(mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k))|
          + |(∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k))|
          + |∫ t in c..s, g (W t.toNNReal)| := by
      have h6 := abs_sub ((mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k)))
        ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k)))
      have h7 := abs_sub ((mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k)))
        ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k)))
      have h8 := abs_sub (((mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k)))
          - ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k))))
        (∫ t in c..s, g (W t.toNNReal))
      linarith
    have hsum := abs_add_le
      (mε⁻¹ * (∑ i ∈ range k, g (vertexPoint ε η (q i))) - (∫ t in (0 : ℝ)..((k : ℝ) / mε), g (W t.toNNReal)))
      ((mε⁻¹ - (c - (k : ℝ) / mε)) * g (vertexPoint ε η (q k))
          - ((∫ t in ((k : ℝ) / mε)..c, g (W t.toNNReal)) - (c - (k : ℝ) / mε) * g (vertexPoint ε η (q k)))
          - (∫ t in c..s, g (W t.toNNReal)))
    have hkZ : (k : ℝ) * (mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ)))
        + mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ)) = ((k : ℝ) + 1) * (mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ))) := by
      ring
    have e4 : 4 * M * mε⁻¹ = 4 * (mε⁻¹ * M) := by ring
    have hk1 : (k : ℝ) * (mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ))) ≥ 0 := by
      have := mul_nonneg (inv_nonneg.2 hm.le) hY
      exact mul_nonneg (Nat.cast_nonneg k) this
    have hMm : 0 ≤ mε⁻¹ * M := mul_nonneg (inv_nonneg.2 hm.le) hM0
    have hshell : 0 ≤ M * (s - sn) := mul_nonneg hM0 (by linarith)
    linarith [hsum, h1, hX2, hA2, hXb, hfirst, hNC2, hkZ, e4, hMm, hshell]
  · -- Case A: every vertex of the first ⌊Tm⌋ steps is interior.
    have hall : ∀ j ≤ N, q j ∈ interiorCellVertices ε η (ball z r) := fun j hj => by
      by_contra h
      exact hkill ⟨j, hj, h⟩
    have hint : ∀ j ≤ N, vertexPoint ε η (q j) ∈ ball z r := fun j hj => hvp _ (hall j hj)
    have hdist : ∀ j < N, dist (vertexPoint ε η (q j)) (vertexPoint ε η (q (j + 1))) ≤ 2 * d :=
      fun j hj => dist_vertexPoint_le_two_mul_of_cells_meet hε0 hη (hadj j hj)
        (hdiam j hj.le (hmeetD j (hall j hj.le))) (hdiam (j + 1) hj (hmeetD (j + 1) (hall (j + 1) hj)))
    have hsum : ∑ k ∈ range N, (if (∀ j ≤ k, q j ∈ interiorCellVertices ε η (ball z r)) then
        g (vertexPoint ε η (q k)) else 0) = ∑ k ∈ range N, g (vertexPoint ε η (q k)) :=
      Finset.sum_congr rfl fun k hk => by
        have h : (∀ j ≤ k, q j ∈ interiorCellVertices ε η (ball z r)) :=
          fun j hj => hall j (le_trans hj (Finset.mem_range.1 hk).le)
        split_ifs
        rfl
    rw [hsum]
    have h1 := abs_sum_sub_integral_le hg hχ hM hm (e := 2 * d) N hint hdist
    rw [← hWdef] at h1
    have hNm : (N : ℝ) / mε ≤ T := (div_le_iff₀ hm).2 hmN
    have hWN : ∀ t : ℝ≥0, (t : ℝ) ≤ (N : ℝ) / mε → W t ∈ ball z r := walk_mem_ball_of_le hm N hint
    have hN0 : 0 ≤ (N : ℝ) / mε := div_nonneg (Nat.cast_nonneg N) hm.le
    have hNs : (N : ℝ) / mε ≤ s := hlow _ hN0 hNm hWN
    have hI1 : IntervalIntegrable (fun t : ℝ => g (W t.toNNReal)) volume 0 ((N : ℝ) / mε) :=
      intervalIntegrable_g_walk hg hχ hM hN0 (fun t h1 h2 => hWN t.toNNReal (by
        rw [Real.coe_toNNReal _ h1.le]; exact h2.le))
    have hI2 : IntervalIntegrable (fun t : ℝ => g (W t.toNNReal)) volume ((N : ℝ) / mε) s :=
      intervalIntegrable_g_walk hg hχ hM hNs (fun t h1 h2 => hsT_mem t (by linarith) h2)
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hbd2 : |∫ t in ((N : ℝ) / mε)..s, g (W t.toNNReal)| ≤ M * (s - (N : ℝ) / mε) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N : ℝ) / mε) (b := s) (C := M)
        (f := fun t : ℝ => g (W t.toNNReal))
        (fun t ht => by
          rw [Set.uIoc_of_le hNs] at ht
          rw [Real.norm_eq_abs]
          exact hM _)
      rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hNs)] at h
    have hsN : s - (N : ℝ) / mε ≤ mε⁻¹ := by
      have h3 : (T - (N : ℝ) / mε) * mε ≤ 1 := by
        rw [sub_mul, div_mul_cancel₀ _ hm.ne']
        linarith
      calc s - (N : ℝ) / mε ≤ T - (N : ℝ) / mε := by linarith
        _ = ((T - (N : ℝ) / mε) * mε) * mε⁻¹ := by field_simp
        _ ≤ 1 * mε⁻¹ := mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 hm.le)
        _ = mε⁻¹ := one_mul _
    have hNC : (N : ℝ) * (mε⁻¹ * (C * (2 * d) ^ (χ : ℝ))) ≤ T * C * (2 * d) ^ (χ : ℝ) := by
      have hX : 0 ≤ (C : ℝ) * (2 * d) ^ (χ : ℝ) := mul_nonneg C.2 (Real.rpow_nonneg (by linarith) _)
      have hNm' : (N : ℝ) * mε⁻¹ ≤ T := by
        rw [← div_eq_mul_inv]
        exact hNm
      calc (N : ℝ) * (mε⁻¹ * ((C : ℝ) * (2 * d) ^ (χ : ℝ)))
          = ((N : ℝ) * mε⁻¹) * ((C : ℝ) * (2 * d) ^ (χ : ℝ)) := by ring
        _ ≤ T * ((C : ℝ) * (2 * d) ^ (χ : ℝ)) := mul_le_mul_of_nonneg_right hNm' hX
        _ = T * C * (2 * d) ^ (χ : ℝ) := by ring
    have hkey : mε⁻¹ * (∑ k ∈ range N, g (vertexPoint ε η (q k))) - ∫ t in (0 : ℝ)..s, g (W t.toNNReal)
        = (mε⁻¹ * (∑ k ∈ range N, g (vertexPoint ε η (q k)))
          - ∫ t in (0 : ℝ)..((N : ℝ) / mε), g (W t.toNNReal))
          - ∫ t in ((N : ℝ) / mε)..s, g (W t.toNNReal) := by
      rw [← hsplit2]
      ring
    rw [hkey]
    have hfr : |∫ t in ((N : ℝ) / mε)..s, g (W t.toNNReal)| ≤ mε⁻¹ * M := by
      have hMs := mul_le_mul_of_nonneg_left hsN hM0
      rw [mul_comm mε⁻¹ M]
      exact hbd2.trans hMs
    have hA := abs_sub (mε⁻¹ * (∑ k ∈ range N, g (vertexPoint ε η (q k))) - ∫ t in (0 : ℝ)..((N : ℝ) / mε), g (W t.toNNReal))
      (∫ t in ((N : ℝ) / mε)..s, g (W t.toNNReal))
    have hshell : 0 ≤ M * (s - sn) := mul_nonneg hM0 (by linarith)
    have hMm : 0 ≤ mε⁻¹ * M := mul_nonneg (inv_nonneg.2 hm.le) hM0
    have e4 : 4 * M * mε⁻¹ = 4 * (mε⁻¹ * M) := by ring
    calc |(mε⁻¹ * (∑ k ∈ range N, g (vertexPoint ε η (q k)))
            - (∫ t in (0 : ℝ)..((N : ℝ) / mε), g (W t.toNNReal)))
          - (∫ t in ((N : ℝ) / mε)..s, g (W t.toNNReal))|
        ≤ |mε⁻¹ * (∑ k ∈ range N, g (vertexPoint ε η (q k)))
            - (∫ t in (0 : ℝ)..((N : ℝ) / mε), g (W t.toNNReal))|
          + |∫ t in ((N : ℝ) / mε)..s, g (W t.toNNReal)| := hA
      _ ≤ (N : ℝ) * (mε⁻¹ * (C * (2 * d) ^ (χ : ℝ))) + mε⁻¹ * M := add_le_add h1 hfr
      _ ≤ T * C * (2 * d) ^ (χ : ℝ) + mε⁻¹ * M := add_le_add_left hNC _
      _ ≤ T * C * (2 * d) ^ (χ : ℝ) + 4 * M * mε⁻¹ + M * (s - sn) := by
          rw [e4]
          linarith [hshell, hMm]

end MatedCRT.TruncatedLaws
