import MatedCRT.FirstPass.Derived.ZeroConeLemmaA4Proof

/-!
# The sector geometry for the zero-cone circle-average lemma

For a measure `ν` on `ℂ` which is finite on compacts and has infinite mass in each of the eight open sectors
`a1Sector j` of half-angle `π/6` around the directions `exp(2πij/8)`, the mass radius `r_{b₀}(z)` of `ν` at `z`
is smaller than `‖z‖ - k` once `‖z‖` is large (Gwynne–Miller–Sheffield, arXiv:1705.11161, Appendix A; the written
proof is the second paragraph of §3 of the written answer to the gap check of Lemma A.1).

## Main definitions and statements

* `a1Sector j`: the open sector of half-angle `π/6` around the direction `exp(2πij/8)`.
* `isOpen_a1Sector`: it is open.
* `exists_massRadius_lt_norm_sub`: the mass radius at `z` is below `‖z‖ - k` for all large `z`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Metric

/-- The open sector of half-angle `π/6` around the direction `exp(2πij/8)`. -/
def a1Sector (j : Fin 8) : Set ℂ :=
  {w | w ≠ 0 ∧ |Complex.arg (w * Complex.exp (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I))| < Real.pi / 6}

/-- The sectors are open: the argument is continuous off the origin on a neighbourhood of the sector. -/
theorem isOpen_a1Sector (j : Fin 8) : IsOpen (a1Sector j) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  set c : ℂ := Complex.exp (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hwc : w * c ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨fun h => ?_, mul_ne_zero hw.1 hc0⟩
    have h2 := hw.2
    rw [h, abs_of_pos Real.pi_pos] at h2
    linarith [Real.pi_pos]
  have hmul : ContinuousAt (fun v : ℂ => v * c) w := continuousAt_id.mul continuousAt_const
  have hcont : ContinuousAt (fun v : ℂ => |Complex.arg (v * c)|) w :=
    (ContinuousAt.comp (f := fun v : ℂ => v * c) (Complex.continuousAt_arg hwc) hmul).abs
  have h1 : {v : ℂ | |Complex.arg (v * c)| < Real.pi / 6} ∈ nhds w :=
    hcont.eventually (gt_mem_nhds hw.2)
  have h2 : {v : ℂ | v ≠ 0} ∈ nhds w := isOpen_ne.mem_nhds hw.1
  exact Filter.inter_mem h2 h1

/-- The unit rotation `exp(-2πij/8)` has norm one. -/
theorem norm_a1Rot (j : Fin 8) :
    ‖Complex.exp (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I)‖ = 1 := by
  have : (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I : ℂ) = ((-(2 * Real.pi * (j : ℝ) / 8) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- If two nonzero complex numbers have arguments in `(-π/6, π/6)` and `[-π/8, π/8]`, their product with the
conjugate has real part more than half of the product of the norms. -/
theorem half_mul_norm_lt_re_mul_conj {y w : ℂ} (hy0 : y ≠ 0) (hw0 : w ≠ 0)
    (hy : |Complex.arg y| < Real.pi / 6) (hw : |Complex.arg w| ≤ Real.pi / 8) :
    ‖y‖ * ‖w‖ / 2 < (y * (starRingEnd ℂ) w).re := by
  have hre : (y * (starRingEnd ℂ) w).re = ‖y‖ * ‖w‖ * Real.cos (Complex.arg y - Complex.arg w) := by
    rw [Real.cos_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.norm_mul_cos_arg y,
      ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg y, ← Complex.norm_mul_sin_arg w]
    ring
  have hcos : (1 : ℝ) / 2 < Real.cos (Complex.arg y - Complex.arg w) := by
    have hab : |Complex.arg y - Complex.arg w| < Real.pi / 3 := by
      calc |Complex.arg y - Complex.arg w| ≤ |Complex.arg y| + |Complex.arg w| := abs_sub _ _
        _ < Real.pi / 3 := by linarith [Real.pi_pos]
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hab
  rw [hre]
  have hpos : 0 < ‖y‖ * ‖w‖ := mul_pos (norm_pos_iff.2 hy0) (norm_pos_iff.2 hw0)
  nlinarith

/-- Every nonzero complex number makes an angle at most `π/8` with one of the eight axes. -/
theorem exists_axis_arg_le {z : ℂ} (hz : z ≠ 0) :
    ∃ j : Fin 8, |Complex.arg (z * Complex.exp (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I))| ≤ Real.pi / 8 := by
  set φ := Complex.arg z with hφ
  set m : ℤ := round (φ / (Real.pi / 4)) with hm
  set r : ℝ := φ - m * (Real.pi / 4) with hr
  have hpi := Real.pi_pos
  have hr8 : |r| ≤ Real.pi / 8 := by
    have h := abs_sub_round (φ / (Real.pi / 4))
    rw [← hm] at h
    have h2 : r = (φ / (Real.pi / 4) - m) * (Real.pi / 4) := by
      rw [hr]; field_simp
    rw [h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 4)]
    have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ Real.pi / 4)
    linarith
  set j : Fin 8 := ⟨(m % 8).toNat, by omega⟩ with hj
  have hjz : ((j : ℕ) : ℤ) = m % 8 := by simp [hj]; omega
  have hmz : m % 8 + 8 * (m / 8) = m := by omega
  have hjr : ((j : ℕ) : ℝ) + 8 * ((m / 8 : ℤ) : ℝ) = (m : ℝ) := by
    have : (((j : ℕ) : ℤ) : ℝ) + 8 * ((m / 8 : ℤ) : ℝ) = ((m : ℤ) : ℝ) := by
      rw [hjz]; exact_mod_cast hmz
    simpa using this
  refine ⟨j, ?_⟩
  have hprod : z * Complex.exp (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I) =
      (‖z‖ : ℂ) * Complex.exp (r * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    have hrC : (r : ℂ) = φ - m * (Real.pi / 4) := by rw [hr]; push_cast; ring
    have hmC : (m : ℂ) = ((j : ℕ) : ℂ) + 8 * ((m / 8 : ℤ) : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hjr
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_intCast,
        Complex.ofReal_ofNat] at this
      exact this.symm
    have h2 : (φ : ℂ) * Complex.I + -(2 * Real.pi * (j : ℝ) / 8) * Complex.I =
        r * Complex.I + ((m / 8 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hrC, hmC]; push_cast; ring
    rw [← hφ, h2]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hprod, Complex.arg_real_mul _ (norm_pos_iff.2 hz), Complex.arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).2
      ⟨by linarith [(abs_le.1 hr8).1], by linarith [(abs_le.1 hr8).2]⟩]
  exact hr8

/-- In each sector of infinite mass, a bounded portion far from the origin already has mass above any given level. -/
theorem exists_nat_lt_measure_sector {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] {j : Fin 8}
    (hsec : ν (a1Sector j) = ⊤) (c b₀ : ℝ) :
    ∃ n : ℕ, ENNReal.ofReal b₀ < ν (a1Sector j ∩ {x | c < ‖x‖} ∩ closedBall 0 n) := by
  have htop : ν (a1Sector j ∩ {x | c < ‖x‖}) = ⊤ := by
    by_contra hne
    have hlt : ν (a1Sector j) < ⊤ := by
      calc ν (a1Sector j)
          ≤ ν ((a1Sector j ∩ closedBall 0 c) ∪ (a1Sector j ∩ {x | c < ‖x‖})) := by
            refine measure_mono fun x hx => ?_
            by_cases h : ‖x‖ ≤ c
            · exact Or.inl ⟨hx, by simpa using h⟩
            · exact Or.inr ⟨hx, lt_of_not_ge h⟩
        _ ≤ ν (a1Sector j ∩ closedBall 0 c) + ν (a1Sector j ∩ {x | c < ‖x‖}) := measure_union_le _ _
        _ < ⊤ := ENNReal.add_lt_top.2
            ⟨lt_of_le_of_lt (measure_mono inter_subset_right) measure_closedBall_lt_top,
              lt_top_iff_ne_top.2 hne⟩
    exact hlt.ne hsec
  have hmono : Monotone fun n : ℕ => a1Sector j ∩ {x | c < ‖x‖} ∩ closedBall (0 : ℂ) n :=
    fun a b hab => inter_subset_inter_right _ (closedBall_subset_closedBall (Nat.cast_le.2 hab))
  have hunion : (⋃ n : ℕ, a1Sector j ∩ {x | c < ‖x‖} ∩ closedBall (0 : ℂ) n) =
      a1Sector j ∩ {x | c < ‖x‖} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨n, h, _⟩; exact h
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
      exact ⟨n, h, hn⟩
  have hsup := hmono.measure_iUnion (μ := ν)
  rw [hunion, htop] at hsup
  have : ENNReal.ofReal b₀ < ⨆ n : ℕ, ν (a1Sector j ∩ {x | c < ‖x‖} ∩ closedBall (0 : ℂ) n) := by
    rw [← hsup]; exact ENNReal.ofReal_lt_top
  exact lt_iSup_iff.1 this

/-- **The mass radius at a far point is below its norm minus `k`.** If a measure `ν` on `ℂ` is finite on compacts and
has infinite mass in each of the eight sectors `a1Sector j`, then for every `k` and `b₀` the mass radius
`r_{b₀}(z) = inf {r > 0 : ν(B_r(z)) > b₀}` is smaller than `‖z‖ - k` for all `z` of large norm. -/
theorem exists_massRadius_lt_norm_sub {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν]
    (hsec : ∀ j : Fin 8, ν (a1Sector j) = ⊤) (k b₀ : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → ZeroConeRoot.massRadius ν b₀ z < ‖z‖ - k := by
  choose n hn using fun j => exists_nat_lt_measure_sector (hsec j) (2 * (k + 2)) b₀
  set D : ℝ := ∑ j, (n j : ℝ) with hD
  have hnD : ∀ j, (n j : ℝ) ≤ D := fun j =>
    Finset.single_le_sum (f := fun j => (n j : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨D ^ 2 + |k| + 2, fun z hz => ?_⟩
  set t : ℝ := ‖z‖ with ht
  have hkabs : k ≤ |k| := le_abs_self k
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  have htpos : 0 < t := by linarith [abs_nonneg k]
  have hz0 : z ≠ 0 := norm_pos_iff.1 htpos
  have hr : 0 < t - k - 1 := by linarith
  obtain ⟨j, hj⟩ := exists_axis_arg_le hz0
  have hsub : a1Sector j ∩ {x | 2 * (k + 2) < ‖x‖} ∩ closedBall (0 : ℂ) (n j) ⊆ ball z (t - k - 1) := by
    rintro x ⟨⟨hxs, hxc⟩, hxn⟩
    have hxD : ‖x‖ ≤ D := by
      have := mem_closedBall_zero_iff.1 hxn
      linarith [hnD j]
    set e : ℂ := Complex.exp (-(2 * Real.pi * (j : ℝ) / 8) * Complex.I) with he
    have he1 : ‖e‖ = 1 := norm_a1Rot j
    have hx0 : x ≠ 0 := hxs.1
    have hre := half_mul_norm_lt_re_mul_conj (mul_ne_zero hx0 (Complex.exp_ne_zero _))
      (mul_ne_zero hz0 (Complex.exp_ne_zero _)) hxs.2 hj
    have hyn : ‖x * e‖ = ‖x‖ := by rw [norm_mul, he1, mul_one]
    have hwn : ‖z * e‖ = t := by rw [norm_mul, he1, mul_one]
    have hdist : dist x z = ‖x * e - z * e‖ := by
      rw [← sub_mul, norm_mul, he1, mul_one, dist_eq_norm]
    have hsq : ‖x * e - z * e‖ ^ 2 = ‖x * e‖ ^ 2 + ‖z * e‖ ^ 2 - 2 * (x * e * (starRingEnd ℂ) (z * e)).re := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    rw [hyn, hwn] at hre hsq
    have hxt : 2 * (k + 2) * t < ‖x‖ * t := mul_lt_mul_of_pos_right hxc htpos
    have hlt : ‖x * e - z * e‖ ^ 2 < (t - k - 1) ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg (k + 1), mul_le_mul hxD hxD (norm_nonneg x) hD0]
    rw [mem_ball, hdist]
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_self_le_mul_self hr.le hcon]
  have hmass : ENNReal.ofReal b₀ < ν (ball z (t - k - 1)) :=
    lt_of_lt_of_le (hn j) (measure_mono hsub)
  have hmem : t - k - 1 ∈ {r : ℝ | 0 < r ∧ ENNReal.ofReal b₀ < ν (ball z r)} := ⟨hr, hmass⟩
  have := csInf_le ⟨0, fun r hr => hr.1.le⟩ hmem
  unfold ZeroConeRoot.massRadius
  linarith

end MatedCRT
