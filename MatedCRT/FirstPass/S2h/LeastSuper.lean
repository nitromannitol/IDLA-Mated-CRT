import MatedCRT.FirstPass.Frozen.S2h
import MatedCRT.FirstPass.S2g.Family
import MatedCRT.Draft.Section2

/-!
# Least-supersolution null hull of the cone (fp-S2h, z1, round 3)

Written argument: `notes/fp-gaps/CHATGPT-cone-leastsuper-null-hull.md`, Sections 2-7 (operator note 23:02 UTC).

* `lsoClass γ` (Section 2): finite mass on `closedBall 0 (7/8)` and, from some index `m ≥ 6` on, two-sided bounds
  `r_n^{β⁻} ≤ ν(B_{r_n}(q)) ≤ r_n^{β⁺}` at all rational centres `q` of `B_{13/16}`, with `r_n = 2^{-n}`.
  It is Giry-measurable (`measurableSet_lsoClass`).
* `ae_mem_lsoClass` (Section 3): cone measures lie in `lsoClass γ` almost surely, from `VolumeGrowthStmt`
  (Lemma 2.7) and the Radon property of the LQG measure, by Borel-Cantelli (`ae_eventually_notMem`).
* `lsoClass_leastSuperOK` (Sections 4-5): every `ν ∈ lsoClass γ` satisfies `LeastSuperOK ν`. The restriction
  `ν.restrict (closedBall 0 (7/8))` has volume growth on `B_{3/4}` (`volumeGrowth_restrict_of_mem`, a dyadic
  comparison); the frozen deterministic input `LeastSupersolutionMemOfVolumeGrowthStmt` applies; the restriction
  does not change the supersolution class (`supersolutions_restrict`, `laplacianLE_restrict_iff`).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-! ## Exponents and dyadic radii -/

/-- The lower exponent `β⁻ = (2+γ)²/2 + 1` of the class (`(2+γ)²/2 < β⁻`, as in `VolumeGrowthStmt`). -/
noncomputable def lsoLowerExp (γ : ℝ) : ℝ := (2 + γ) ^ 2 / 2 + 1

/-- The upper exponent `β⁺ = (2-γ)²/4` of the class (`0 < β⁺ < (2-γ)²/2`). -/
noncomputable def lsoUpperExp (γ : ℝ) : ℝ := (2 - γ) ^ 2 / 4

lemma lsoLowerExp_pos (γ : ℝ) : 0 < lsoLowerExp γ := by
  unfold lsoLowerExp
  positivity

lemma lsoUpperExp_pos {γ : ℝ} (hγ2 : γ < 2) : 0 < lsoUpperExp γ := by
  unfold lsoUpperExp
  have h : 0 < 2 - γ := by linarith
  exact div_pos (pow_pos h 2) (by norm_num)

lemma lsoUpperExp_lt {γ : ℝ} (hγ2 : γ < 2) : lsoUpperExp γ < (2 - γ) ^ 2 / 2 := by
  have h : 0 < 2 - γ := by linarith
  unfold lsoUpperExp
  have := pow_pos h 2
  linarith

lemma lsoLowerExp_gt (γ : ℝ) : (2 + γ) ^ 2 / 2 < lsoLowerExp γ := by
  unfold lsoLowerExp
  linarith

/-- The dyadic radius `r_n = 2^{-n}` (Section 2 of the written argument). -/
noncomputable def dyadicRad (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

lemma dyadicRad_pos (n : ℕ) : 0 < dyadicRad n := pow_pos (by norm_num) n

lemma dyadicRad_anti {k m : ℕ} (h : k ≤ m) : dyadicRad m ≤ dyadicRad k :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

lemma le_of_dyadicRad_lt {k m : ℕ} (h : dyadicRad k < dyadicRad m) : m ≤ k := by
  by_contra hc
  exact absurd h (not_lt.2 (dyadicRad_anti (show k ≤ m by omega)))

lemma dyadicRad_six : dyadicRad 6 = 1 / 64 := by
  norm_num [dyadicRad]

lemma dyadicRad_le_of_six_le {n : ℕ} (h : 6 ≤ n) : dyadicRad n ≤ 1 / 64 :=
  (dyadicRad_anti h).trans dyadicRad_six.le

lemma dyadicRad_rpow (n : ℕ) (p : ℝ) : (dyadicRad n) ^ p = ((1 / 2 : ℝ) ^ p) ^ n := by
  unfold dyadicRad
  have h : ((1 / 2 : ℝ) ^ n) ^ p = ((1 / 2 : ℝ) ^ (n : ℝ)) ^ p := by
    rw [Real.rpow_natCast]
  rw [h, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast]

/-- Every interval `[u, 2u)` with `0 < u ≤ 1` contains a dyadic radius. -/
lemma exists_dyadic_mem {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ n : ℕ, u ≤ dyadicRad n ∧ dyadicRad n < 2 * u := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := 1 / u) (y := (2 : ℝ))
    (one_le_one_div hu hu1) (by norm_num)
  refine ⟨n, ?_, ?_⟩
  · unfold dyadicRad
    rw [one_div_pow, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hu] at hn1
    linarith [mul_comm u ((2 : ℝ) ^ n)]
  · unfold dyadicRad
    rw [one_div_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hu, pow_succ] at hn2
    linarith [mul_comm u ((2 : ℝ) ^ n)]

/-! ## The class `lsoClass γ` -/

/-- Rational centres: `ratCentre (p, q) = p + i q`. -/
noncomputable def ratCentre (q : ℚ × ℚ) : ℂ := ⟨(q.1 : ℝ), (q.2 : ℝ)⟩

/-- The countable index set `Q = (ℚ + iℚ) ∩ B_{13/16}` of rational centres (Section 2). -/
abbrev RatCentreIdx : Type := {q : ℚ × ℚ // ‖ratCentre q‖ < 13 / 16}

/-- The two-sided bound at level `n`, centre `q`, in `[0, ∞]`: `r_n^{β⁻} ≤ ν(B_{r_n}(q)) ≤ r_n^{β⁺}`. -/
def lsoBound (γ : ℝ) (n : ℕ) (q : RatCentreIdx) (ν : Measure ℂ) : Prop :=
  ENNReal.ofReal ((dyadicRad n) ^ lsoLowerExp γ) ≤ ν (ball (ratCentre q.1) (dyadicRad n)) ∧
    ν (ball (ratCentre q.1) (dyadicRad n)) ≤ ENNReal.ofReal ((dyadicRad n) ^ lsoUpperExp γ)

/-- The class `R_γ` of Section 2 (CHATGPT-cone-leastsuper-null-hull.md, (1)): `ν(B̄_{7/8}) < ∞` and, for some
`m ≥ 6`, all levels `n ≥ m` and all rational centres satisfy the two-sided bounds. -/
def lsoClass (γ : ℝ) : Set (Measure ℂ) :=
  {ν | ν (closedBall (0 : ℂ) (7 / 8)) < ⊤ ∧
    ∃ m : ℕ, 6 ≤ m ∧ ∀ n : ℕ, m ≤ n → ∀ q : RatCentreIdx, lsoBound γ n q ν}

lemma measurableSet_lsoBound (γ : ℝ) (n : ℕ) (q : RatCentreIdx) :
    MeasurableSet {ν : Measure ℂ | lsoBound γ n q ν} := by
  have hm : Measurable fun ν : Measure ℂ => ν (ball (ratCentre q.1) (dyadicRad n)) :=
    Measure.measurable_coe measurableSet_ball
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

/-- `lsoClass γ` is Giry-measurable: countably many evaluations `ν ↦ ν s` on Borel sets (Section 2). -/
theorem measurableSet_lsoClass (γ : ℝ) : MeasurableSet (lsoClass γ) := by
  have h1 : MeasurableSet {ν : Measure ℂ | ν (closedBall (0 : ℂ) (7 / 8)) < ⊤} :=
    measurableSet_lt (Measure.measurable_coe measurableSet_closedBall) measurable_const
  have h2 : {ν : Measure ℂ | ∃ m : ℕ, 6 ≤ m ∧ ∀ n : ℕ, m ≤ n → ∀ q : RatCentreIdx, lsoBound γ n q ν} =
      ⋃ m ∈ Ici 6, ⋂ n ∈ Ici m, ⋂ q : RatCentreIdx, {ν : Measure ℂ | lsoBound γ n q ν} := by
    ext ν
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_Ici, exists_prop]
  have h3 : MeasurableSet {ν : Measure ℂ | ∃ m : ℕ, 6 ≤ m ∧ ∀ n : ℕ, m ≤ n → ∀ q : RatCentreIdx,
      lsoBound γ n q ν} := by
    rw [h2]
    exact MeasurableSet.biUnion (Set.to_countable _) fun m _ =>
      MeasurableSet.biInter (Set.to_countable _) fun n _ =>
        MeasurableSet.iInter fun q => measurableSet_lsoBound γ n q
  exact h1.inter h3

/-! ## Restriction to `closedBall 0 (7/8)` does not change the supersolution class -/

/-- Test functions supported in `U ⊆ K` see only `ν|K`: `LaplacianLE` is invariant under restriction to `K`. -/
theorem laplacianLE_restrict_iff {w : ℂ → ℝ} {ν : Measure ℂ} {K U : Set ℂ} (hUK : U ⊆ K) :
    LaplacianLE w (ν.restrict K) U ↔ LaplacianLE w ν U := by
  unfold LaplacianLE
  refine and_congr Iff.rfl ⟨fun h φ hφ hφ0 hint => ?_, fun h φ hφ hφ0 hint => ?_⟩
  · have hsupp : ∀ x, x ∉ K → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hxt => hx (hUK (hφ.2.2 hxt))
    have hi : Integrable φ (ν.restrict K) := hint.restrict
    have := h φ hφ hφ0 hi
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp] at this
    exact this
  · have hsupp : ∀ x, x ∉ K → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hxt => hx (hUK (hφ.2.2 hxt))
    have hsub : Function.support φ ⊆ K := fun x hx => by
      by_contra hxK
      exact hx (hsupp x hxK)
    have hi : Integrable φ ν := (integrableOn_iff_integrable_of_support_subset hsub).1 hint
    have := h φ hφ hφ0 hi
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    exact this

theorem supersolutions_restrict {ν : Measure ℂ} {K : Set ℂ} {r : ℝ} {z : ℂ} {t : ℝ}
    (hUK : ball (0 : ℂ) r ⊆ K) : supersolutions (ν.restrict K) r z t = supersolutions ν r z t := by
  ext w
  simp only [supersolutions, mem_ofPred_eq, laplacianLE_restrict_iff hUK]

theorem leastSupersolution_restrict {ν : Measure ℂ} {K : Set ℂ} {r : ℝ} {z : ℂ} {t : ℝ}
    (hUK : ball (0 : ℂ) r ⊆ K) : leastSupersolution (ν.restrict K) r z t = leastSupersolution ν r z t := by
  funext x
  simp only [leastSupersolution, supersolutions_restrict hUK]

/-! ## Volume growth of the restriction -/

/-- The restriction `ν|B̄_{7/8}` of a measure of `lsoClass γ` has volume growth on `B_{3/4}` with exponents
`(β⁻ + 1, β⁺/2)` (Section 4): the dyadic radii `δ₋ ∈ [r/4, r/2)` and `δ₊ ∈ [2r, 4r)` sandwich `B_r(z)` between
two balls centred at a rational point `q` with `|q - z| < r/4`. -/
theorem volumeGrowth_restrict_of_mem {γ : ℝ} (hγ2 : γ < 2) {ν : Measure ℂ} (hν : ν ∈ lsoClass γ) :
    VolumeGrowth (ν.restrict (closedBall (0 : ℂ) (7 / 8))) (3 / 4)
      (lsoLowerExp γ + 1) (lsoUpperExp γ / 2) := by
  obtain ⟨-, m, hm6, hm⟩ := hν
  have hb : 0 < lsoLowerExp γ := lsoLowerExp_pos γ
  have ha : 0 < lsoUpperExp γ := lsoUpperExp_pos hγ2
  have hr₀pos : 0 < min (min (dyadicRad m / 4) (1 / 16)) ((1 / 4 : ℝ) ^ lsoLowerExp γ) :=
    lt_min (lt_min (by have := dyadicRad_pos m; linarith) (by norm_num)) (by positivity)
  refine ⟨by linarith, by linarith, _, hr₀pos, fun r hr hrr z hz => ?_⟩
  have hr1 : r < dyadicRad m / 4 := lt_of_lt_of_le hrr ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : r < 1 / 16 := lt_of_lt_of_le hrr ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : r < (1 / 4 : ℝ) ^ lsoLowerExp γ := lt_of_lt_of_le hrr (min_le_right _ _)
  have hzn : ‖z‖ < 3 / 4 := by simpa [mem_ball_zero_iff] using hz
  have hm64 : dyadicRad m ≤ 1 / 64 := dyadicRad_le_of_six_le hm6
  -- a rational centre `c` with `|c - z| < r/4`
  obtain ⟨p1, hp1a, hp1b⟩ := exists_rat_btwn (show z.re - r / 8 < z.re + r / 8 by linarith)
  obtain ⟨p2, hp2a, hp2b⟩ := exists_rat_btwn (show z.im - r / 8 < z.im + r / 8 by linarith)
  have hcz : dist (ratCentre (p1, p2)) z < r / 4 := by
    rw [dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (ratCentre (p1, p2) - z)
    have h1 : |(ratCentre (p1, p2) - z).re| < r / 8 := by
      rw [abs_lt]
      simp only [ratCentre, Complex.sub_re]
      constructor <;> linarith
    have h2 : |(ratCentre (p1, p2) - z).im| < r / 8 := by
      rw [abs_lt]
      simp only [ratCentre, Complex.sub_im]
      constructor <;> linarith
    linarith
  have hcn : ‖ratCentre (p1, p2)‖ < 13 / 16 := by
    have h := norm_sub_norm_le (ratCentre (p1, p2)) z
    rw [dist_eq_norm] at hcz
    linarith
  set c : ℂ := ratCentre (p1, p2) with hc
  set q : RatCentreIdx := ⟨(p1, p2), hcn⟩ with hq
  -- dyadic radii `δ₋ ∈ [r/4, r/2)` and `δ₊ ∈ [2r, 4r)`
  obtain ⟨j, hj1, hj2⟩ := exists_dyadic_mem (u := r / 4) (by positivity) (by linarith)
  obtain ⟨k, hk1, hk2⟩ := exists_dyadic_mem (u := 2 * r) (by positivity) (by linarith)
  have hmj : m ≤ j := le_of_dyadicRad_lt (by linarith)
  have hmk : m ≤ k := le_of_dyadicRad_lt (by linarith)
  obtain ⟨hlow, -⟩ := hm j hmj q
  obtain ⟨-, hup⟩ := hm k hmk q
  -- inclusions of balls
  have hsub1 : ball c (dyadicRad j) ⊆ ball z r := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have := dist_triangle x c z
    linarith
  have hsub2 : ball z r ⊆ ball c (dyadicRad k) := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have := dist_triangle x z c
    rw [dist_comm z c] at this
    linarith
  have hsub3 : ball c (dyadicRad k) ⊆ closedBall (0 : ℂ) (7 / 8) := by
    intro x hx
    rw [mem_ball] at hx
    rw [mem_closedBall, dist_zero_right]
    have h := dist_triangle x c 0
    rw [dist_zero_right, dist_zero_right] at h
    have h4 : 4 * r < 1 / 64 := by linarith
    linarith
  have hsubK1 : ball c (dyadicRad j) ⊆ closedBall (0 : ℂ) (7 / 8) :=
    hsub1.trans (hsub2.trans hsub3)
  -- masses
  have heqj : ν.restrict (closedBall (0 : ℂ) (7 / 8)) (ball c (dyadicRad j)) = ν (ball c (dyadicRad j)) := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hsubK1]
  have heqk : ν.restrict (closedBall (0 : ℂ) (7 / 8)) (ball c (dyadicRad k)) = ν (ball c (dyadicRad k)) := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hsub3]
  -- real inequalities
  have hlowR : r ^ (lsoLowerExp γ + 1) ≤ (dyadicRad j) ^ lsoLowerExp γ := by
    have h1 : (r / 4) ^ lsoLowerExp γ ≤ (dyadicRad j) ^ lsoLowerExp γ :=
      Real.rpow_le_rpow (by positivity) hj1 hb.le
    have h2 : (r / 4) ^ lsoLowerExp γ = r ^ lsoLowerExp γ * (1 / 4) ^ lsoLowerExp γ := by
      rw [← Real.mul_rpow hr.le (by norm_num)]
      congr 1
      ring
    have h3 : r ^ (lsoLowerExp γ + 1) = r ^ lsoLowerExp γ * r := Real.rpow_add_one hr.ne' _
    have h4 : r ^ lsoLowerExp γ * r ≤ r ^ lsoLowerExp γ * (1 / 4) ^ lsoLowerExp γ :=
      mul_le_mul_of_nonneg_left hr3.le (Real.rpow_nonneg hr.le _)
    linarith
  have hupR : (dyadicRad k) ^ lsoUpperExp γ ≤ r ^ (lsoUpperExp γ / 2) := by
    have hk' : dyadicRad k ≤ 4 * r := by linarith
    have h1 : (dyadicRad k) ^ lsoUpperExp γ ≤ (4 * r) ^ lsoUpperExp γ :=
      Real.rpow_le_rpow (dyadicRad_pos k).le hk' ha.le
    have h2 : (4 * r) ^ lsoUpperExp γ = (4 : ℝ) ^ lsoUpperExp γ * r ^ lsoUpperExp γ :=
      Real.mul_rpow (by norm_num) hr.le
    have h3 : r ^ lsoUpperExp γ = r ^ (lsoUpperExp γ / 2) * r ^ (lsoUpperExp γ / 2) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    have hs : r ^ (lsoUpperExp γ / 2) ≤ ((1 : ℝ) / 16) ^ (lsoUpperExp γ / 2) :=
      Real.rpow_le_rpow hr.le hr2.le (by positivity)
    have h16 : ((1 : ℝ) / 16) ^ (lsoUpperExp γ / 2) = (1 / 4 : ℝ) ^ lsoUpperExp γ := by
      rw [show (1 : ℝ) / 16 = (1 / 4 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have h44 : (4 : ℝ) ^ lsoUpperExp γ * (1 / 4 : ℝ) ^ lsoUpperExp γ = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    have hpos : 0 < r ^ (lsoUpperExp γ / 2) := Real.rpow_pos_of_pos hr _
    have hk4 : (4 : ℝ) ^ lsoUpperExp γ * r ^ (lsoUpperExp γ / 2) ≤ 1 := by
      have : (4 : ℝ) ^ lsoUpperExp γ * r ^ (lsoUpperExp γ / 2) ≤
          (4 : ℝ) ^ lsoUpperExp γ * (1 / 4 : ℝ) ^ lsoUpperExp γ :=
        mul_le_mul_of_nonneg_left (hs.trans_eq h16) (by positivity)
      linarith
    calc (dyadicRad k) ^ lsoUpperExp γ ≤ (4 * r) ^ lsoUpperExp γ := h1
      _ = (4 : ℝ) ^ lsoUpperExp γ * (r ^ (lsoUpperExp γ / 2) * r ^ (lsoUpperExp γ / 2)) := by
        rw [h2, h3]
      _ = ((4 : ℝ) ^ lsoUpperExp γ * r ^ (lsoUpperExp γ / 2)) * r ^ (lsoUpperExp γ / 2) := by ring
      _ ≤ 1 * r ^ (lsoUpperExp γ / 2) := mul_le_mul_of_nonneg_right hk4 hpos.le
      _ = r ^ (lsoUpperExp γ / 2) := one_mul _
  refine ⟨?_, ?_⟩
  · calc ENNReal.ofReal (r ^ (lsoLowerExp γ + 1))
        ≤ ENNReal.ofReal ((dyadicRad j) ^ lsoLowerExp γ) := ENNReal.ofReal_le_ofReal hlowR
      _ ≤ ν (ball c (dyadicRad j)) := hlow
      _ = ν.restrict (closedBall (0 : ℂ) (7 / 8)) (ball c (dyadicRad j)) := heqj.symm
      _ ≤ ν.restrict (closedBall (0 : ℂ) (7 / 8)) (ball z r) := measure_mono hsub1
  · calc ν.restrict (closedBall (0 : ℂ) (7 / 8)) (ball z r)
        ≤ ν.restrict (closedBall (0 : ℂ) (7 / 8)) (ball c (dyadicRad k)) := measure_mono hsub2
      _ = ν (ball c (dyadicRad k)) := heqk
      _ ≤ ENNReal.ofReal ((dyadicRad k) ^ lsoUpperExp γ) := hup
      _ ≤ ENNReal.ofReal (r ^ (lsoUpperExp γ / 2)) := ENNReal.ofReal_le_ofReal hupR

/-! ## Deterministic membership: `lsoClass γ ⊆ {ν | LeastSuperOK ν}` -/

/-- Every measure of `lsoClass γ` satisfies `LeastSuperOK` (Section 5), from the frozen deterministic input
`LeastSupersolutionMemOfVolumeGrowthStmt` applied to the restriction `ν|B̄_{7/8}` (Section 4). -/
theorem lsoClass_leastSuperOK (hL : LeastSupersolutionMemOfVolumeGrowthStmt) {γ : ℝ} (hγ2 : γ < 2)
    {ν : Measure ℂ} (hν : ν ∈ lsoClass γ) : LeastSuperOK ν := by
  unfold LeastSuperOK
  intro s hs
  have hK : ν (closedBall (0 : ℂ) (7 / 8)) < ⊤ := hν.1
  have : IsFiniteMeasure (ν.restrict (closedBall (0 : ℂ) (7 / 8))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK⟩
  have hUK : ball (0 : ℂ) (3 / 4) ⊆ closedBall (0 : ℂ) (7 / 8) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hmem := hL (ν.restrict (closedBall (0 : ℂ) (7 / 8))) inferInstance _ _
    (volumeGrowth_restrict_of_mem hγ2 hν) s hs
  rw [leastSupersolution_restrict hUK, supersolutions_restrict hUK] at hmem
  exact hmem

/-! ## Cone measures lie in `lsoClass γ` almost surely (Section 3) -/

/-- The good event at radius `δ` of `VolumeGrowthStmt` (Lemma 2.7) for the exponents of the class: every `z` of
`B_{1-δ}` carries the two-sided bounds at radius `δ`. -/
def lsoRadiusGood {Ω : Type} (γ : ℝ) (μ : Ω → Measure ℂ) (δ : ℝ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ lsoLowerExp γ) ≤ μ ω (ball z δ) ∧
    μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ lsoUpperExp γ)}

/-- A cone measure lies in `lsoClass γ` almost surely (Section 3): `VolumeGrowthStmt` gives polynomially high
probability of the radius-`2^{-n}` bounds, Borel-Cantelli (`ae_eventually_notMem`) gives them for all large `n`, and
local finiteness gives `μ(B̄_{7/8}) < ∞` almost surely. -/
theorem ae_mem_lsoClass (hV : VolumeGrowthStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) : ∀ᵐ ω ∂P, μ ω ∈ lsoClass γ := by
  have hup : lsoUpperExp γ < (2 - γ) ^ 2 / 2 := lsoUpperExp_lt hγ2
  have hPHP : PolyHighProb P (lsoRadiusGood γ μ) :=
    hV γ hγ hγ2 (lsoUpperExp γ) (lsoLowerExp γ) (lsoUpperExp_pos hγ2) hup (lsoLowerExp_gt γ) Ω P hC hcirc μ
      hcone
  unfold PolyHighProb at hPHP
  obtain ⟨p, hp, C, r₀, hr₀, hbd⟩ := hPHP
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hr₀ (show (1 / 2 : ℝ) < 1 by norm_num)
  set ρ : ℝ := (1 / 2 : ℝ) ^ p with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) p
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hterm : ∀ k : ℕ, P (lsoRadiusGood γ μ (dyadicRad (k + n0)))ᶜ ≤
      ENNReal.ofReal (|C| * ρ ^ n0 * ρ ^ k) := by
    intro k
    have hr : dyadicRad (k + n0) < r₀ :=
      lt_of_le_of_lt (dyadicRad_anti (show n0 ≤ k + n0 by omega)) hn0
    refine (hbd _ (dyadicRad_pos _) hr).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [dyadicRad_rpow, ← hρ]
    have hX : 0 ≤ ρ ^ (k + n0) := pow_nonneg hρ0.le _
    calc C * ρ ^ (k + n0) ≤ |C| * ρ ^ (k + n0) := mul_le_mul_of_nonneg_right (le_abs_self C) hX
      _ = |C| * ρ ^ n0 * ρ ^ k := by rw [pow_add]; ring
  have hsum : Summable (fun k : ℕ => |C| * ρ ^ n0 * ρ ^ k) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hfin : ∑' k : ℕ, P (lsoRadiusGood γ μ (dyadicRad (k + n0)))ᶜ ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc ∑' k : ℕ, P (lsoRadiusGood γ μ (dyadicRad (k + n0)))ᶜ
        ≤ ∑' k : ℕ, ENNReal.ofReal (|C| * ρ ^ n0 * ρ ^ k) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' k : ℕ, |C| * ρ ^ n0 * ρ ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun k => mul_nonneg (mul_nonneg (abs_nonneg C) (pow_nonneg hρ0.le _)) (pow_nonneg hρ0.le _))
          hsum).symm
  have hbc := ae_eventually_notMem (s := fun k : ℕ => (lsoRadiusGood γ μ (dyadicRad (k + n0)))ᶜ) hfin
  have hL : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  have hfinite : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (7 / 8)) < ⊤ := by
    filter_upwards [hL] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact (isCompact_closedBall (0 : ℂ) (7 / 8)).measure_lt_top
  filter_upwards [hbc, hfinite] with ω hω hωfin
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  show μ ω (closedBall (0 : ℂ) (7 / 8)) < ⊤ ∧
    ∃ m : ℕ, 6 ≤ m ∧ ∀ n : ℕ, m ≤ n → ∀ q : RatCentreIdx, lsoBound γ n q (μ ω)
  refine ⟨hωfin, max 6 (N + n0), le_max_left _ _, fun n hn q => ?_⟩
  have hn6 : 6 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N + n0 ≤ n := le_trans (le_max_right _ _) hn
  have hωn : ω ∈ lsoRadiusGood γ μ (dyadicRad n) := by
    have h := hN (n - n0) (by omega)
    rw [Nat.sub_add_cancel (by omega : n0 ≤ n)] at h
    simpa using h
  have hωn2 : ∀ z ∈ ball (0 : ℂ) (1 - dyadicRad n), ENNReal.ofReal (dyadicRad n ^ lsoLowerExp γ) ≤
      μ ω (ball z (dyadicRad n)) ∧ μ ω (ball z (dyadicRad n)) ≤ ENNReal.ofReal (dyadicRad n ^ lsoUpperExp γ) :=
    hωn
  have hd := dyadicRad_le_of_six_le hn6
  have hz : ratCentre q.1 ∈ ball (0 : ℂ) (1 - dyadicRad n) := by
    rw [mem_ball_zero_iff]
    have := q.2
    linarith
  exact hωn2 (ratCentre q.1) hz

end MatedCRT
