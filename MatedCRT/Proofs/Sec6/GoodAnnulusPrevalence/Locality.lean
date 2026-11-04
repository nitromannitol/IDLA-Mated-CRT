import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.ConeTransfer
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.EventCountable
import MatedCRT.Proofs.Sec6.AnnulusHit.EventInvariance

/-!
# `E_r(z)` is a.s. determined by `h|_{𝔸_{r/3,3r}(z)}` modulo additive constant (IR-c4-6)

Lines 2388-2390 of the proof of Lemma 6.4: `E_r(z)` depends only on `μ_h` restricted to `U = 𝔸_{r/3,3r}(z)` and is
unchanged when `μ_h` is multiplied by a constant; by locality and Weyl scaling it is therefore a.s. determined by `h|_U`
modulo additive constant. The proof here goes through the definition of `μ_h` as the circle-average limit
(`IsLQGMeasure`, `IsLQGLimit`):

* `E_r(z)` for `m` is a measurable condition on countably many integrals `∫ g_j dm`, `g_j` continuous with compact support
  in `U` (`AnnulusEventCountable.isGoodAnnulusEvent_iff_criterion`), and it is unchanged under `m ↦ c m`
  (`isGoodAnnulusEvent_smul_iff`); take `c = e^{-γ h_{s₀}(y₀)}` for a fixed circle in `U`;
* `∫ g d(e^{-γ h_{s₀}(y₀)} μ_h) = lim_k ∫ g(x) ε_k^{γ²/2} e^{γ (h_{ε_k}(x) - h_{s₀}(y₀))} dx` (`IsLQGLimit`), and the
  differences `h_{ε_k}(x) - h_{s₀}(y₀)` are a.s. determined by `h|_U` modulo additive constant
  (`CircleAverageModConstStep`), at countably many dyadic points; the a.s. continuity of the circle average process
  gives a jointly measurable version (`gridVersion`), whose integrals are measurable (`ae_eq_integral_smul`).
-/

namespace MatedCRT

namespace AnnulusLocality

open MeasureTheory ProbabilityTheory Filter Set Metric Topology HarmonicBalls
open scoped ENNReal

/-! ### Dyadic grids -/

/-- The dyadic grid point `(a₁ + a₂ i)/2^j`. -/
noncomputable def gridPt (j : ℕ) (a : ℤ × ℤ) : ℂ := ⟨(a.1 : ℝ) / 2 ^ j, (a.2 : ℝ) / 2 ^ j⟩

/-- The index of the dyadic square of side `2^{-j}` containing `x`. -/
noncomputable def gridIdx (j : ℕ) (x : ℂ) : ℤ × ℤ := (⌊2 ^ j * x.re⌋, ⌊2 ^ j * x.im⌋)

lemma measurable_gridIdx (j : ℕ) : Measurable (gridIdx j) :=
  (Int.measurable_floor.comp (measurable_const.mul Complex.measurable_re)).prodMk
    (Int.measurable_floor.comp (measurable_const.mul Complex.measurable_im))

lemma abs_floor_div_sub_le (j : ℕ) (t : ℝ) : |(⌊2 ^ j * t⌋ : ℝ) / 2 ^ j - t| ≤ 1 / 2 ^ j := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have e : (⌊2 ^ j * t⌋ : ℝ) / 2 ^ j - t = ((⌊2 ^ j * t⌋ : ℝ) - 2 ^ j * t) / 2 ^ j := by
    field_simp
  rw [e, abs_div, abs_of_pos hp]
  refine div_le_div_of_nonneg_right ?_ hp.le
  rw [abs_le]
  constructor <;> linarith [Int.floor_le (2 ^ j * t), Int.lt_floor_add_one (2 ^ j * t)]

lemma dist_gridPt_le (j : ℕ) (x : ℂ) : dist (gridPt j (gridIdx j x)) x ≤ 2 / 2 ^ j := by
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 := abs_floor_div_sub_le j x.re
  have h2 := abs_floor_div_sub_le j x.im
  have e : (2 : ℝ) / 2 ^ j = 1 / 2 ^ j + 1 / 2 ^ j := by ring
  rw [e]
  exact add_le_add h1 h2

lemma tendsto_gridPt (x : ℂ) : Tendsto (fun j => gridPt j (gridIdx j x)) atTop (𝓝 x) := by
  have h : Tendsto (fun j : ℕ => (2 : ℝ) / 2 ^ j) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul 2
    rw [mul_zero] at this
    refine this.congr fun j => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun j => dist_gridPt_le j x) h)

/-! ### A jointly measurable version from countably many random variables -/

/-- `limsup_j V(q_j(x))`, `q_j(x)` the dyadic grid point of `x` at level `j`. -/
noncomputable def gridVersion {Ω : Type*} (V : ℂ → Ω → ℝ) (ω : Ω) (x : ℂ) : ℝ :=
  limsup (fun j => V (gridPt j (gridIdx j x)) ω) atTop

lemma measurable_gridVersion {Ω : Type*} [m : MeasurableSpace Ω] {V : ℂ → Ω → ℝ} (hV : ∀ p, Measurable (V p)) :
    Measurable (Function.uncurry (gridVersion V)) := by
  have hj : ∀ j : ℕ, Measurable fun p : Ω × ℂ => V (gridPt j (gridIdx j p.2)) p.1 := by
    intro j
    have hW : Measurable fun q : Ω × (ℤ × ℤ) => V (gridPt j q.2) q.1 :=
      measurable_from_prod_countable_left fun a => hV (gridPt j a)
    exact hW.comp (measurable_fst.prodMk ((measurable_gridIdx j).comp measurable_snd))
  exact Measurable.limsup hj

lemma measurable_integral_gridVersion {Ω : Type*} [m : MeasurableSpace Ω] {V : ℂ → Ω → ℝ}
    (hV : ∀ p, Measurable (V p)) {g : ℂ → ℝ} (hg : Continuous g) (a b : ℝ) :
    Measurable fun ω => ∫ x, g x * (a * Real.exp (b * gridVersion V ω x)) := by
  have h : StronglyMeasurable (Function.uncurry fun ω x => g x * (a * Real.exp (b * gridVersion V ω x))) :=
    Measurable.stronglyMeasurable ((hg.measurable.comp measurable_snd).mul (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_gridVersion hV)))))
  exact h.integral_prod_right.measurable

lemma measurable_limsup_of {Ω : Type*} [m : MeasurableSpace Ω] {I : ℕ → Ω → ℝ} (hI : ∀ k, Measurable (I k)) :
    Measurable fun ω => limsup (fun k => I k ω) atTop :=
  Measurable.limsup hI

lemma measurable_pi_of {Ω ι : Type*} [m : MeasurableSpace Ω] {Y : ι → Ω → ℝ} (hY : ∀ j, Measurable (Y j)) :
    Measurable fun ω j => Y j ω :=
  Measurable.of_eval hY

/-! ### Integrals against `e^{-γ h_{s₀}(y₀)} μ_h` -/

/-- **One test function.** For `g` continuous with compact support in `U`, the integral
`∫ g d(e^{-γ h_{s₀}(y₀)} μ_h)` is a.s. equal to a random variable determined by `h|_U` modulo additive constant. -/
theorem ae_eq_integral_smul {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hcone : IsConeField γ P hC hcirc μ)
    (hD : CircleAverageModConstStep) {U : Set ℂ} (hU : IsOpen U) (hU1 : U ⊆ ball 0 1)
    {s₀ : ℝ} {y₀ : ℂ} (hs₀ : 0 < s₀) (hy₀ : closedBall y₀ s₀ ⊆ U)
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    ∃ Y : Ω → ℝ, Measurable[modConstSigma hC U] Y ∧
      ∀ᵐ ω ∂P, ∫ u, g u ∂(ENNReal.ofReal (Real.exp (-γ * hcirc ω s₀ y₀)) • μ ω) = Y ω := by
  have hPprob : IsProbabilityMeasure P := hcone.1
  have hcq : IsQuantumCone γ P hC hcirc := hcone.2.1
  obtain ⟨δ, hδ, hδU⟩ := IsCompact.exists_cthickening_subset_open hgc hU hgU
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (2 : ℝ)⁻¹ ^ k₀ < δ / 2 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  -- the scales `ε_k = 2^{-(k + k₀)}`
  set ε : ℕ → ℝ := fun k => dyadicScale (k + k₀) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by
    simp only [hεdef, dyadicScale]
    positivity
  have hεδ : ∀ k, ε k < δ / 2 := fun k => by
    simp only [hεdef, dyadicScale]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k₀ k)).trans_lt hk₀
  -- versions of the circle-average differences
  have hV : ∀ (k : ℕ) (p : ℂ), ∃ V : Ω → ℝ, Measurable[modConstSigma hC U] V ∧
      (closedBall p (ε k) ⊆ U → (fun ω => hcirc ω (ε k) p - hcirc ω s₀ y₀) =ᵐ[P] V) := by
    intro k p
    by_cases hp : closedBall p (ε k) ⊆ U
    · obtain ⟨D, hDm, hDe⟩ := hD γ hγ hγ2 Ω P hC hcirc hPprob hcq U hU hU1 (ε k) s₀ p y₀ (hε k) hs₀ hp hy₀
      exact ⟨D, hDm, fun _ => hDe⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h hp⟩
  choose V hVm hVe using hV
  let I : ℕ → Ω → ℝ := fun k ω =>
    ∫ x, g x * ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * gridVersion (V k) ω x))
  refine ⟨fun ω => limsup (fun k => I k ω) atTop, ?_, ?_⟩
  · exact measurable_limsup_of (m := modConstSigma hC U) (I := I) (fun k =>
      measurable_integral_gridVersion (m := modConstSigma hC U) (hVm k) hg _ _)
  -- the good event
  have h3 : ∀ᵐ ω ∂P, ∀ (k j : ℕ) (a : ℤ × ℤ), closedBall (gridPt j a) (ε k) ⊆ U →
      V k (gridPt j a) ω = hcirc ω (ε k) (gridPt j a) - hcirc ω s₀ y₀ := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun j => ae_all_iff.2 fun a => ?_
    by_cases hp : closedBall (gridPt j a) (ε k) ⊆ U
    · filter_upwards [hVe k _ hp] with ω hω _
      exact hω.symm
    · exact Eventually.of_forall fun ω h => absurd h hp
  have hlqg : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  filter_upwards [hlqg, hcq.ae_continuousOn_circle, h3] with ω hlim hcont hgrid
  set H₀ := hcirc ω s₀ y₀ with hH₀
  have hcx : ∀ k, Continuous fun x => hcirc ω (ε k) x := fun k =>
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨mem_Ioi.2 (hε k), mem_univ x⟩
  -- the version agrees with the differences on `tsupport g`
  have hver : ∀ k, ∀ x ∈ tsupport g, gridVersion (V k) ω x = hcirc ω (ε k) x - H₀ := by
    intro k x hx
    have hq := tendsto_gridPt x
    have hev : ∀ᶠ j in atTop, hcirc ω (ε k) (gridPt j (gridIdx j x)) - H₀ = V k (gridPt j (gridIdx j x)) ω := by
      have hsmall : ∀ᶠ j in atTop, dist (gridPt j (gridIdx j x)) x < δ / 2 :=
        (tendsto_iff_dist_tendsto_zero.1 hq).eventually (gt_mem_nhds (by positivity))
      filter_upwards [hsmall] with j hj
      refine (hgrid k j _ fun y hy => hδU ?_).symm
      refine mem_cthickening_of_dist_le y x δ _ hx ?_
      have := dist_triangle y (gridPt j (gridIdx j x)) x
      rw [mem_closedBall] at hy
      linarith [hεδ k]
    have ht : Tendsto (fun j => V k (gridPt j (gridIdx j x)) ω) atTop (𝓝 (hcirc ω (ε k) x - H₀)) :=
      Tendsto.congr' hev ((((hcx k).tendsto x).comp hq).sub_const H₀)
    exact ht.limsup_eq
  -- the integrals of the version are the rescaled approximations of `μ_h`
  have hI : ∀ k, I k ω = Real.exp (-γ * H₀) * ∫ x, g x ∂(lqgApprox γ (hcirc ω) (ε k)) := by
    intro k
    have hmeas : Measurable fun x => ENNReal.ofReal ((ε k) ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (ε k) x)) :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcx k)))).measurable.ennreal_ofReal
    rw [lqgApprox, integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport g
    · simp only [hver k x hx, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (hε k).le _) (Real.exp_pos _).le),
        show γ * (hcirc ω (ε k) x - H₀) = γ * hcirc ω (ε k) x + -γ * H₀ by ring, Real.exp_add]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, smul_zero, mul_zero]
  have hlimk : Tendsto (fun k => I k ω) atTop (𝓝 (Real.exp (-γ * H₀) * ∫ x, g x ∂(μ ω))) := by
    have h := ((hlim.tendsto_integral g hg hgc).comp (tendsto_add_atTop_nat k₀)).const_mul
      (Real.exp (-γ * H₀))
    exact Tendsto.congr (fun k => (hI k).symm) h
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  exact hlimk.limsup_eq.symm

lemma isLocallyFiniteMeasure_smul {m : Measure ℂ} [IsLocallyFiniteMeasure m] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    IsLocallyFiniteMeasure (c • m) :=
  ⟨fun x => by
    obtain ⟨s, hs, hfin⟩ := m.finiteAt_nhds x
    exact ⟨s, hs, by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top hc.lt_top hfin⟩⟩

end AnnulusLocality

open MeasureTheory ProbabilityTheory Filter Set Metric Topology HarmonicBalls
open scoped ENNReal

open AnnulusLocality AnnulusEventCountable in
/-- **`E_r(z)` is a.s. determined by `h|_{𝔸_{r/3,3r}(z)}` modulo additive constant** (IR-c4-6), from the definition
of `μ_h` as the circle-average limit and `CircleAverageModConstStep`. -/
theorem goodAnnulusEventLocality (hD : CircleAverageModConstStep) : GoodAnnulusEventLocalityStep := by
  intro γ hγ hγ2 c₀ hc₀ hc₀' C hCpos Ω _ P hC hcirc μ hcone r z hr hsub
  set U := annulus z (r / 3) (3 * r) with hUdef
  have hUo : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  -- the reference circle `∂B_{r/2}(z + 2r)`
  set y₀ : ℂ := z + ((2 * r : ℝ) : ℂ) with hy₀def
  have hy₀z : dist y₀ z = 2 * r := by
    rw [hy₀def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hy₀ : closedBall y₀ (r / 2) ⊆ U := by
    intro x hx
    rw [mem_closedBall] at hx
    have t1 := dist_triangle x y₀ z
    have t2 := dist_triangle y₀ x z
    rw [dist_comm y₀ x] at t2
    refine ⟨mem_ball.2 (by linarith), fun h => ?_⟩
    rw [mem_closedBall] at h
    linarith
  -- the countable criterion and a.s. versions of its integrals
  have hY : ∀ j : Index, ∃ Y : Ω → ℝ, Measurable[modConstSigma hC U] Y ∧
      ∀ᵐ ω ∂P, ∫ u, testFn z r c₀ j u ∂(ENNReal.ofReal (Real.exp (-γ * hcirc ω (r / 2) y₀)) • μ ω) = Y ω := by
    intro j
    obtain ⟨hgc, hgcs, hgU⟩ := testFn_properties (c₀ := c₀) hr z j
    exact ae_eq_integral_smul hγ hγ2 hcone hD hUo hsub (by positivity) hy₀ hgc hgcs hgU
  choose Y hYm hYe using hY
  have hYmeas : Measurable[modConstSigma hC U] fun ω j => Y j ω := measurable_pi_of (m := modConstSigma hC U) hYm
  refine ⟨(fun ω j => Y j ω) ⁻¹' criterion z r C, hYmeas (measurableSet_criterion z r C), ?_⟩
  have hlqg : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_all_iff.2 hYe, hlqg] with ω hω hlim
  have : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-γ * hcirc ω (r / 2) y₀)) with hcdef
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have : IsLocallyFiniteMeasure (c • μ ω) := isLocallyFiniteMeasure_smul hctop
  show IsGoodAnnulusEvent (μ ω) c₀ C r z ↔ (fun j => Y j ω) ∈ criterion z r C
  rw [← isGoodAnnulusEvent_smul_iff hc0 hctop, isGoodAnnulusEvent_iff_criterion hr hc₀' C z (c • μ ω)]
  have hfun : (fun j => ∫ u, testFn z r c₀ j u ∂(c • μ ω)) = fun j => Y j ω := funext hω
  rw [hfun]

/-- **Lemma 6.4 from Lemmas 6.5, 6.6 and the two field steps** (proof lines 2387-2400): eq:gff on mean-zero pairings
(`ConeMeanZeroRestrictionStep`) and the determination of circle-average differences modulo additive constant
(`CircleAverageModConstStep`). -/
theorem goodAnnulusPrevalence_of_fieldSteps (h66 : AnnulusIterateStmt) (h65 : AnnulusHitStmt)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_restriction h66 h65 hR (goodAnnulusEventLocality hD)

end MatedCRT
