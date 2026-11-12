import MatedCRT.FirstPass.Derived.ConeScaleRadiusDecoder

/-!
# The rescaled circle average process is a measurable function of the circle average process and the radius

For `R > 0`, the circle averages of the rescaled field `h(R ·) + Q log R - γ⁻¹ log b` are
`(r, z) ↦ h_{Rr}(Rz) + Q log R - γ⁻¹ log b` (`rescaledCircle`).  On the product σ-algebra of
`(0, ∞) × ℂ → ℝ` the evaluation at the random point `(Rr, Rz)` is not measurable in `(x, R)`, but for a
process continuous on `(0, ∞) × ℂ` it is the limit of the evaluations at the dyadic upper approximations of
`(Rr, Rz)`, each of which is a measurable function of `(x, R)` (the approximation point ranges over a countable
set).  The limit is taken through `ENNReal.ofReal ∘ exp` and `liminf`, which is measurable.
-/

open MeasureTheory Filter Topology Set HarmonicBalls
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The dyadic upper approximation `⌈2ⁿ t⌉ / 2ⁿ` of `t`. -/
noncomputable def ceilGrid (n : ℕ) (t : ℝ) : ℝ := (⌈(2 : ℝ) ^ n * t⌉ : ℝ) / 2 ^ n

theorem le_ceilGrid (n : ℕ) (t : ℝ) : t ≤ ceilGrid n t := by
  unfold ceilGrid
  rw [le_div_iff₀ (by positivity)]
  have := Int.le_ceil ((2 : ℝ) ^ n * t)
  linarith

theorem ceilGrid_le (n : ℕ) (t : ℝ) : ceilGrid n t ≤ t + (1 / 2) ^ n := by
  unfold ceilGrid
  rw [div_le_iff₀ (by positivity)]
  have h1 := Int.ceil_lt_add_one ((2 : ℝ) ^ n * t)
  have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]; norm_num
  nlinarith

theorem tendsto_ceilGrid (t : ℝ) : Tendsto (fun n => ceilGrid n t) atTop (𝓝 t) := by
  have h0 : Tendsto (fun n : ℕ => t + ((1 : ℝ) / 2) ^ n) atTop (𝓝 (t + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [add_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun n => le_ceilGrid n t) (fun n => ceilGrid_le n t)

/-- The evaluation of the extended process at the dyadic upper approximation of `(R r, R z)`. -/
noncomputable def gridEval (n : ℕ) (x : Ioi (0 : ℝ) × ℂ → ℝ) (R r : ℝ) (z : ℂ) : ℝ :=
  extendCircle x (ceilGrid n (R * r)) ⟨ceilGrid n (R * z.re), ceilGrid n (R * z.im)⟩

theorem measurable_gridEval (n : ℕ) (r : ℝ) (z : ℂ) :
    Measurable fun q : (Ioi (0 : ℝ) × ℂ → ℝ) × ℝ => gridEval n q.1 q.2 r z := by
  have hk : Measurable fun q : (Ioi (0 : ℝ) × ℂ → ℝ) × (ℤ × ℤ × ℤ) =>
      extendCircle q.1 ((q.2.1 : ℝ) / 2 ^ n) ⟨(q.2.2.1 : ℝ) / 2 ^ n, (q.2.2.2 : ℝ) / 2 ^ n⟩ := by
    apply measurable_from_prod_countable_left
    intro k
    by_cases h : 0 < (k.1 : ℝ) / 2 ^ n
    · simp only [extendCircle, h, dite_true]
      exact measurable_pi_apply ((⟨(k.1 : ℝ) / 2 ^ n, h⟩ : Ioi (0 : ℝ)),
        (⟨(k.2.1 : ℝ) / 2 ^ n, (k.2.2 : ℝ) / 2 ^ n⟩ : ℂ))
    · simp only [extendCircle, h, dite_false]
      exact measurable_const
  have hc : Measurable fun q : (Ioi (0 : ℝ) × ℂ → ℝ) × ℝ =>
      (q.1, (⌈(2 : ℝ) ^ n * (q.2 * r)⌉, ⌈(2 : ℝ) ^ n * (q.2 * z.re)⌉, ⌈(2 : ℝ) ^ n * (q.2 * z.im)⌉)) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))
    · exact Int.measurable_ceil.comp (measurable_const.mul (measurable_snd.mul measurable_const))
    · exact Int.measurable_ceil.comp (measurable_const.mul (measurable_snd.mul measurable_const))
    · exact Int.measurable_ceil.comp (measurable_const.mul (measurable_snd.mul measurable_const))
  exact hk.comp hc

theorem tendsto_gridEval {hc : ℝ → ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ)) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    Tendsto (fun n => gridEval n (circleProcess hc) R r z) atTop (𝓝 (hc (R * r) (R * z))) := by
  have hRr : 0 < R * r := mul_pos hR hr
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := isOpen_Ioi.prod isOpen_univ
  have hca : ContinuousAt (fun p : ℝ × ℂ => hc p.1 p.2) (R * r, (R : ℂ) * z) :=
    hcont.continuousAt (hopen.mem_nhds ⟨hRr, mem_univ _⟩)
  have hpt : Tendsto (fun n : ℕ => (ceilGrid n (R * r),
      (⟨ceilGrid n (R * z.re), ceilGrid n (R * z.im)⟩ : ℂ))) atTop (𝓝 (R * r, (R : ℂ) * z)) := by
    refine (tendsto_ceilGrid (R * r)).prodMk_nhds ?_
    have hz : (R : ℂ) * z = ((R * z.re : ℝ) : ℂ) + ((R * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hz]
    simp only [Complex.mk_eq_add_mul_I]
    exact (((Complex.continuous_ofReal.tendsto _).comp (tendsto_ceilGrid (R * z.re))).add
      (((Complex.continuous_ofReal.tendsto _).comp (tendsto_ceilGrid (R * z.im))).mul_const Complex.I))
  have := hca.tendsto.comp hpt
  refine this.congr fun n => ?_
  have hpos : 0 < ceilGrid n (R * r) := lt_of_lt_of_le hRr (le_ceilGrid n _)
  simp [gridEval, extendCircle, hpos, circleProcess]

/-- The decoder of the rescaled circle average process: `(x, R) ↦ ((r, z) ↦ lim x(Rr, Rz) + Q log R - γ⁻¹ log b)`,
the limit being taken along the dyadic upper approximations through `ENNReal.ofReal ∘ exp`. -/
noncomputable def rescaledCircleDecoder (γ b : ℝ) (q : (Ioi (0 : ℝ) × ℂ → ℝ) × ℝ) :
    Ioi (0 : ℝ) × ℂ → ℝ :=
  fun p => Real.log (ENNReal.toReal (Filter.liminf
    (fun n => ENNReal.ofReal (Real.exp (gridEval n q.1 q.2 p.1 p.2))) atTop)) +
    lqgQ γ * Real.log q.2 - γ⁻¹ * Real.log b

theorem measurable_rescaledCircleDecoder (γ b : ℝ) : Measurable (rescaledCircleDecoder γ b) := by
  refine measurable_pi_iff.2 fun p => ?_
  have h1 : Measurable fun q : (Ioi (0 : ℝ) × ℂ → ℝ) × ℝ => Filter.liminf
      (fun n => ENNReal.ofReal (Real.exp (gridEval n q.1 q.2 p.1 p.2))) atTop :=
    Measurable.liminf fun n => ((measurable_gridEval n p.1 p.2).exp).ennreal_ofReal
  exact ((Real.measurable_log.comp h1.ennreal_toReal).add
    (measurable_const.mul (Real.measurable_log.comp measurable_snd))).sub measurable_const

theorem rescaledCircleDecoder_circleProcess {γ b R : ℝ} {hc : ℝ → ℂ → ℝ} (hR : 0 < R)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ)) :
    rescaledCircleDecoder γ b (circleProcess hc, R) = circleProcess (rescaledCircle γ hc R b) := by
  funext p
  have hlim := ((ENNReal.continuous_ofReal.tendsto _).comp
    ((Real.continuous_exp.tendsto _).comp (tendsto_gridEval hR hcont p.1 p.1.2 p.2)))
  have hl : Filter.liminf (fun n => ENNReal.ofReal (Real.exp (gridEval n (circleProcess hc) R p.1 p.2))) atTop
      = ENNReal.ofReal (Real.exp (hc (R * p.1) (R * p.2))) := hlim.liminf_eq
  simp only [rescaledCircleDecoder, circleProcess, rescaledCircle]
  rw [hl, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

/-- **The circle averages of the rescaled field are a measurable function of the circle average process and of
the scale.** -/
theorem exists_measurable_rescaledCircle_decoder (γ b : ℝ) :
    ∃ ψ : ((Set.Ioi (0 : ℝ) × ℂ → ℝ) × ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ), Measurable ψ ∧
      ∀ (hc : ℝ → ℂ → ℝ) (R : ℝ), 0 < R →
        ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) →
        ψ (circleProcess hc, R) = circleProcess (rescaledCircle γ hc R b) :=
  ⟨rescaledCircleDecoder γ b, measurable_rescaledCircleDecoder γ b,
    fun _ _ hR hcont => rescaledCircleDecoder_circleProcess hR hcont⟩

end MatedCRT.FirstPass.Derived
