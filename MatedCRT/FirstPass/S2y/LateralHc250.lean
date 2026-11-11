import MatedCRT.FirstPass.S2y.LateralBilin250
import MatedCRT.FirstPass.S2y.LateralL2250

/-!
# The whole-plane pairing kernel and the L² limit of the pairing

For test functions `ψ, φ`: `E[(h(ψ) - h(φ))²] = ∬ (ψ-φ)(x)(ψ-φ)(y) wholePlaneCov x y dx dy` (Duplantier-Sheffield, Section
2.1, covariance `wholePlaneCov`), and this tends to `0` under the dominated convergence of `LateralL2250`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT.LQGMeasure

section Kernel

/-- A test function equal to `1` on a closed ball (a `ContDiffBump`). -/
lemma exists_test_one_on_ball (R : ℝ) :
    ∃ χ : ℂ → ℝ, IsTestFunction univ χ ∧ ∀ x ∈ closedBall (0 : ℂ) R, χ x = 1 := by
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := max R 0 + 1, rOut := max R 0 + 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport, subset_univ _⟩, fun x hx => b.one_of_mem_closedBall ?_⟩
  rw [mem_closedBall] at hx ⊢
  show dist x 0 ≤ max R 0 + 1
  linarith [le_max_left R 0]

/-- `wholePlaneCov x y = log M_x + log M_y - log ‖x - y‖` for `x ≠ y`, with `M_x = max ‖x‖ 1`. -/
lemma wholePlaneCov_eq {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log ‖x - y‖ := by
  have h1 : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  have h2 : 0 < max ‖y‖ 1 := lt_max_of_lt_right one_pos
  have h3 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold wholePlaneCov
  rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']

lemma wholePlaneCov_comm (x y : ℂ) : wholePlaneCov x y = wholePlaneCov y x := by
  unfold wholePlaneCov; rw [mul_comm, norm_sub_rev]

/-- The whole-plane kernel is integrable against a product of two test functions. -/
lemma integrable_prod_wholePlaneCov {f g : ℂ → ℝ} (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) := by
  obtain ⟨R₁, hR₁⟩ := exists_radius hf
  obtain ⟨R₂, hR₂⟩ := exists_radius hg
  have hf0 : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  have hg0 : Integrable g := hg.1.continuous.integrable_of_hasCompactSupport hg.2.1
  have hlogM : ∀ u : ℂ → ℝ, IsTestFunction univ u →
      Integrable (fun x => u x * Real.log (max ‖x‖ 1)) := by
    intro u hu
    have hc : Continuous fun x : ℂ => Real.log (max ‖x‖ 1) :=
      (continuous_norm.max continuous_const).log (fun x => (lt_max_of_lt_right one_pos).ne')
    exact (hu.1.continuous.mul hc).integrable_of_hasCompactSupport (hu.2.1.mul_right)
  have hfl := hlogM f hf
  have hgl := hlogM g hg
  have hlog : Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * Real.log ‖p.1 - p.2‖) (volume.prod volume) := by
    have h := integrable_uncurry_mul_logPotential hf hg (R := max R₁ R₂) (c := 1)
      (fun x hx => (hR₁ x hx).trans (le_max_left _ _)) (fun z hz => (hR₂ z hz).trans (le_max_right _ _))
      zero_le_one le_rfl
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, one_smul, mul_assoc]
  have hsum := ((Integrable.mul_prod hfl hg0).add (Integrable.mul_prod hf0 hgl)).sub hlog
  refine hsum.congr ?_
  have hae : ∀ᵐ p ∂(volume.prod volume : Measure (ℂ × ℂ)), p.1 ≠ p.2 := by
    rw [ae_iff]; simpa using diag_null
  filter_upwards [hae] with p hp
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [wholePlaneCov_eq hp]
  ring

/-- The whole-plane kernel is integrable on a square, through a test function equal to `1` on the ball. -/
lemma integrableOn_wholePlaneCov_square (R : ℝ) :
    IntegrableOn (fun p : ℂ × ℂ => wholePlaneCov p.1 p.2) (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R)
      (volume.prod volume) := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_test_one_on_ball R
  have hS : MeasurableSet (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
    measurableSet_closedBall.prod measurableSet_closedBall
  have hI := (integrable_prod_wholePlaneCov hχ hχ).indicator hS
  refine (integrable_indicator_iff hS).1 (hI.congr (Eventually.of_forall fun p => ?_))
  by_cases hp : p ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hp, indicator_of_mem hp, hχ1 p.1 hp.1, hχ1 p.2 hp.2]; ring
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

end Kernel

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- A pairing with a test function is square integrable. -/
lemma memLp_pairing (h : IsWholePlaneGFF P hC hcirc) {f : ℂ → ℝ} (hf : IsTestFunction univ f) :
    MemLp (fun ω => hC ω f) 2 P :=
  (MatedCRT.Field.wpSpace_gaussian h).memLp (Submodule.subset_span ⟨⟨GFFObservable.pairing f, hf⟩, rfl⟩)

/-- The iterated integral of `integral_mul_pairing` is the integral over the product. -/
lemma integral_iterated_eq_prod {f g : ℂ → ℝ} (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
    ∫ x, f x * ∫ y, g y * wholePlaneCov x y = ∫ p : ℂ × ℂ, f p.1 * g p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume) := by
  refine Eq.trans ?_ (integral_prod _ (integrable_prod_wholePlaneCov hf hg)).symm
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-- `E[(h(ψ) - h(φ))²] = ∬ (ψ-φ)(x)(ψ-φ)(y) wholePlaneCov x y dx dy` for test functions `ψ, φ`. -/
lemma integral_sq_pairing_sub [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {ψ φ : ℂ → ℝ}
    (hψ : IsTestFunction univ ψ) (hφ : IsTestFunction univ φ) :
    ∫ ω, (hC ω ψ - hC ω φ) ^ 2 ∂P =
      ∫ p : ℂ × ℂ, (ψ p.1 - φ p.1) * (ψ p.2 - φ p.2) * wholePlaneCov p.1 p.2 ∂(volume.prod volume) := by
  have hXψ := memLp_pairing h hψ
  have hXφ := memLp_pairing h hφ
  have hi_ψψ : Integrable (fun ω => hC ω ψ * hC ω ψ) P := by
    simpa only [sq] using hXψ.integrable_sq
  have hi_φφ : Integrable (fun ω => hC ω φ * hC ω φ) P := by
    simpa only [sq] using hXφ.integrable_sq
  have hbd : ∀ ω, ‖hC ω ψ * hC ω φ‖ ≤ (hC ω ψ * hC ω ψ + hC ω φ * hC ω φ) / 2 := fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (hC ω ψ), sq_abs (hC ω φ), sq_nonneg (|hC ω ψ| - |hC ω φ|),
      abs_nonneg (hC ω ψ), abs_nonneg (hC ω φ)]
  have hi_ψφ : Integrable (fun ω => hC ω ψ * hC ω φ) P :=
    Integrable.mono' ((hi_ψψ.add hi_φφ).div_const 2) (hXψ.aestronglyMeasurable.mul hXφ.aestronglyMeasurable)
      (Eventually.of_forall hbd)
  have hi_mix : Integrable (fun ω => 2 * (hC ω ψ * hC ω φ)) P := hi_ψφ.const_mul 2
  have hi_12 : Integrable (fun ω => hC ω ψ * hC ω ψ - 2 * (hC ω ψ * hC ω φ)) P := hi_ψψ.sub hi_mix
  have hexp : ∀ ω, (hC ω ψ - hC ω φ) ^ 2 =
      hC ω ψ * hC ω ψ - 2 * (hC ω ψ * hC ω φ) + hC ω φ * hC ω φ := fun ω => by ring
  have e1 : ∫ ω, (hC ω ψ - hC ω φ) ^ 2 ∂P = ∫ ω, (hC ω ψ * hC ω ψ - 2 * (hC ω ψ * hC ω φ)
      + hC ω φ * hC ω φ) ∂P := integral_congr_ae (Eventually.of_forall hexp)
  rw [e1, integral_add hi_12 hi_φφ, integral_sub hi_ψψ hi_mix, integral_const_mul,
    integral_mul_pairing h hψ hψ, integral_mul_pairing h hψ hφ, integral_mul_pairing h hφ hφ,
    integral_iterated_eq_prod hψ hψ, integral_iterated_eq_prod hψ hφ, integral_iterated_eq_prod hφ hφ]
  -- the mixed term is symmetric
  have hsym : ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume) =
      ∫ p : ℂ × ℂ, ψ p.1 * φ p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume) := by
    rw [integral_prod _ (integrable_prod_wholePlaneCov hφ hψ),
      integral_prod _ (integrable_prod_wholePlaneCov hψ hφ),
      integral_integral_swap (f := fun x y => φ x * ψ y * wholePlaneCov x y)
        (integrable_prod_wholePlaneCov hφ hψ)]
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only
    rw [wholePlaneCov_comm]; ring
  have i1 : Integrable (fun p : ℂ × ℂ => ψ p.1 * ψ p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) :=
    integrable_prod_wholePlaneCov hψ hψ
  have i2 : Integrable (fun p : ℂ × ℂ => φ p.1 * ψ p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) :=
    integrable_prod_wholePlaneCov hφ hψ
  have i3 : Integrable (fun p : ℂ × ℂ => ψ p.1 * φ p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) :=
    integrable_prod_wholePlaneCov hψ hφ
  have i4 : Integrable (fun p : ℂ × ℂ => φ p.1 * φ p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) :=
    integrable_prod_wholePlaneCov hφ hφ
  have i12 : Integrable (fun p : ℂ × ℂ => ψ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 -
      φ p.1 * ψ p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) := i1.sub i2
  have i123 : Integrable (fun p : ℂ × ℂ => ψ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 -
      φ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 - ψ p.1 * φ p.2 * wholePlaneCov p.1 p.2) (volume.prod volume) :=
    i12.sub i3
  have hR' : ∫ p : ℂ × ℂ, (ψ p.1 - φ p.1) * (ψ p.2 - φ p.2) * wholePlaneCov p.1 p.2 ∂(volume.prod volume) =
      ∫ p : ℂ × ℂ, ψ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume)
        - ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume)
        - ∫ p : ℂ × ℂ, ψ p.1 * φ p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume)
        + ∫ p : ℂ × ℂ, φ p.1 * φ p.2 * wholePlaneCov p.1 p.2 ∂(volume.prod volume) := by
    have e : ∀ p : ℂ × ℂ, (ψ p.1 - φ p.1) * (ψ p.2 - φ p.2) * wholePlaneCov p.1 p.2 =
        (ψ p.1 * ψ p.2 * wholePlaneCov p.1 p.2 - φ p.1 * ψ p.2 * wholePlaneCov p.1 p.2
          - ψ p.1 * φ p.2 * wholePlaneCov p.1 p.2) + φ p.1 * φ p.2 * wholePlaneCov p.1 p.2 :=
      fun p => by ring
    simp_rw [e]
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  rw [hR', hsym]
  ring

end L2

end MatedCRT.LQGMeasure
