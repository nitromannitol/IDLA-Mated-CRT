import MatedCRT.FirstPass.S4S6c.Lemma1Mass

/-!
# Lemma 1 of the Lemma 6.8 argument: the kernel bound on subsets (q2, task fp-S4S6c; LEMMA68 eq (5))

For `0 < R ≤ 1`, a measurable annulus `A ⊆ closedBall z (2R)` of finite `μ`-mass, a measurable `E ⊆ A` and `v ∈ A`:
`∫_E (log(R/|u-v|) + 1 + log(1/R)) dμ(u) ≤ C m (1 + a₀)(1 + log(1/R)) / κ₀`, with `a₀ = log 4 - 1`, `κ₀ = 1 - log 2`.
This is LEMMA68 eq (5) with the constant `C₁ = C (1+a₀)/κ₀`: the integrand is the paper's `log(1/|u-v|) + 1` up to the
diagonal `u = v`, where the paper's kernel is `+∞` (the diagonal is `μ`-null once `F(v)` is finite; not formalized here).
Proof: split `∫_A = ∫_E + ∫_{A∖E}`; the kernel is `≥ -a₀` on `A` (`|u-v| ≤ 4R`); `F(v) ≤ C m` by hypothesis (4) at `v`;
the mass bound `κ₀ μ(A) ≤ C m` of `Lemma1Mass`; and the elementary algebra `kernel_E_algebra`.
Hypotheses: `hint` (finiteness of `F(v)` on `A`, presupposed by (4)) and `hF` (the good-annulus bound (4) for all `v ∈ A`).
-/

open MeasureTheory Real Set Metric

namespace MatedCRT

/-- Elementary algebra of the final step of eq (5). -/
theorem kernel_E_algebra {X Cm M κ a L : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hCm : 0 ≤ Cm) (hM : κ * M ≤ Cm) (hX : X ≤ Cm + a * M + L * M) :
    X ≤ Cm * (1 + a) * (1 + L) / κ := by
  rw [le_div_iff₀ hκ]
  have h1 : X * κ ≤ (Cm + a * M + L * M) * κ := mul_le_mul_of_nonneg_right hX hκ.le
  have h2 : (a + L) * (κ * M) ≤ (a + L) * Cm := mul_le_mul_of_nonneg_left hM (add_nonneg ha hL)
  have h3 : Cm * κ ≤ Cm := by nlinarith
  have h4 : 0 ≤ Cm * (a * L) := mul_nonneg hCm (mul_nonneg ha hL)
  nlinarith [h1, h2, h3, h4]

/-- **Kernel bound on subsets of the annulus** (LEMMA68 eq (5)). -/
theorem lemma1_kernel_bound_E {A E : Set ℂ} (μ : Measure ℂ) [SFinite μ] {z v : ℂ} {R C m : ℝ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hA : MeasurableSet A) (hAb : A ⊆ closedBall z (2 * R)) (hμA : μ A ≠ ⊤)
    (hsph : sphere z (3 * R / 2) ⊆ A) (hE : MeasurableSet E) (hEA : E ⊆ A)
    (hC : 0 ≤ C) (hm : 0 ≤ m) (hv : v ∈ A)
    (hint : IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) A μ)
    (hF : ∀ w ∈ A, ∫ u in A, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ C * m) :
    ∫ u in E, (Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R)) ∂μ ≤
      C * m * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2) := by
  have hmass := lemma1_mass_le μ hR0 hA hAb hμA hC hm (fun w hw => hF w (hsph hw))
  have hκ : 0 < 1 - Real.log 2 := by
    have h2 : Real.log 2 < 2 - 1 := Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
    linarith
  have hκ1 : 1 - Real.log 2 ≤ 1 := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have ha0 : 0 ≤ Real.log 4 - 1 := by linarith [one_le_log_four]
  have hL : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR0 hR1)
  -- the kernel is bounded below by `-(log 4 - 1)` on the annulus (`|u - v| ≤ 4R`)
  have hpair : ∀ u ∈ A, ‖u - v‖ ≤ 4 * R := by
    intro u hu
    have h1 : dist u z ≤ 2 * R := hAb hu
    have h2 : dist v z ≤ 2 * R := hAb hv
    have htri := dist_triangle u z v
    rw [dist_comm z v] at htri
    simp only [dist_eq_norm] at htri h1 h2
    linarith
  have hK_lb : ∀ u ∈ A, -(Real.log 4 - 1) ≤ Real.log (R / ‖u - v‖) + 1 :=
    fun u hu => kernel_ge_neg (hpair u hu)
  have hμD : μ (A \ E) ≠ ⊤ := ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)
  have hlow : -(Real.log 4 - 1) * (μ (A \ E)).toReal ≤
      ∫ u in A \ E, (Real.log (R / ‖u - v‖) + 1) ∂μ := by
    have h := setIntegral_mono_on (integrableOn_const hμD) (hint.mono_set sdiff_subset) (hA.diff hE)
      (fun u hu => hK_lb u hu.1)
    simp only [setIntegral_const, smul_eq_mul, Measure.real] at h
    linarith
  have hsplit : ∫ u in E, (Real.log (R / ‖u - v‖) + 1) ∂μ + ∫ u in A \ E, (Real.log (R / ‖u - v‖) + 1) ∂μ =
      ∫ u in A, (Real.log (R / ‖u - v‖) + 1) ∂μ := by
    have h := integral_inter_add_sdiff (μ := μ) (f := fun u : ℂ => Real.log (R / ‖u - v‖) + 1) hE hint
    rwa [Set.inter_eq_right.2 hEA] at h
  have hFv : ∫ u in A, (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ C * m := hF v hv
  have hμE_le : (μ E).toReal ≤ (μ A).toReal := ENNReal.toReal_mono hμA (measure_mono hEA)
  have hμD_le : (μ (A \ E)).toReal ≤ (μ A).toReal := ENNReal.toReal_mono hμA (measure_mono sdiff_subset)
  have hK_E : IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) E μ := hint.mono_set hEA
  have hfin : ∫ u in E, (Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R)) ∂μ =
      ∫ u in E, (Real.log (R / ‖u - v‖) + 1) ∂μ + Real.log (1 / R) * (μ E).toReal := by
    rw [integral_add hK_E (integrableOn_const (ne_top_of_le_ne_top hμA (measure_mono hEA)))]
    simp only [setIntegral_const, smul_eq_mul, Measure.real]
    ring
  -- `∫_E K ≤ C m + a₀ μ(A)`
  have hXle : ∫ u in E, (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ C * m + (Real.log 4 - 1) * (μ A).toReal := by
    have h5 := mul_le_mul_of_nonneg_left hμD_le ha0
    linarith
  have hLM : Real.log (1 / R) * (μ E).toReal ≤ Real.log (1 / R) * (μ A).toReal :=
    mul_le_mul_of_nonneg_left hμE_le hL
  have hT : ∫ u in E, (Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R)) ∂μ ≤
      C * m + (Real.log 4 - 1) * (μ A).toReal + Real.log (1 / R) * (μ A).toReal := by
    rw [hfin]
    linarith
  exact kernel_E_algebra hκ hκ1 ha0 hL (mul_nonneg hC hm) hmass hT

end MatedCRT
