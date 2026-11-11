import MatedCRT.FirstPass.S4S6c.Lemma1Kernel

/-!
# The potential supremum of the exit-moment bound from Lemma 1

with `D = B_{R/4}(x)`, `E = B_{ε^α}(D)`, `x` in the
annulus `A = A_{R,2R}(z)` and `E ⊂ A` (B6), the supremum over the centre `v ∈ D` of the log-potential integral of the
Draft Lemma 2.18 statement (`ExitTimeUpperBoundStmt`, `ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1)`) is at most the
Lemma 1 bound `C₁ (1 + log(1/R)) m`, with `C₁ = C (1 + (log 4 - 1)) / (1 - log 2)`.

The Draft kernel uses Lean's junk value `log (1/0) = 0` on the diagonal `u = v`, which is `1`; Lemma 1 is stated for the
integrand `log (R/|u - v|) + 1 + log(1/R)`, which is `1 + log(1/R) ≥ 1` on the diagonal. Off the diagonal the two
integrands are equal, so the Draft integrand is dominated pointwise and no atom-freeness of `μ` is needed.
Inputs: the good-annulus bound (4) of Lemma 1 (`hF`, with the mass `m` taken to be `m₀`), integrability of the log kernel on
`A` (`hint`), and the geometric bound `‖u - v‖ ≤ 1` on `E × D`.
-/

open MeasureTheory Real Set Metric

namespace MatedCRT

/-- **Pointwise sup bound on the thickened set** (one centre). For `v ∈ D ⊆ A` the Draft
kernel integral over `E` is at most the Lemma 1 bound. -/
theorem kernel_integral_le_of_annulus {A D E : Set ℂ} (μ : Measure ℂ) [SFinite μ] {z : ℂ} {R C m : ℝ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hA : MeasurableSet A) (hAb : A ⊆ closedBall z (2 * R)) (hμA : μ A ≠ ⊤)
    (hsph : sphere z (3 * R / 2) ⊆ A) (hE : MeasurableSet E) (hEA : E ⊆ A) (hDA : D ⊆ A)
    (hdist : ∀ u ∈ E, ∀ v ∈ D, ‖u - v‖ ≤ 1) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hint : ∀ v ∈ D, IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) A μ)
    (hF : ∀ w ∈ A, ∫ u in A, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ C * m)
    {v : ℂ} (hv : v ∈ D) :
    ∫⁻ u in E, ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ ≤
      ENNReal.ofReal (C * m * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2)) := by
  have hL := lemma1_kernel_bound_E μ hR0 hR1 hA hAb hμA hsph hE hEA hC hm (hDA hv) (hint v hv) hF
  have hlog1R : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR0 hR1)
  -- the Draft integrand is at most the Lemma 1 integrand at every point (equality off the diagonal)
  have hpt : ∀ u : ℂ, Real.log (1 / ‖v - u‖) + 1 ≤ Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R) := by
    intro u
    rcases eq_or_ne (‖u - v‖) 0 with h0 | h0
    · have hvu : ‖v - u‖ = 0 := by rw [norm_sub_rev]; exact h0
      rw [hvu, h0]
      simp only [div_zero, Real.log_zero]
      linarith
    · have hvu : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
      have hRd : R / ‖u - v‖ ≠ 0 := div_ne_zero hR0.ne' h0
      have hR' : 1 / R ≠ 0 := one_div_ne_zero hR0.ne'
      have heq : Real.log (R / ‖u - v‖) + Real.log (1 / R) = Real.log (1 / ‖u - v‖) := by
        rw [← Real.log_mul hRd hR']
        congr 1
        field_simp
      rw [hvu]
      linarith
  -- nonnegativity of the Lemma 1 integrand on `E`
  have hnn : ∀ u ∈ E, 0 ≤ Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R) := by
    intro u hu
    rcases eq_or_ne (‖u - v‖) 0 with h0 | h0
    · rw [h0, div_zero, Real.log_zero]
      linarith
    · have hd : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hd1 : ‖u - v‖ ≤ 1 := hdist u hu v hv
      have hRd : R / ‖u - v‖ ≠ 0 := div_ne_zero hR0.ne' h0
      have hR' : 1 / R ≠ 0 := one_div_ne_zero hR0.ne'
      have heq : Real.log (R / ‖u - v‖) + Real.log (1 / R) = Real.log (1 / ‖u - v‖) := by
        rw [← Real.log_mul hRd hR']
        congr 1
        field_simp
      have hlog : 0 ≤ Real.log (1 / ‖u - v‖) := Real.log_nonneg (one_le_one_div hd hd1)
      linarith
  -- integrability of the Lemma 1 integrand on `E`
  have hintE : IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R)) E μ := by
    have h1 : IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) E μ :=
      (hint v hv).mono_set hEA
    have h2 : IntegrableOn (fun _ : ℂ => Real.log (1 / R)) E μ :=
      integrableOn_const (ne_top_of_le_ne_top hμA (measure_mono hEA))
    exact h1.add h2
  have hnnE : 0 ≤ᵐ[μ.restrict E] fun u : ℂ => Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R) :=
    ae_restrict_of_forall_mem hE (fun u hu => hnn u hu)
  calc ∫⁻ u in E, ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ
      ≤ ∫⁻ u in E, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R)) ∂μ :=
        lintegral_mono (fun u => ENNReal.ofReal_le_ofReal (hpt u))
    _ = ENNReal.ofReal (∫ u in E, (Real.log (R / ‖u - v‖) + 1 + Real.log (1 / R)) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hintE hnnE).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hL

/-- **Potential supremum**: the supremum over the centre `v ∈ D` of the Draft kernel integral
over `E` is at most `ofReal (C₁ (1 + log(1/R)) m)`, with `C₁ = C (1 + (log 4 - 1)) / (1 - log 2)`. -/
theorem sup_kernel_le_of_annulus {A D E : Set ℂ} (μ : Measure ℂ) [SFinite μ] {z : ℂ} {R C m : ℝ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hA : MeasurableSet A) (hAb : A ⊆ closedBall z (2 * R)) (hμA : μ A ≠ ⊤)
    (hsph : sphere z (3 * R / 2) ⊆ A) (hE : MeasurableSet E) (hEA : E ⊆ A) (hDA : D ⊆ A)
    (hdist : ∀ u ∈ E, ∀ v ∈ D, ‖u - v‖ ≤ 1) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hint : ∀ v ∈ D, IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) A μ)
    (hF : ∀ w ∈ A, ∫ u in A, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ C * m) :
    (⨆ v ∈ D, ∫⁻ u in E, ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ≤
      ENNReal.ofReal (C * m * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2)) :=
  iSup₂_le (fun _ hv =>
    kernel_integral_le_of_annulus μ hR0 hR1 hA hAb hμA hsph hE hEA hDA hdist hC hm hint hF hv)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.sup_kernel_le_of_annulus
