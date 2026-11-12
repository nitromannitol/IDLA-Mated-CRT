import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle

/-!
# Scaling covariance of the degree-weighted cell measure (scaling step of BG20 Corollary A.6)

For `b > 0` and `R ≠ 0` let `η' = R⁻¹ η(b ·)` and `μ' = b⁻¹ μ(R ·)` (`rescaledMeasure`). The cells of `η'` with cell
size `ε / b` are `R⁻¹` times the cells of `η` with cell size `ε` (`Sec1.mem_cell_rescale`), so for every edge
multiplicity `m` the degree-weighted measure of `(η', μ')` at cell size `ε / b` is the image of the degree-weighted
measure of `(η, μ)` at cell size `ε` under the same rescaling (`degreeWeightedMeasure_rescale`). The mated-CRT map of
the Brownian-rescaled boundary-length pair `b^{-1/2} (L, R)(b ·)` with cell size `ε / b` is the map of `(L, R)` with
cell size `ε` (`MatedCRTEnv.mult_rescale`, from `Sec1.bmEdgeCount_rescale`). Hence, for the rescaled environment of
`ConeEnvironmentScalingStep` (curve `R_b⁻¹ η(b ·)`, pair `b^{-1/2} (L, R)(b ·)`, measure `b⁻¹ μ_h(R_b ·)`), almost
surely, for every `ε` and every `f`,
`∫ f dμ'^{ε/b} = b⁻¹ ∫ f(R_b⁻¹ ·) dμ_h^ε` and `∫ f dμ' = b⁻¹ ∫ f(R_b⁻¹ ·) dμ_h`
(`MatedCRTEnv.ae_integral_degreeWeightedMeasure_rescale`); with `f = g(R_b ·)` this reads
`∫ g dμ_h^ε = b ∫ g(R_b ·) dμ'^{ε/b}` (`MatedCRTEnv.ae_integral_degreeWeightedMeasure_eq_rescale`). This is the
identity by which BG20 transfer the convergence `μ_h^ε → 6 μ_h` from test functions supported in `B_ρ`, `ρ < 1`, to
all compactly supported test functions (scale invariance of the `γ`-quantum cone, BG20 Lemma 2.3).
-/

namespace MatedCRT

open MeasureTheory Filter Set

/-- **Scaling covariance of the degree-weighted measure.** For `b > 0`, `R ≠ 0` and `η' = R⁻¹ η(b ·)`, the
degree-weighted measure of `(η', b⁻¹ μ(R ·))` at cell size `ε / b` is `b⁻¹` times the image under `x ↦ R⁻¹ x` of the
degree-weighted measure of `(η, μ)` at cell size `ε`, for every edge multiplicity `m`. -/
theorem degreeWeightedMeasure_rescale {ε b R : ℝ} (hb : 0 < b) (hR : R ≠ 0) (m : ℤ → ℤ → ℕ)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (μ : Measure ℂ) :
    degreeWeightedMeasure m (ε / b) η' (rescaledMeasure μ R b) =
      rescaledMeasure (degreeWeightedMeasure m ε η μ) R b := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  have he := measurableEmbedding_inv_dilation hR
  have hcell : ∀ k : ℤ, cell (ε / b) η' k = (fun x : ℂ => (R : ℂ) * x) ⁻¹' cell ε η k := fun k => by
    ext x
    exact Sec1.mem_cell_rescale hb hRc η η' hη k x
  ext s hs
  have hs' : MeasurableSet ((fun x : ℂ => (R : ℂ)⁻¹ * x) ⁻¹' s) := he.measurable hs
  simp only [degreeWeightedMeasure, rescaledMeasure]
  rw [Measure.sum_apply _ hs, Measure.smul_apply, he.map_apply, Measure.sum_apply _ hs', smul_eq_mul,
    ← ENNReal.tsum_mul_left]
  congr 1
  funext k
  rw [hcell k]
  simp only [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs', he.map_apply,
    preimage_inter, preimage_inv_dilation_preimage_dilation hR, smul_eq_mul]
  ring

/-- Integrals against the degree-weighted measure of the rescaled pair `(R⁻¹ η(b ·), b⁻¹ μ(R ·))` at cell size `ε / b`:
`∫ f dμ'^{ε/b} = b⁻¹ ∫ f(R⁻¹ ·) dμ^ε`. -/
theorem integral_degreeWeightedMeasure_rescale {ε b R : ℝ} (hb : 0 < b) (hR : R ≠ 0) (m : ℤ → ℤ → ℕ)
    (η η' : ℝ → ℂ) (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (μ : Measure ℂ) (f : ℂ → ℝ) :
    ∫ x, f x ∂degreeWeightedMeasure m (ε / b) η' (rescaledMeasure μ R b) =
      b⁻¹ * ∫ y, f ((R : ℂ)⁻¹ * y) ∂degreeWeightedMeasure m ε η μ := by
  rw [degreeWeightedMeasure_rescale hb hR m η η' hη μ, integral_rescaledMeasure _ hR hb]

/-- The mated-CRT map of the Brownian-rescaled boundary-length pair `b^{-1/2} (L, R)(b ·)` with cell size `ε / b` is
the mated-CRT map of `(L, R)` with cell size `ε` (Definition 1.1 is invariant under Brownian scaling). -/
theorem MatedCRTEnv.mult_rescale {Ω : Type} [MeasurableSpace Ω] (S S' : MatedCRTEnv Ω) {b : ℝ} (hb : 0 < b)
    (ω : Ω) (hbm : ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s)) (ε : ℝ) :
    S'.mult (ε / b) ω = S.mult ε ω := by
  have hc : 0 < (Real.sqrt b)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hb)
  funext j k
  refine Sec1.bmEdgeCount_rescale hb hc _ _ _ _ (fun s => ?_) (fun s => ?_) j k
  · simp only [hbm, Prod.smul_fst, smul_eq_mul]
  · simp only [hbm, Prod.smul_snd, smul_eq_mul]

/-- **The degree-weighted measure of the rescaled environment.** If `S'` has (almost surely) curve `R_b⁻¹ η(b ·)`,
boundary-length pair `b^{-1/2} (L, R)(b ·)` and measure `b⁻¹ μ_h(R_b ·)` with `R_b > 0` (the data of
`ConeEnvironmentScalingStep`), then almost surely, for every `ε` and every `f`,
`∫ f dμ'^{ε/b} = b⁻¹ ∫ f(R_b⁻¹ ·) dμ_h^ε` and `∫ f dμ' = b⁻¹ ∫ f(R_b⁻¹ ·) dμ_h`. -/
theorem MatedCRTEnv.ae_integral_degreeWeightedMeasure_rescale {Ω : Type} [MeasurableSpace Ω]
    (S S' : MatedCRTEnv Ω) (γ : ℝ) {b : ℝ} (hb : 0 < b)
    (hpos : ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b)
    (hη : ∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s))
    (hbm : ∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s))
    (hμ : ∀ᵐ ω ∂S.P, S'.μ ω = rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ) (f : ℂ → ℝ),
      ∫ x, f x ∂degreeWeightedMeasure (S'.mult (ε / b) ω) (ε / b) (S'.η ω) (S'.μ ω) =
          b⁻¹ * ∫ y, f (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * y)
            ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω) ∧
        ∫ x, f x ∂S'.μ ω = b⁻¹ * ∫ y, f (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * y) ∂S.μ ω := by
  filter_upwards [hpos, hη, hbm, hμ] with ω hp he hm hmu ε f
  rw [MatedCRTEnv.mult_rescale S S' hb ω hm ε, hmu]
  exact ⟨integral_degreeWeightedMeasure_rescale hb hp.ne' _ _ _ he _ f,
    integral_rescaledMeasure _ hp.ne' hb f⟩

/-- **Transfer form.** Under the hypotheses of `MatedCRTEnv.ae_integral_degreeWeightedMeasure_rescale`, almost surely,
for every `ε` and every `g`, with `R = R_b`:
`∫ g dμ_h^ε - 6 ∫ g dμ_h = b (∫ g(R ·) dμ'^{ε/b} - 6 ∫ g(R ·) dμ')`. -/
theorem MatedCRTEnv.ae_integral_degreeWeightedMeasure_eq_rescale {Ω : Type} [MeasurableSpace Ω]
    (S S' : MatedCRTEnv Ω) (γ : ℝ) {b : ℝ} (hb : 0 < b)
    (hpos : ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b)
    (hη : ∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s))
    (hbm : ∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s))
    (hμ : ∀ᵐ ω ∂S.P, S'.μ ω = rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ) (g : ℂ → ℝ),
      ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω) - 6 * ∫ x, g x ∂S.μ ω =
        b * (∫ x, g (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ) * x)
              ∂degreeWeightedMeasure (S'.mult (ε / b) ω) (ε / b) (S'.η ω) (S'.μ ω) -
            6 * ∫ x, g (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ) * x) ∂S'.μ ω) := by
  filter_upwards [hpos, MatedCRTEnv.ae_integral_degreeWeightedMeasure_rescale S S' γ hb hpos hη hbm hμ]
    with ω hp h ε g
  have hRc : ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp.ne'
  obtain ⟨h1, h2⟩ := h ε fun x => g (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ) * x)
  simp only [mul_inv_cancel_left₀ hRc] at h1 h2
  rw [h1, h2]
  field_simp
