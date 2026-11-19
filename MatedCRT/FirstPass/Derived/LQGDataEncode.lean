import MatedCRT.FirstPass.Derived.LQGDataSpace

/-!
# Encoding a locally finite measure on the plane as a point of `LQGData`

For a Borel measure `μ` on `ℂ` and `R : ℕ`, the localization of `μ` to the annulus `ann R` is
`α_R = ι_R^* (annRho R · μ)`, the pull-back along the inclusion `ι_R : ann R → ℂ` of the measure
with density `annRho R` with respect to `μ`. The coordinate `R` of `LQGData.encode μ` is the pair
(total mass, normalization) of `α_R` when `α_R` is finite, and the fixed pair
`(0, δ_{z_R})` otherwise.

* `LQGData.toMeasure_encode`: for a locally finite `μ`, every `α_R` is finite (`ann R` is
  compact), `(mass α_R) • ι_R* (normalize α_R) = ι_R* α_R = annRho R · μ`, and
  `∑_R annRho R · μ = μ` since the `annRho R` form a partition of unity. Hence
  `(LQGData.encode μ).toMeasure = μ`.
* `LQGData.measurable_encode`: `LQGData.encode` is measurable for the Giry `σ`-algebra on
  `Measure ℂ` and the product `σ`-algebra on `LQGData`.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace MatedCRT.FirstPass.Derived

/-! ### Finite measures and their normalization -/

/-- A finite measure is its total mass times its normalization, as measures. -/
theorem toMeasure_eq_mass_smul_toMeasure_normalize {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : FiniteMeasure X) :
    (ν : Measure X) = ν.mass • ((ν.normalize : ProbabilityMeasure X) : Measure X) := by
  have h := congrArg (fun ρ : FiniteMeasure X => (ρ : Measure X))
    ν.self_eq_mass_smul_normalize
  rw [FiniteMeasure.toMeasure_smul] at h
  exact h

/-- A finite measure is its total mass (in `ℝ≥0∞`) times its normalization, as measures. -/
theorem mass_smul_toMeasure_normalize {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : FiniteMeasure X) :
    (ν.mass : ℝ≥0∞) • ((ν.normalize : ProbabilityMeasure X) : Measure X) = (ν : Measure X) := by
  ext B _
  have h := congrArg (fun ρ : Measure X => ρ B) (toMeasure_eq_mass_smul_toMeasure_normalize ν)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h
  rw [Measure.smul_apply, smul_eq_mul, h]

/-- The normalization of a nonzero finite measure `ν` is `(ν univ)⁻¹ • ν`, as measures. -/
theorem toMeasure_normalize_eq_inv_smul {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : FiniteMeasure X) (hν : ν ≠ 0) :
    ((ν.normalize : ProbabilityMeasure X) : Measure X) =
      ((ν : Measure X) univ)⁻¹ • (ν : Measure X) := by
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hν]
  ext B _
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, smul_eq_mul]
  rw [ENNReal.coe_inv ((FiniteMeasure.mass_nonzero_iff _).mpr hν), FiniteMeasure.ennreal_mass]

/-! ### The annuli and the partition of unity in `ℝ≥0∞` -/

theorem measurableSet_ann (R : ℕ) : MeasurableSet (ann R) :=
  (isClosed_ann R).measurableSet

instance nonempty_ann (R : ℕ) : Nonempty (ann R) :=
  ⟨⟨(R : ℂ), by rw [mem_ann, Complex.norm_natCast]; constructor <;> linarith⟩⟩

theorem measurable_ofReal_annRho (R : ℕ) :
    Measurable fun z : ℂ => ENNReal.ofReal (annRho R z) :=
  ENNReal.measurable_ofReal.comp (continuous_annRho R).measurable

theorem support_ofReal_annRho_subset (R : ℕ) :
    Function.support (fun z : ℂ => ENNReal.ofReal (annRho R z)) ⊆ ann R := by
  intro z hz
  apply mem_ann_of_annRho_ne_zero
  intro h0
  have h1 : ENNReal.ofReal (annRho R z) = 0 := by rw [h0, ENNReal.ofReal_zero]
  exact hz h1

/-- `∑_R annRho R z = 1` in `ℝ≥0∞`. -/
theorem tsum_ofReal_annRho (z : ℂ) : ∑' R, ENNReal.ofReal (annRho R z) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun R => annRho_nonneg R z) (hasSum_annRho z).summable,
    (hasSum_annRho z).tsum_eq, ENNReal.ofReal_one]

/-- **The localized measures `annRho R · μ` sum to `μ`.** -/
theorem sum_withDensity_annRho (μ : Measure ℂ) :
    Measure.sum (fun R : ℕ => μ.withDensity fun z => ENNReal.ofReal (annRho R z)) = μ := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp only [withDensity_apply _ hs]
  rw [← lintegral_tsum fun R => (measurable_ofReal_annRho R).aemeasurable]
  simp only [tsum_ofReal_annRho, lintegral_const, Measure.restrict_apply_univ, one_mul]

/-! ### The localization of a measure to an annulus -/

/-- The localization of `μ` to the annulus `ann R`: the pull-back along the inclusion
`ι_R : ann R → ℂ` of the measure `annRho R · μ` with density `annRho R` with respect to `μ`. -/
def annLocalization (μ : Measure ℂ) (R : ℕ) : Measure (ann R) :=
  (μ.withDensity fun z => ENNReal.ofReal (annRho R z)).comap Subtype.val

/-- The push-forward of the localization `α_R` along `ι_R` is `annRho R · μ`: the density
`annRho R` vanishes off `ann R`. -/
theorem map_annLocalization (μ : Measure ℂ) (R : ℕ) :
    (annLocalization μ R).map Subtype.val = μ.withDensity fun z => ENNReal.ofReal (annRho R z) := by
  rw [annLocalization, (MeasurableEmbedding.subtype_coe (measurableSet_ann R)).map_comap,
    Subtype.range_coe, restrict_withDensity (measurableSet_ann R),
    ← withDensity_indicator (measurableSet_ann R),
    Set.indicator_eq_self.mpr (support_ofReal_annRho_subset R)]

/-- For a locally finite `μ`, the localization `α_R` is a finite measure:
`α_R (ann R) ≤ μ (ann R) < ∞` since `annRho R ≤ 1` and `ann R` is compact. -/
theorem annLocalization_univ_lt_top (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (R : ℕ) :
    annLocalization μ R univ < ∞ := by
  rw [annLocalization, (MeasurableEmbedding.subtype_coe (measurableSet_ann R)).comap_apply,
    Set.image_univ, Subtype.range_coe, withDensity_apply _ (measurableSet_ann R)]
  calc ∫⁻ z in ann R, ENNReal.ofReal (annRho R z) ∂μ ≤ ∫⁻ _ in ann R, 1 ∂μ :=
        lintegral_mono fun z => ENNReal.ofReal_le_one.mpr (annRho_le_one R z)
    _ = μ (ann R) := by rw [lintegral_one, Measure.restrict_apply_univ]
    _ < ∞ := (isCompact_ann R).measure_lt_top

/-- The localization `μ ↦ α_R` is measurable for the Giry `σ`-algebras: for a Borel set
`B ⊆ ann R`, `α_R B = ∫⁻ 1_{ι_R '' B} annRho R dμ`. -/
theorem measurable_annLocalization (R : ℕ) :
    Measurable fun μ : Measure ℂ => annLocalization μ R := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have hB' : MeasurableSet (Subtype.val '' B : Set ℂ) := (measurableSet_ann R).subtype_image hB
  simp only [annLocalization, (MeasurableEmbedding.subtype_coe (measurableSet_ann R)).comap_apply,
    withDensity_apply _ hB', ← lintegral_indicator hB']
  exact Measure.measurable_lintegral ((measurable_ofReal_annRho R).indicator hB')

/-! ### The encoding -/

/-- The probability measure used in the coordinates of infinite mass: the Dirac mass at a
point of `ann R`. -/
def annJunk (R : ℕ) : ProbabilityMeasure (ann R) :=
  ⟨Measure.dirac (Classical.arbitrary (ann R)), inferInstance⟩

/-- The localization `α_R` as a finite measure, when its total mass is finite. -/
def annFiniteMeasure (μ : Measure ℂ) (R : ℕ) (h : annLocalization μ R univ < ∞) :
    FiniteMeasure (ann R) :=
  ⟨annLocalization μ R, ⟨h⟩⟩

theorem toMeasure_annFiniteMeasure {μ : Measure ℂ} {R : ℕ} (h : annLocalization μ R univ < ∞) :
    (annFiniteMeasure μ R h : Measure (ann R)) = annLocalization μ R :=
  rfl

/-- The coordinate `R` of the encoding of `μ`: (total mass, normalization) of the localization
`α_R` when it is finite, and `(0, annJunk R)` otherwise. -/
def encodeCoord (μ : Measure ℂ) (R : ℕ) : ℝ≥0 × ProbabilityMeasure (ann R) :=
  if h : annLocalization μ R univ < ∞ then
    ((annFiniteMeasure μ R h).mass, (annFiniteMeasure μ R h).normalize)
  else (0, annJunk R)

/-- **The encoding of a measure on `ℂ` as a point of `LQGData`**: coordinate `R` is
(total mass, normalization) of the localization `α_R = ι_R^* (annRho R · μ)` when `α_R` is
finite, and `(0, annJunk R)` otherwise. -/
def LQGData.encode (μ : Measure ℂ) : LQGData := fun R => encodeCoord μ R

theorem encodeCoord_of_lt_top {μ : Measure ℂ} {R : ℕ} (h : annLocalization μ R univ < ∞) :
    encodeCoord μ R = ((annFiniteMeasure μ R h).mass, (annFiniteMeasure μ R h).normalize) := by
  rw [encodeCoord, dite_eq_left h]

/-- For a finite localization, `(mass α_R) • ι_R* (normalize α_R) = annRho R · μ`. -/
theorem encodeCoord_smul_map {μ : Measure ℂ} {R : ℕ} (h : annLocalization μ R univ < ∞) :
    ((encodeCoord μ R).1 : ℝ≥0∞) • ((encodeCoord μ R).2 : Measure (ann R)).map Subtype.val =
      μ.withDensity fun z => ENNReal.ofReal (annRho R z) := by
  rw [← map_annLocalization μ R, encodeCoord_of_lt_top h, ← Measure.map_smul]
  · exact congrArg (Measure.map Subtype.val) (mass_smul_toMeasure_normalize (annFiniteMeasure μ R h))
  · exact measurable_subtype_coe.aemeasurable

/-- **The encoding recovers a locally finite measure**: `(LQGData.encode μ).toMeasure = μ`. -/
theorem LQGData.toMeasure_encode (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    (LQGData.encode μ).toMeasure = μ := by
  rw [LQGData.toMeasure]
  conv_rhs => rw [← sum_withDensity_annRho μ]
  congr 1
  funext R
  exact encodeCoord_smul_map (annLocalization_univ_lt_top μ R)

/-! ### Measurability of the encoding -/

theorem encodeCoord_fst (μ : Measure ℂ) (R : ℕ) :
    (encodeCoord μ R).1 = (annLocalization μ R univ).toNNReal := by
  by_cases h : annLocalization μ R univ < ∞
  · rw [encodeCoord_of_lt_top h]
    rfl
  · rw [encodeCoord, dite_eq_right h, ENNReal.not_lt_top.mp h, ENNReal.toNNReal_top]

/-- The probability coordinate of the encoding, as a measure: `(α_R univ)⁻¹ • α_R` when
`0 < α_R univ < ∞`. -/
theorem encodeCoord_snd (μ : Measure ℂ) (R : ℕ) :
    ((encodeCoord μ R).2 : Measure (ann R)) =
      if annLocalization μ R univ < ∞ then
        (if annLocalization μ R univ = 0 then
          (((0 : FiniteMeasure (ann R)).normalize : ProbabilityMeasure (ann R)) : Measure (ann R))
        else (annLocalization μ R univ)⁻¹ • annLocalization μ R)
      else ((annJunk R : ProbabilityMeasure (ann R)) : Measure (ann R)) := by
  by_cases h : annLocalization μ R univ < ∞
  · have hsnd : (encodeCoord μ R).2 = (annFiniteMeasure μ R h).normalize := by
      rw [encodeCoord_of_lt_top h]
    rw [hsnd, ite_eq_left h]
    by_cases h0 : annLocalization μ R univ = 0
    · have hν : annFiniteMeasure μ R h = 0 :=
        Subtype.ext ((Measure.measure_univ_eq_zero.mp h0).trans FiniteMeasure.toMeasure_zero.symm)
      rw [ite_eq_left h0, hν]
    · have hν : annFiniteMeasure μ R h ≠ 0 := by
        intro hz
        exact h0 (Measure.measure_univ_eq_zero.mpr
          ((congrArg (fun ν : FiniteMeasure (ann R) => (ν : Measure (ann R))) hz).trans
            FiniteMeasure.toMeasure_zero))
      rw [ite_eq_right h0]
      exact toMeasure_normalize_eq_inv_smul _ hν
  · rw [encodeCoord, dite_eq_right h, ite_eq_right h]

theorem measurable_encodeCoord (R : ℕ) : Measurable fun μ : Measure ℂ => encodeCoord μ R := by
  have hα := measurable_annLocalization R
  have hU : Measurable fun μ : Measure ℂ => annLocalization μ R univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp hα
  have h1 : Measurable fun μ : Measure ℂ => (encodeCoord μ R).1 := by
    simp only [encodeCoord_fst]
    exact ENNReal.measurable_toNNReal.comp hU
  have hsmul : Measurable fun μ : Measure ℂ =>
      (annLocalization μ R univ)⁻¹ • annLocalization μ R := by
    refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hU.inv.mul ((Measure.measurable_coe hB).comp hα)
  have hval : Measurable fun μ : Measure ℂ => ((encodeCoord μ R).2 : Measure (ann R)) := by
    simp only [encodeCoord_snd]
    exact Measurable.ite (hU measurableSet_Iio)
      (Measurable.ite (hU (measurableSet_singleton 0)) measurable_const hsmul) measurable_const
  have h2 : Measurable fun μ : Measure ℂ => (encodeCoord μ R).2 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hval ht
  exact h1.prodMk h2

/-- **The encoding is measurable** for the Giry `σ`-algebra on `Measure ℂ` and the product
`σ`-algebra on `LQGData`. -/
theorem LQGData.measurable_encode : Measurable LQGData.encode :=
  measurable_pi_iff.mpr fun R => measurable_encodeCoord R

end MatedCRT.FirstPass.Derived

end
