import MatedCRT.FirstPass.SLERef.Similarity

/-!
# Scaling of Lebesgue representatives and of area-parametrized curves

The deterministic part of the similarity transfer of the whole-plane space-filling SLE: the rescaled curve
`s ↦ R⁻¹ η(b s)` is parametrized by the area of the rescaled measure `FPScaledMeasure μ R b` whenever `η` is
parametrized by the area of `μ`, and the rescaled Lebesgue representative `t ↦ a⁻¹ c(a² t)` represents the rescaled curve.
Also the Borel measurability of the rescaling of paths in the pair (scale, path).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

/-- The rescaled path `t ↦ a⁻¹ c(a² t)`, as a continuous path. -/
noncomputable def scaleRep (a : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => (a : ℂ)⁻¹ * c (a ^ 2 * t),
    continuous_const.mul (c.continuous.comp (continuous_const.mul continuous_id))⟩

theorem scaleRep_apply (a : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    scaleRep a c t = (a : ℂ)⁻¹ * c (a ^ 2 * t) := rfl

/-- The rescaled Lebesgue representative represents the rescaled curve. -/
theorem isLebesgueRepresentative_scaleRep {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {η : ℝ → ℂ} {c : C(ℝ, ℂ)}
    (h : IsLebesgueRepresentative η c) :
    IsLebesgueRepresentative (fun s => (a : ℂ)⁻¹ * η (b * s)) (scaleRep a c) := by
  obtain ⟨h0, hsurj, hproper, hvol, φ, hφ0, hηφ⟩ := h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have ha2 : 0 < a ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [scaleRep_apply, h0]
  · intro z
    obtain ⟨t, ht⟩ := hsurj ((a : ℂ) * z)
    refine ⟨t / a ^ 2, ?_⟩
    have : a ^ 2 * (t / a ^ 2) = t := by field_simp
    rw [scaleRep_apply, this, ht]
    field_simp
  · have h1 : Tendsto (fun t : ℝ => a ^ 2 * t) (cocompact ℝ) (cocompact ℝ) :=
      (Homeomorph.mulLeft₀ (a ^ 2) ha2.ne').map_cocompact.le
    have h2 : Tendsto (fun z : ℂ => (a : ℂ)⁻¹ * z) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.mulLeft₀ ((a : ℂ)⁻¹) (inv_ne_zero ha0)).map_cocompact.le
    exact h2.comp (hproper.comp h1)
  · intro s t hst
    have himg : (scaleRep a c) '' Icc s t = (a⁻¹ : ℝ) • (c '' Icc (a ^ 2 * s) (a ^ 2 * t)) := by
      rw [← image_mul_left_Icc' ha2 s t, ← Set.image_smul, Set.image_image, Set.image_image]
      refine Set.image_congr fun u _ => ?_
      simp [scaleRep_apply, Complex.real_smul]
    rw [himg, Measure.addHaar_smul, hvol _ _ (mul_le_mul_of_nonneg_left hst ha2.le),
      Complex.finrank_real_complex, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_pos (by positivity)]
    field_simp
  · refine ⟨((OrderIso.mulLeft₀ b hb).trans φ).trans (OrderIso.mulLeft₀ ((a ^ 2)⁻¹) (inv_pos.2 ha2)), ?_, ?_⟩
    · show (a ^ 2)⁻¹ * φ (b * 0) = 0
      simp [hφ0]
    · intro s
      show (a : ℂ)⁻¹ * η (b * s) = (a : ℂ)⁻¹ * c (a ^ 2 * ((a ^ 2)⁻¹ * φ (b * s)))
      rw [mul_inv_cancel_left₀ ha2.ne', hηφ]

/-- The rescaled curve is parametrized by the area of the rescaled measure. -/
theorem isAreaParametrized_fPScaledMeasure {μ : Measure ℂ} {η : ℝ → ℂ} {R b : ℝ} (hR : R ≠ 0) (hb : 0 < b)
    (h : IsAreaParametrized μ η) :
    IsAreaParametrized (FPScaledMeasure μ R b) (fun s => (R : ℂ)⁻¹ * η (b * s)) := by
  obtain ⟨hcont, h0, hsurj, hmass⟩ := h
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hc' : Continuous fun s : ℝ => (R : ℂ)⁻¹ * η (b * s) :=
    continuous_const.mul (hcont.comp (continuous_const.mul continuous_id))
  refine ⟨hc', by simp [h0], ?_, ?_⟩
  · intro z
    obtain ⟨t, ht⟩ := hsurj ((R : ℂ) * z)
    refine ⟨t / b, ?_⟩
    have : b * (t / b) = t := by field_simp
    show (R : ℂ)⁻¹ * η (b * (t / b)) = z
    rw [this, ht]
    field_simp
  · intro x y hxy
    have hcomp : IsCompact ((fun s : ℝ => (R : ℂ)⁻¹ * η (b * s)) '' Icc x y) := isCompact_Icc.image hc'
    have hmeasf : Measurable fun w : ℂ => (R : ℂ)⁻¹ * w := (continuous_const.mul continuous_id).measurable
    have himg : (fun s : ℝ => η (b * s)) '' Icc x y = η '' Icc (b * x) (b * y) := by
      rw [← image_mul_left_Icc' hb x y, Set.image_image]
    have hpre : (fun w : ℂ => (R : ℂ)⁻¹ * w) ⁻¹' ((fun s : ℝ => (R : ℂ)⁻¹ * η (b * s)) '' Icc x y) =
        η '' Icc (b * x) (b * y) := by
      rw [← himg, ← Set.image_image (fun w : ℂ => (R : ℂ)⁻¹ * w) (fun s : ℝ => η (b * s)),
        Function.Injective.preimage_image (mul_right_injective₀ (inv_ne_zero hR0))]
    unfold FPScaledMeasure
    rw [Measure.smul_apply, Measure.map_apply hmeasf hcomp.isClosed.measurableSet, hpre,
      hmass _ _ (mul_lt_mul_of_pos_left hxy hb), smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp

/-- The rescaled area measure of a locally finite measure is locally finite. -/
theorem isLocallyFiniteMeasure_fPScaledMeasure {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R : ℝ} (hR : R ≠ 0)
    (b : ℝ) : IsLocallyFiniteMeasure (FPScaledMeasure μ R b) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hmeasf : Measurable fun w : ℂ => (R : ℂ)⁻¹ * w := (continuous_const.mul continuous_id).measurable
  refine ⟨fun x => ?_⟩
  obtain ⟨V, hVx, hVo, hV⟩ := Measure.exists_isOpen_measure_lt_top μ ((R : ℂ) * x)
  have hUo : IsOpen {w : ℂ | (R : ℂ) * w ∈ V} := hVo.preimage (continuous_const.mul continuous_id)
  refine ⟨{w : ℂ | (R : ℂ) * w ∈ V}, hUo.mem_nhds hVx, ?_⟩
  unfold FPScaledMeasure
  rw [Measure.smul_apply, Measure.map_apply hmeasf hUo.measurableSet]
  have : (fun w : ℂ => (R : ℂ)⁻¹ * w) ⁻¹' {w : ℂ | (R : ℂ) * w ∈ V} = V := by
    ext w
    simp [mul_inv_cancel_left₀ hR0]
  rw [this, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV

/-- The nonzero scale `a` if `0 < a`, and `1` otherwise. -/
noncomputable def posScale (a : ℝ) : {a : ℝ // a ≠ 0} :=
  ⟨if 0 < a then a else 1, by split_ifs with h; exacts [h.ne', one_ne_zero]⟩

theorem continuous_scaleRep_uncurry :
    Continuous fun x : ({a : ℝ // a ≠ 0} × C(ℝ, ℂ)) × ℝ => scaleRep x.1.1.1 x.1.2 x.2 := by
  have h1 : Continuous fun x : ({a : ℝ // a ≠ 0} × C(ℝ, ℂ)) × ℝ => ((x.1.1.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have h2 : Continuous fun x : ({a : ℝ // a ≠ 0} × C(ℝ, ℂ)) × ℝ => ((x.1.1.1 : ℝ) : ℂ)⁻¹ :=
    h1.inv₀ fun x => by exact_mod_cast x.1.1.2
  have h3 : Continuous fun x : ({a : ℝ // a ≠ 0} × C(ℝ, ℂ)) × ℝ => (x.1.2, x.1.1.1 ^ 2 * x.2) :=
    (continuous_snd.comp continuous_fst).prodMk
      (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).pow 2).mul continuous_snd)
  have h4 : Continuous fun x : ({a : ℝ // a ≠ 0} × C(ℝ, ℂ)) × ℝ =>
      ((x.1.1.1 : ℝ) : ℂ)⁻¹ * x.1.2 (x.1.1.1 ^ 2 * x.2) := h2.mul (continuous_eval.comp h3)
  simp only [scaleRep_apply]
  exact h4

/-- Borel measurability of the rescaling of paths in the pair (scale, path). -/
theorem measurable_scaleRep :
    Measurable fun p : ℝ × C(ℝ, ℂ) => scaleRep (if 0 < p.1 then p.1 else 1) p.2 := by
  have hG : Continuous fun q : {a : ℝ // a ≠ 0} × C(ℝ, ℂ) => scaleRep q.1.1 q.2 :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_scaleRep_uncurry
  have hm : Measurable fun p : ℝ × C(ℝ, ℂ) => (posScale p.1, p.2) := by
    refine Measurable.prodMk ?_ measurable_snd
    refine Measurable.subtype_mk ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_fst measurable_const
  have h := hG.measurable.comp hm
  exact h

end MatedCRT.FirstPass.Derived
