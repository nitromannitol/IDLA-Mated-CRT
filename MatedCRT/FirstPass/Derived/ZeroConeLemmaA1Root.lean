import MatedCRT.FirstPass.Derived.ZeroConeLemmaA4Proof
import MatedCRT.FirstPass.Derived.ZeroConeAreaCoordinateChangeProof

/-!
# The local observation at a uniform root (Lemma A.1 of Gwynne–Miller–Sheffield)

Section 2 of the proof of Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161, Appendix A, Steps 1-3) for the
circle-average embedding `h` of the `0`-quantum cone. For `z ∈ ℂ` let `r_s(z)` be the mass radius of the area
measure at `z` and `H_z = h(r_1(z) · + z) + Q log r_1(z)` the field normalized at `r_1(z)`. The local observation
`J(h, z) = f(H_z|_{B_a(0)}) 1{0 < a r_1(z) < r_b(z)}` is jointly measurable, and satisfies the radius identity
`J(h(C · + z) + Q log C, 0) = J(h, z)` on the good set. Lemma A.4 at the uniform roots of the capped squares
(`ZeroConeUniformRootLemmaA4`) then transfers an approximation of an invariant functional `F` by `J(·, 0)` to its
approximation by the average of `J` over the capped square `S_m` of an independent uniform dyadic system.

## Main definitions

* `rootField`, `RootTest`, `rootObs`: the normalized field, the radius test and the local observation.
* `rootAverage`: the average of the local observation over the capped square `S_m` of a dyadic system.

## Main statements

* `measurable_rootObs`: the local observation is jointly measurable in the field and the centre.
* `rootObs_lqgSimilarityField`: the radius identity.
* `integral_abs_sub_rootAverage_le`: display (1) of the written proof,
  `E |F(h) - A_m| ≤ δ` whenever `E |F(h) - J(h, 0)| ≤ δ`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-- The open disc `B_a(0)`. -/
def a1Ball (a : ℕ) : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩

/-- The field normalized at the mass radius `r_1(z)` around `z`: `H_z = h(r_1(z) · + z) + Q log r_1(z)`. -/
def rootField (γ : ℝ) (h : Field) (z : ℂ) : Field :=
  lqgSimilarityField γ (ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) 1 z) z h

/-- The radius test `0 < a r_1(z) < r_b(z)`. -/
def RootTest (γ : ℝ) (a : ℕ) (b₀ : ℝ) (h : Field) (z : ℂ) : Prop :=
  0 < ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) 1 z ∧
    (a : ℝ) * ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) 1 z <
      ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) b₀ z

/-- The local observation `J(h, z) = f(H_z|_{B_a}) 1{0 < a r_1(z) < r_b(z)}`. -/
def rootObs (γ : ℝ) {a : ℕ} (f : LQGMetric.DistOn (a1Ball a) → ℝ) (b₀ : ℝ) (h : Field) (z : ℂ) : ℝ :=
  open Classical in
  if RootTest γ a b₀ h z then f (LQGMetric.restrictTo (a1Ball a) (rootField γ h z)) else 0

/-- The average `A_m` of the local observation over the capped square `S_m` of the dyadic system `q`. -/
def rootAverage (γ : ℝ) {a : ℕ} (f : LQGMetric.DistOn (a1Ball a) → ℝ) (b₀ : ℝ) (m : ℝ≥0∞) (h : Field)
    (q : ZeroConeRoot.DyCoord) : ℝ :=
  ⨍ z in LatticeProb.CappedSquare.cappedSquare
      (LatticeProb.DyadicOffset.dyadicSquares q.1 q.2.1 q.2.2) (⇑(ConeAreaCovariance.areaMap γ h)) m 0,
    rootObs γ f b₀ h z

/-- The mass radius `r_s(z)` of the area map is jointly measurable in the field and the centre. -/
theorem measurable_massRadius_areaMap (γ s : ℝ) :
    Measurable fun p : Field × ℂ => ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ p.1) s p.2 := by
  have h1 : Measurable fun p : Field × ℂ => ConeAreaCovariance.areaMap γ p.1 :=
    (ConeAreaCovariance.measurable_areaMap γ).comp measurable_fst
  have h2 : Measurable fun p : Field × ℂ => (ConeAreaCovariance.areaMap γ p.1, p.2) :=
    h1.prodMk measurable_snd
  have h3 := (ZeroConeRoot.measurable_massRadius s).comp h2
  simp only [Function.comp_def] at h3
  exact h3

/-- **The local observation is jointly measurable** in the field and the centre. -/
theorem measurable_rootObs (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ} (hf : Measurable f)
    (b₀ : ℝ) : Measurable fun p : Field × ℂ => rootObs γ f b₀ p.1 p.2 := by
  have hr1 := measurable_massRadius_areaMap γ 1
  have hrb := measurable_massRadius_areaMap γ b₀
  have hset : MeasurableSet {p : Field × ℂ | RootTest γ a b₀ p.1 p.2} :=
    (measurableSet_lt measurable_const hr1).inter (measurableSet_lt (hr1.const_mul _) hrb)
  have hact : Measurable fun p : Field × ℂ =>
      lqgSimilarityAction γ (ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ p.1) 1 p.2, p.2) p.1 :=
    (measurable_lqgSimilarityAction γ).comp ((hr1.prodMk measurable_snd).prodMk measurable_fst)
  have hmain : Measurable fun p : Field × ℂ =>
      open Classical in
      if RootTest γ a b₀ p.1 p.2 then
        f (LQGMetric.restrictTo (a1Ball a)
          (lqgSimilarityAction γ
            (ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ p.1) 1 p.2, p.2) p.1))
      else 0 :=
    Measurable.ite hset (hf.comp ((LQGMetric.measurable_restrictTo _).comp hact)) measurable_const
  convert hmain using 1
  funext p
  by_cases hp : RootTest γ a b₀ p.1 p.2
  · have hact' := lqgSimilarityAction_of_pos γ (h := p.1) (t :=
      (ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ p.1) 1 p.2, p.2)) hp.1
    simp only [rootObs, rootField, hp, ↓reduceIte, hact']
  · simp only [rootObs, hp, ↓reduceIte]

/-- **Composition of the LQG coordinate changes**: the change of coordinates at `z` with scale `C`, followed by
the centred change of scale `C'`, is the change of coordinates at `z` with scale `C C'`. -/
theorem lqgSimilarityField_comp (γ : ℝ) {C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') (z : ℂ) (h : Field) :
    lqgSimilarityField γ C' 0 (lqgSimilarityField γ C z h) = lqgSimilarityField γ (C * C') z h := by
  unfold lqgSimilarityField
  rw [LQGMetric.GM.affineComp_addConst hC', LQGMetric.GM.affineComp_comp hC'.ne' hC.ne',
    LQGMetric.GFFLaw.addConst_addConst, mul_zero, zero_add, Real.log_mul hC.ne' hC'.ne', mul_add]

/-- **The radius identity.** On the good set, the local observation of the field `h(C · + z) + Q log C` at the
origin is the local observation of `h` at `z`: the mass radii of the transformed area measure at `0` are those of
`h` at `z` divided by `C`, and the normalized field is the same. -/
theorem rootObs_lqgSimilarityField (γ : ℝ) (hγ : γ ≠ 0) {a : ℕ} (f : LQGMetric.DistOn (a1Ball a) → ℝ)
    (b₀ : ℝ) {h : Field} (hh : h ∈ ConeAreaCovariance.goodSet γ) {C : ℝ} (hC : 0 < C) (z : ℂ) :
    rootObs γ f b₀ (lqgSimilarityField γ C z h) 0 = rootObs γ f b₀ h z := by
  have hspec : ConeAreaCovariance.areaMap γ (lqgSimilarityField γ C z h) =
      (ConeAreaCovariance.areaMap γ h).map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z) :=
    (ConeAreaCovariance.areaMap_spec hγ hh).2 C hC z
  have hr : ∀ s : ℝ, ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ (lqgSimilarityField γ C z h)) s 0 =
      ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) s z / C := fun s => by
    rw [hspec]
    exact ZeroConeRoot.massRadius_map_similarity _ s hC z
  by_cases ht : RootTest γ a b₀ h z
  · have hts : RootTest γ a b₀ (lqgSimilarityField γ C z h) 0 := by
      refine ⟨?_, ?_⟩
      · rw [hr]
        exact div_pos ht.1 hC
      · rw [hr, hr, ← mul_div_assoc]
        exact div_lt_div_of_pos_right ht.2 hC
    have hfield : rootField γ (lqgSimilarityField γ C z h) 0 = rootField γ h z := by
      unfold rootField
      rw [hr, lqgSimilarityField_comp γ hC (div_pos ht.1 hC), mul_div_cancel₀ _ hC.ne']
    simp only [rootObs, ht, hts, ↓reduceIte, hfield]
  · have hts : ¬ RootTest γ a b₀ (lqgSimilarityField γ C z h) 0 := by
      rintro ⟨h1, h2⟩
      rw [hr] at h1
      rw [hr, hr, ← mul_div_assoc] at h2
      exact ht ⟨(div_pos_iff_of_pos_right hC).1 h1, (div_lt_div_iff_of_pos_right hC).1 h2⟩
    simp only [rootObs, ht, hts, ↓reduceIte]

/-! ### The uniform point of a square -/

section UniformSquare

open LatticeProb.DyadicOffset (unifIco cornerSquare mem_cornerSquare)

/-- The uniform law on `[0, 1)` under `u ↦ a + ℓ u` is the normalized Lebesgue measure of `[a, a + ℓ]`. -/
theorem map_unifIco_affine (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (unifIco 1).map (fun u : ℝ => a + ℓ * u) =
      (ENNReal.ofReal ℓ)⁻¹ • volume.restrict (Icc a (a + ℓ)) := by
  have hm : Measurable fun u : ℝ => a + ℓ * u := by fun_prop
  have hpre : (fun u : ℝ => a + ℓ * u) ⁻¹' Ico a (a + ℓ) = Ico 0 1 := by
    ext u
    simp only [mem_preimage, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hvol : (volume : Measure ℝ).map (fun u : ℝ => a + ℓ * u) = (ENNReal.ofReal ℓ)⁻¹ • volume := by
    have e : (fun u : ℝ => a + ℓ * u) = (fun y => a + y) ∘ (fun u => ℓ * u) := rfl
    rw [e, ← Measure.map_map (measurable_const_add a) (measurable_const_mul ℓ),
      Real.map_volume_mul_left hℓ.ne', Measure.map_smul, map_add_left_eq_self, abs_of_pos (inv_pos.2 hℓ),
      ENNReal.ofReal_inv_of_pos hℓ]
    exact (measurable_const_add a).aemeasurable
  rw [unifIco, ENNReal.ofReal_one, inv_one, one_smul, ← hpre, ← Measure.restrict_map hm measurableSet_Ico,
    hvol, Measure.restrict_smul, Measure.restrict_congr_set Ico_ae_eq_Icc]

/-- **A uniform point of a square.** For `u` uniform on `[0, 1)²`, the point `(a + ℓ u₁) + i (c + ℓ u₂)` is
distributed as the normalized Lebesgue measure of the closed square `[a, a + ℓ] × [c, c + ℓ]`. -/
theorem map_unifSquareLaw_affine (a c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ZeroConeRoot.unifSquareLaw.map
        (fun u : ℝ × ℝ => ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) =
      (volume (cornerSquare a c ℓ))⁻¹ • volume.restrict (cornerSquare a c ℓ) := by
  have hf1 : Measurable fun u : ℝ => a + ℓ * u := by fun_prop
  have hf2 : Measurable fun u : ℝ => c + ℓ * u := by fun_prop
  have hφ : (fun u : ℝ × ℝ => ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) =
      Complex.measurableEquivRealProd.symm ∘
        Prod.map (fun u : ℝ => a + ℓ * u) (fun u : ℝ => c + ℓ * u) := by
    funext u
    exact (Complex.mk_eq_add_mul_I _ _).symm
  have hprod : ZeroConeRoot.unifSquareLaw.map (Prod.map (fun u : ℝ => a + ℓ * u) (fun u : ℝ => c + ℓ * u)) =
      ((ENNReal.ofReal ℓ)⁻¹ * (ENNReal.ofReal ℓ)⁻¹) •
        (volume.restrict (Icc a (a + ℓ) ×ˢ Icc c (c + ℓ)) : Measure (ℝ × ℝ)) := by
    unfold ZeroConeRoot.unifSquareLaw
    rw [← Measure.map_prod_map _ _ hf1 hf2, map_unifIco_affine a hℓ, map_unifIco_affine c hℓ,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  have hset : cornerSquare a c ℓ = Complex.measurableEquivRealProd ⁻¹' (Icc a (a + ℓ) ×ˢ Icc c (c + ℓ)) := by
    ext z
    simp only [mem_cornerSquare, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Icc,
      and_assoc]
  have hmp := MeasurePreserving.symm _ (Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet (Icc a (a + ℓ) ×ˢ Icc c (c + ℓ))))
  rw [← hset] at hmp
  rw [hφ, ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable (hf1.prodMap hf2), hprod,
    Measure.map_smul, hmp.map_eq]
  · congr 1
    rw [LatticeProb.DyadicOffset.volume_cornerSquare,
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
  · exact Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- **The uniform point of a square, in integral form**: the integral of a measurable function of
`(a + ℓ u₁) + i (c + ℓ u₂)`, `u` uniform on `[0, 1)²`, is its average over `[a, a + ℓ] × [c, c + ℓ]`. -/
theorem integral_unifSquareLaw_affine (a c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ u, g (((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) ∂ZeroConeRoot.unifSquareLaw =
      ⨍ z in cornerSquare a c ℓ, g z := by
  have hφm : Measurable fun u : ℝ × ℝ =>
      ((a + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I := by fun_prop
  rw [← integral_map hφm.aemeasurable hg.aestronglyMeasurable, map_unifSquareLaw_affine a c hℓ,
    setAverage_eq']

end UniformSquare

/-! ### The approximation at a uniform root -/

section UniformRoot

open LatticeProb.DyadicOffset (dyadicSquares cornerSquare unifIco)
open LatticeProb.CappedSquare (cappedSquare)

/-- The local observation is non-negative for a non-negative functional. -/
theorem rootObs_nonneg (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ} (hf0 : ∀ x, 0 ≤ f x) (b₀ : ℝ)
    (h : Field) (z : ℂ) : 0 ≤ rootObs γ f b₀ h z := by
  unfold rootObs
  split_ifs
  · exact hf0 _
  · exact le_rfl

/-- The local observation is bounded by the bound of the functional. -/
theorem rootObs_le (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ} {K : ℝ} (hfK : ∀ x, f x ≤ K)
    (hK : 0 ≤ K) (b₀ : ℝ) (h : Field) (z : ℂ) : rootObs γ f b₀ h z ≤ K := by
  unfold rootObs
  split_ifs
  · exact hfK _
  · exact hK

/-- A measurable function bounded in absolute value is integrable for a finite measure. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ x, |g x| ≤ K) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable K (ae_of_all _ fun x => by simpa using hK x)

/-- **Fubini for the root sampler**: for a function of a pair and of the uniform point, the integral over the
product with the independent extra variable is the integral of the average over the uniform point. -/
theorem integral_prod_forget {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μ : Measure α) (D : Measure β) (U : Measure γ) (V : Measure δ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure D] [IsProbabilityMeasure U] [IsProbabilityMeasure V]
    {g : (α × β) × γ → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) :
    ∫ x, g ((x.1, x.2.1), x.2.2.1) ∂μ.prod (D.prod (U.prod V)) =
      ∫ p, ∫ u, g (p, u) ∂U ∂μ.prod D := by
  have hΦm : StronglyMeasurable fun p : α × β => ∫ u, g (p, u) ∂U := hg.stronglyMeasurable.integral_prod_right'
  have hΦ : Integrable (fun p : α × β => ∫ u, g (p, u) ∂U) (μ.prod D) := by
    refine Integrable.of_bound hΦm.aestronglyMeasurable K (ae_of_all _ fun p => ?_)
    have := norm_integral_le_of_norm_le_const (μ := U) (f := fun u => g (p, u)) (C := K)
      (ae_of_all _ fun u => by simpa using hK (p, u))
    simpa using this
  have h3 : Measurable fun x : α × β × γ × δ => g ((x.1, x.2.1), x.2.2.1) :=
    hg.comp (by fun_prop)
  rw [integral_prod _ (integrable_of_abs_le h3 fun x => hK _), integral_prod _ hΦ]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  have h2 : Measurable fun e : β × γ × δ => g ((a, e.1), e.2.1) := hg.comp (by fun_prop)
  rw [integral_prod _ (integrable_of_abs_le h2 fun x => hK _)]
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  dsimp only
  have h1 : Measurable fun w : γ × δ => g ((a, b), w.1) := hg.comp (by fun_prop)
  rw [integral_prod _ (integrable_of_abs_le h1 fun x => hK _)]
  simp

/-- **Jensen's inequality for a probability measure**: `|t - ∫ J| ≤ ∫ |t - J|`. -/
theorem abs_sub_integral_le_integral_abs_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {J : α → ℝ} (hJ : Integrable J μ) (t : ℝ) :
    |t - ∫ x, J x ∂μ| ≤ ∫ x, |t - J x| ∂μ := by
  have h := norm_integral_le_integral_norm (μ := μ) (fun x => t - J x)
  rw [integral_sub (integrable_const t) hJ, integral_const] at h
  have h1 : μ.real univ = 1 := by simp [Measure.real]
  rw [h1, one_smul] at h
  simpa only [Real.norm_eq_abs] using h

/-- The local observation is measurable in the centre, for a fixed field. -/
theorem measurable_rootObs_section (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ}
    (hfm : Measurable f) (b₀ : ℝ) (h : Field) : Measurable fun z : ℂ => rootObs γ f b₀ h z := by
  have h2 : Measurable fun z : ℂ => ((h, z) : Field × ℂ) := measurable_const.prodMk measurable_id
  have h3 := (measurable_rootObs γ hfm b₀).comp h2
  simp only [Function.comp_def] at h3
  exact h3

/-- The local observation at the root sampler is measurable in the uniform point. -/
theorem measurable_rootObs_rootSample (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ}
    (hfm : Measurable f) (b₀ : ℝ) (m : ℝ≥0∞) (h : Field) (q : ZeroConeRoot.DyCoord) :
    Measurable fun u : ℝ × ℝ =>
      rootObs γ f b₀ h (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u) := by
  have hsm : Measurable fun u : ℝ × ℝ =>
      ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u :=
    ZeroConeRoot.measurable_rootSample_comp (N := fun _ : ℝ × ℝ => ConeAreaCovariance.areaMap γ h)
      (q := fun _ => q) measurable_const measurable_const measurable_id m
  have h3 := (measurable_rootObs_section γ hfm b₀ h).comp hsm
  simp only [Function.comp_def] at h3
  exact h3

/-- **The average over the capped square is the mean over the uniform root**: if the root sampler is the affine
parametrization of the capped square `Ŝ_m = [a, a + ℓ] × [c, c + ℓ]`, the average `A_m` of the local observation
is the integral of the observation at the root sampler over the uniform point `u ∈ [0, 1)²`. -/
theorem rootAverage_eq (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ} (hfm : Measurable f) (b₀ : ℝ)
    (m : ℝ≥0∞) (h : Field) (q : ZeroConeRoot.DyCoord)
    (hq : ∃ a₀ c ℓ : ℝ, 0 < ℓ ∧
      cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑(ConeAreaCovariance.areaMap γ h)) m 0 =
        cornerSquare a₀ c ℓ ∧
      ∀ u : ℝ × ℝ, ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u =
        ((a₀ + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) :
    rootAverage γ f b₀ m h q =
      ∫ u, rootObs γ f b₀ h (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u)
        ∂ZeroConeRoot.unifSquareLaw := by
  obtain ⟨a₀, c, ℓ, hℓ, hcap, hu⟩ := hq
  have hJm := measurable_rootObs_section γ hfm b₀ h
  unfold rootAverage
  rw [hcap, ← integral_unifSquareLaw_affine a₀ c hℓ hJm]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  exact congrArg (rootObs γ f b₀ h) (hu u).symm

/-- **Jensen for the average over the capped square**: the distance from `t` to the average `A_m` of the local
observation is at most the mean distance from `t` to the local observation at a uniform point of the square. -/
theorem abs_sub_rootAverage_le (γ : ℝ) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ} (hfm : Measurable f)
    {K : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfK : ∀ x, f x ≤ K) (hK : 0 ≤ K) (b₀ : ℝ) (m : ℝ≥0∞) (t : ℝ) (h : Field)
    (q : ZeroConeRoot.DyCoord)
    (hq : ∃ a₀ c ℓ : ℝ, 0 < ℓ ∧
      cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑(ConeAreaCovariance.areaMap γ h)) m 0 =
        cornerSquare a₀ c ℓ ∧
      ∀ u : ℝ × ℝ, ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u =
        ((a₀ + ℓ * u.1 : ℝ) : ℂ) + ((c + ℓ * u.2 : ℝ) : ℂ) * Complex.I) :
    |t - rootAverage γ f b₀ m h q| ≤
      ∫ u, |t - rootObs γ f b₀ h (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u)|
        ∂ZeroConeRoot.unifSquareLaw := by
  have hJint : Integrable (fun u : ℝ × ℝ =>
      rootObs γ f b₀ h (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) q m u))
      ZeroConeRoot.unifSquareLaw := by
    refine integrable_of_abs_le (measurable_rootObs_rootSample γ hfm b₀ m h q) (K := K) fun u => ?_
    rw [abs_of_nonneg (rootObs_nonneg γ hf0 b₀ _ _)]
    exact rootObs_le γ hfK hK b₀ _ _
  rw [rootAverage_eq γ hfm b₀ m h q hq]
  exact abs_sub_integral_le_integral_abs_sub hJint t

/-- **The approximation at a uniform root** (display (1) of the written proof of Lemma A.1 of
Gwynne–Miller–Sheffield, arXiv:1705.11161, Appendix A). Let `F` be bounded, non-negative and measurable, almost
surely invariant under the coordinate changes `h ↦ h(C · + z) + Q log C`, and approximated in `L¹` by the local
observation `J(·, 0)` at the origin up to `δ`. Then, for every mass `m ∈ (0, ∞)`, the same approximation holds
for the average `A_m` of the local observation over the capped square `S_m` of an independent uniform dyadic
system. The proof applies Lemma A.4 at the uniform root of `S_m` (`ZeroConeUniformRootLemmaA4`) with the area map
`ConeAreaCovariance.areaMap`, the radius identity `rootObs_lqgSimilarityField`, and Jensen's inequality for the
uniform point of the capped square. -/
theorem integral_abs_sub_rootAverage_le (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ)
    (hP : IsProbabilityMeasure P') (hX : LQGMetric.IsWholePlaneGFF X₀' P') (hb : IsBrownianReal b P')
    (hb' : IsBrownianReal b' P')
    (hXbb : IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P')
    (hbb' : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P')
    (hA4 : ZeroConeUniformRootLemmaA4 γ hγ) {F : Field → ℝ} (hFm : Measurable F) {K : ℝ}
    (hF0 : ∀ h, 0 ≤ F h) (hFK : ∀ h, F h ≤ K)
    (hinv : ∀ᵐ ω ∂P', ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      F (lqgSimilarityField γ C z (zeroConeFieldOf γ X₀' b b' ω)) = F (zeroConeFieldOf γ X₀' b b' ω))
    {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfK : ∀ x, f x ≤ K) {b₀ δ : ℝ}
    (happrox : ∫ h, |F h - rootObs γ f b₀ h 0| ∂(P'.map (zeroConeFieldOf γ X₀' b b')) ≤ δ)
    (m : ℝ≥0∞) (hm0 : m ≠ 0) (hmT : m ≠ ⊤) :
    ∫ p, |F p.1 - rootAverage γ f b₀ m p.1 p.2| ∂((P'.map (zeroConeFieldOf γ X₀' b b')).prod
      ZeroConeRoot.uniformDyadicLaw) ≤ δ := by
  classical
  have hK : 0 ≤ K := (hF0 0).trans (hFK 0)
  have hHm : AEMeasurable (zeroConeFieldOf γ X₀' b b') P' :=
    ZeroConeRoot.aemeasurable_zeroConeFieldOf γ hX hb hb' hbb'
  have : IsProbabilityMeasure (P'.map (zeroConeFieldOf γ X₀' b b')) :=
    (Measure.isProbabilityMeasure_map_iff hHm).2 hP
  have hQ : (0 : ℝ) < MatedCRTHarmonic.CellScaling.lqgQ γ := MatedCRTHarmonic.LQGCoord.lqgQ_pos hγ.1
  have hgoodω : ∀ᵐ ω ∂P', zeroConeFieldOf γ X₀' b b' ω ∈ ConeAreaCovariance.goodSet γ :=
    ConeAreaCovariance.ae_coneField_mem_goodSet hγ.1 hγ.2 hQ hX hb hb'
  have hgoodμ : ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), h ∈ ConeAreaCovariance.goodSet γ :=
    (ae_map_iff hHm (ConeAreaCovariance.measurableSet_goodSet γ)).2 hgoodω
  have hMv := hgoodμ.mono fun h hh => (ConeAreaCovariance.areaMap_spec hγ.1.ne' hh).1
  obtain ⟨hA2, hlaw⟩ := hA4 P' X₀' b b' hP hX hb hb' hXbb hbb' (ConeAreaCovariance.areaMap γ)
    (ConeAreaCovariance.measurable_areaMap γ) hMv
  have hgood := ZeroConeRoot.ae_goodPair (M := ConeAreaCovariance.areaMap γ) (hMv.mono fun _ hh => hh.1) hA2
  have hZm : Measurable fun x : Field × ZeroConeRoot.DyCoord × (ℝ × ℝ) =>
      ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1) x.2.1 m x.2.2 :=
    ZeroConeRoot.measurable_rootSample_comp ((ConeAreaCovariance.measurable_areaMap γ).comp measurable_fst)
      measurable_snd.fst measurable_snd.snd m
  obtain ⟨C, hCm, hCpos, hClaw⟩ := hlaw m hm0 hmT _ hZm (ZeroConeRoot.ae_rootSample_affine hgood hm0 hmT)
  -- the root and its observation as functions on the extended space
  have hZx : Measurable fun x : Field × ZeroConeRoot.DyCoord × (ℝ × ℝ) × ℝ =>
      ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1) x.2.1 m x.2.2.1 :=
    ZeroConeRoot.measurable_rootSample_comp ((ConeAreaCovariance.measurable_areaMap γ).comp measurable_fst)
      measurable_snd.fst measurable_snd.snd.fst m
  have hG : Measurable fun x : Field × ZeroConeRoot.DyCoord × (ℝ × ℝ) × ℝ =>
      lqgSimilarityField γ (C x) (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1) x.2.1 m x.2.2.1)
        x.1 := by
    have h1 := (measurable_lqgSimilarityAction γ).comp ((hCm.prodMk hZx).prodMk measurable_fst)
    convert h1 using 1
    funext x
    exact (lqgSimilarityAction_of_pos γ (t := (C x, _)) (hCpos x) x.1).symm
  have hFobs : Measurable fun h : Field => |F h - rootObs γ f b₀ h 0| :=
    (hFm.sub ((measurable_rootObs γ hfm b₀).comp (measurable_id.prodMk measurable_const))).abs
  -- the observation at the root has the same mean error as at the origin
  have hA : ∫ x, |F (lqgSimilarityField γ (C x) (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1)
        x.2.1 m x.2.2.1) x.1) - rootObs γ f b₀ (lqgSimilarityField γ (C x)
          (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1) x.2.1 m x.2.2.1) x.1) 0|
      ∂((P'.map (zeroConeFieldOf γ X₀' b b')).prod (ZeroConeRoot.uniformDyadicLaw.prod
        (ZeroConeRoot.unifSquareLaw.prod (unifIco 1)))) =
      ∫ h, |F h - rootObs γ f b₀ h 0| ∂(P'.map (zeroConeFieldOf γ X₀' b b')) := by
    rw [← integral_map hG.aemeasurable hFobs.aestronglyMeasurable]
    exact congrArg (fun ν => ∫ h, |F h - rootObs γ f b₀ h 0| ∂ν) hClaw
  -- invariance of `F` at the random parameters
  have hsmeas : MeasurableSet {x : Field × ZeroConeRoot.DyCoord × (ℝ × ℝ) × ℝ |
      F (lqgSimilarityField γ (C x) (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1) x.2.1 m
        x.2.2.1) x.1) = F x.1} :=
    measurableSet_eq_fun (hFm.comp hG) (hFm.comp measurable_fst)
  have hq : MeasurableSet {h : Field | ∀ᵐ e ∂(ZeroConeRoot.uniformDyadicLaw.prod
      (ZeroConeRoot.unifSquareLaw.prod (unifIco 1))), F (lqgSimilarityField γ (C (h, e))
        (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ h) e.1 m e.2.1) h) = F h} := by
    have h0 := measurable_measure_prodMk_left (ν := ZeroConeRoot.uniformDyadicLaw.prod
      (ZeroConeRoot.unifSquareLaw.prod (unifIco 1))) hsmeas.compl (measurableSet_singleton 0)
    convert h0 using 1
    ext h
    simp only [mem_ofPred_eq, ae_iff, mem_preimage, mem_singleton_iff]
    rfl
  have hqμ := (ae_map_iff hHm hq).2 (by
    filter_upwards [hinv] with ω hω
    exact ae_of_all _ fun e => hω (C (zeroConeFieldOf γ X₀' b b' ω, e)) (hCpos _) _)
  have hinvν := (Measure.ae_prod_iff_ae_ae hsmeas).2 hqμ
  have hobsν := ZeroConeRoot.ae_prod_fst_of_ae (ν := ZeroConeRoot.uniformDyadicLaw.prod
      (ZeroConeRoot.unifSquareLaw.prod (unifIco 1))) hgoodμ
  have hC1 : ∫ x : Field × ZeroConeRoot.DyCoord × (ℝ × ℝ) × ℝ,
      |F x.1 - rootObs γ f b₀ x.1 (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ x.1) x.2.1 m
        x.2.2.1)| ∂((P'.map (zeroConeFieldOf γ X₀' b b')).prod (ZeroConeRoot.uniformDyadicLaw.prod
        (ZeroConeRoot.unifSquareLaw.prod (unifIco 1)))) ≤ δ := by
    refine le_trans (le_of_eq ?_) (hA.trans_le happrox)
    refine integral_congr_ae ?_
    filter_upwards [hinvν, hobsν] with x h1 h2
    rw [rootObs_lqgSimilarityField γ hγ.1.ne' f b₀ h2 (hCpos x), h1]
  -- Jensen at the good pairs and Fubini
  have hĨm : Measurable fun y : (Field × ZeroConeRoot.DyCoord) × (ℝ × ℝ) =>
      |F y.1.1 - rootObs γ f b₀ y.1.1 (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ y.1.1) y.1.2 m
        y.2)| := by
    have hr := ZeroConeRoot.measurable_rootSample_comp (N := fun y : (Field × ZeroConeRoot.DyCoord) × (ℝ × ℝ) =>
      ConeAreaCovariance.areaMap γ y.1.1) (q := fun y => y.1.2) (u := fun y => y.2)
      ((ConeAreaCovariance.measurable_areaMap γ).comp (measurable_fst.comp measurable_fst))
      (measurable_snd.comp measurable_fst) measurable_snd m
    exact (((hFm.comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_rootObs γ hfm b₀).comp ((measurable_fst.comp measurable_fst).prodMk hr))).abs)
  have hĨK : ∀ y : (Field × ZeroConeRoot.DyCoord) × (ℝ × ℝ),
      |F y.1.1 - rootObs γ f b₀ y.1.1 (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ y.1.1) y.1.2 m
        y.2)| ≤ K := fun y => by
    have h1 := rootObs_nonneg γ hf0 b₀ y.1.1
      (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ y.1.1) y.1.2 m y.2)
    have h2 := rootObs_le γ hfK hK b₀ y.1.1
      (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ y.1.1) y.1.2 m y.2)
    have h3 := hF0 y.1.1
    have h4 := hFK y.1.1
    rw [abs_le]
    constructor <;> linarith
  have hfub := integral_prod_forget (P'.map (zeroConeFieldOf γ X₀' b b')) ZeroConeRoot.uniformDyadicLaw
    ZeroConeRoot.unifSquareLaw (unifIco 1) hĨm (fun y => (abs_abs _).trans_le (hĨK y))
  have hΦm : StronglyMeasurable fun p : Field × ZeroConeRoot.DyCoord =>
      ∫ u, |F p.1 - rootObs γ f b₀ p.1 (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ p.1) p.2 m u)|
        ∂ZeroConeRoot.unifSquareLaw := hĨm.stronglyMeasurable.integral_prod_right'
  have hΦ : Integrable (fun p : Field × ZeroConeRoot.DyCoord =>
      ∫ u, |F p.1 - rootObs γ f b₀ p.1 (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ p.1) p.2 m u)|
        ∂ZeroConeRoot.unifSquareLaw) ((P'.map (zeroConeFieldOf γ X₀' b b')).prod
          ZeroConeRoot.uniformDyadicLaw) := by
    refine Integrable.of_bound hΦm.aestronglyMeasurable K (ae_of_all _ fun p => ?_)
    have := norm_integral_le_of_norm_le_const (μ := ZeroConeRoot.unifSquareLaw)
      (f := fun u => |F p.1 - rootObs γ f b₀ p.1
        (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ p.1) p.2 m u)|) (C := K)
      (ae_of_all _ fun u => by simpa using hĨK (p, u))
    simpa using this
  have hJ : ∀ᵐ p ∂(P'.map (zeroConeFieldOf γ X₀' b b')).prod ZeroConeRoot.uniformDyadicLaw,
      |F p.1 - rootAverage γ f b₀ m p.1 p.2| ≤ ∫ u, |F p.1 - rootObs γ f b₀ p.1
        (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ p.1) p.2 m u)| ∂ZeroConeRoot.unifSquareLaw := by
    filter_upwards [ZeroConeRoot.ae_rootSample_affine hgood hm0 hmT] with p hp
    exact abs_sub_rootAverage_le γ hfm hf0 hfK hK b₀ m (F p.1) p.1 p.2 hp
  calc ∫ p, |F p.1 - rootAverage γ f b₀ m p.1 p.2| ∂((P'.map (zeroConeFieldOf γ X₀' b b')).prod
        ZeroConeRoot.uniformDyadicLaw)
      ≤ ∫ p, ∫ u, |F p.1 - rootObs γ f b₀ p.1
        (ZeroConeRoot.rootSample (ConeAreaCovariance.areaMap γ p.1) p.2 m u)| ∂ZeroConeRoot.unifSquareLaw
          ∂((P'.map (zeroConeFieldOf γ X₀' b b')).prod ZeroConeRoot.uniformDyadicLaw) :=
        integral_mono_of_nonneg (ae_of_all _ fun p => abs_nonneg _) hΦ hJ
    _ = _ := hfub.symm
    _ ≤ δ := hC1

end UniformRoot

end MatedCRT
