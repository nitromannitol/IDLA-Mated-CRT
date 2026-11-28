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

end MatedCRT
