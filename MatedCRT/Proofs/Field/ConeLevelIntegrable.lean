import MatedCRT.Proofs.Field.ConeLevelGaussian

/-!
# Gaussian spans and almost sure integrability of level integrals (eq:gff)

* `isCentredGaussianSpace_span`: the linear span of a centred Gaussian process is a centred Gaussian linear space.
* `integral_abs_le_of_map_eq`: `E|X| ≤ 1 + v` for `X` of law `N(0, v)`.
* `ae_integrable_level`: if `V` has almost surely continuous paths and `E|V_u| ≤ 1 + |u|`, then almost surely
  `x ↦ g(x) V_{s(x)}` is `ν`-integrable as soon as `g (1 + |s|)` is (Tonelli, on a jointly measurable version of `V`).
-/

namespace MatedCRT.Field.GaussClosure

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The linear span of a centred Gaussian process is a centred Gaussian linear space.** -/
theorem isCentredGaussianSpace_span {T : Type*} {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    (hXm : ∀ t, Measurable (X t)) (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) :
    IsCentredGaussianSpace P (Submodule.span ℝ (Set.range X) : Set (Ω → ℝ)) := by
  classical
  have := hX.isProbabilityMeasure
  intro Y hY
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hY
  set I := c.support
  let L : (I → ℝ) →L[ℝ] ℝ := ∑ i : I, c i • ContinuousLinearMap.proj i
  have hYeq : (c.sum fun i a => a • X i) = ⇑L ∘ fun ω => I.restrict fun t => X t ω := by
    funext ω
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, L,
      FunLike.coe_sum, FunLike.coe_smul, ContinuousLinearMap.proj_apply,
      Finset.restrict]
    exact (Finset.sum_coe_sort I fun i => c i * X i ω).symm
  have hvec : Measurable fun ω => I.restrict fun t => X t ω := measurable_pi_iff.2 fun i => hXm i
  have hG : HasGaussianLaw (c.sum fun i a => a • X i) P := by
    rw [hYeq]
    exact (hX.hasGaussianLaw I).map L
  have hint0 : ∫ ω, (c.sum fun i a => a • X i) ω ∂P = 0 := by
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ =>
      ((hX.hasGaussianLaw_eval i).memLp_two.integrable one_le_two).const_mul _]
    simp [integral_const_mul, hX0]
  refine ⟨hYeq ▸ L.continuous.measurable.comp hvec, Var[c.sum fun i a => a • X i; P].toNNReal, ?_⟩
  rw [hG.map_eq_gaussianReal, hint0]

/-- `E|X| ≤ 1 + v` for `X` of law `N(0, v)`. -/
theorem integral_abs_le_of_map_eq [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) {v : ℝ≥0}
    (h : P.map X = gaussianReal 0 v) : ∫ ω, |X ω| ∂P ≤ 1 + v := by
  have hL2 : MemLp id 2 (gaussianReal 0 v) := IsGaussian.memLp_two_id
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    simpa using hL2.integrable_sq
  have hvar : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
    have h1 := variance_eq_integral (μ := gaussianReal 0 v) (X := id) aemeasurable_id
    rw [variance_id_gaussianReal] at h1
    simp only [id_eq] at h1
    rw [integral_id_gaussianReal] at h1
    simpa using h1.symm
  rw [← integral_map hX.aemeasurable continuous_abs.aestronglyMeasurable, h]
  calc ∫ x, |x| ∂(gaussianReal 0 v) ≤ ∫ x, (1 + x ^ 2) ∂(gaussianReal 0 v) := by
        refine integral_mono (hL2.integrable one_le_two).abs ((integrable_const 1).add hsq) fun x => ?_
        nlinarith [abs_nonneg x, sq_abs x]
    _ = 1 + v := by
        rw [integral_add (integrable_const 1) hsq, hvar, integral_const, probReal_univ, one_smul]

/-- **Almost sure integrability of level integrals.** -/
theorem ae_integrable_level [IsProbabilityMeasure P] {α : Type*} [MeasurableSpace α] {V : ℝ → Ω → ℝ}
    (hVm : ∀ u, Measurable (V u)) (hcont : ∀ᵐ ω ∂P, Continuous fun u => V u ω)
    (hint1 : ∀ u, Integrable (V u) P) (hbd : ∀ u, ∫ ω, |V u ω| ∂P ≤ 1 + |u|)
    {ν : Measure α} [SFinite ν] {g s : α → ℝ} (hgm : Measurable g) (hs : Measurable s)
    (hg : Integrable (fun x => g x * (1 + |s x|)) ν) :
    ∀ᵐ ω ∂P, Integrable (fun x => g x * V (s x) ω) ν := by
  set B := {ω | ¬ Continuous fun u => V u ω}
  have hB : P B = 0 := ae_iff.1 hcont
  set G := (toMeasurable P B)ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P B).compl
  have hGc : ∀ ω ∈ G, Continuous fun u => V u ω := fun ω hω =>
    by_contra fun h => hω (subset_toMeasurable P B h)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa [G, measure_toMeasurable] using hB
  set W : ℝ → Ω → ℝ := fun u => G.indicator (V u)
  have hWc : ∀ ω, Continuous fun u => W u ω := fun ω => by
    by_cases hω : ω ∈ G
    · simpa [W, hω] using hGc ω hω
    · simpa [W, hω] using continuous_const
  have hWm : ∀ u, Measurable (W u) := fun u => (hVm u).indicator hGm
  have hjoint : Measurable (Function.uncurry W) := measurable_uncurry_of_continuous_of_measurable hWc hWm
  set F : Ω → α → ℝ≥0∞ := fun ω x => ‖g x‖ₑ * ‖W (s x) ω‖ₑ
  have hFm : Measurable (Function.uncurry F) :=
    (hgm.comp measurable_snd).enorm.mul
      (hjoint.comp ((hs.comp measurable_snd).prodMk measurable_fst)).enorm
  have hinner : ∀ x, ∫⁻ ω, F ω x ∂P ≤ ‖g x‖ₑ * ENNReal.ofReal (1 + |s x|) := by
    intro x
    rw [lintegral_const_mul _ (hWm (s x)).enorm]
    gcongr
    calc ∫⁻ ω, ‖W (s x) ω‖ₑ ∂P ≤ ∫⁻ ω, ‖V (s x) ω‖ₑ ∂P := lintegral_mono fun ω => by
          by_cases hω : ω ∈ G <;> simp [W, hω]
      _ = ENNReal.ofReal (∫ ω, |V (s x) ω| ∂P) := by
          rw [ofReal_integral_eq_lintegral_ofReal (hint1 _).abs (ae_of_all _ fun _ => abs_nonneg _)]
          simp only [Real.enorm_eq_ofReal_abs]
      _ ≤ ENNReal.ofReal (1 + |s x|) := ENNReal.ofReal_le_ofReal (hbd _)
  have hfin : ∫⁻ ω, ∫⁻ x, F ω x ∂ν ∂P ≠ ∞ := by
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hinner)
    refine ne_of_eq_of_ne (lintegral_congr fun x => ?_) hg.2.ne
    rw [enorm_mul, Real.enorm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |s x|)]
  have hae := ae_lt_top hFm.lintegral_prod_right' hfin
  filter_upwards [hae, hGae] with ω hω hωG
  have hWV : ∀ u, W u ω = V u ω := fun u => by simp [W, hωG]
  refine ⟨(hgm.mul ((hGc ω hωG).measurable.comp hs)).aestronglyMeasurable, ?_⟩
  refine lt_of_eq_of_lt (lintegral_congr fun x => ?_) hω
  show ‖g x * V (s x) ω‖ₑ = ‖g x‖ₑ * ‖W (s x) ω‖ₑ
  rw [hWV, enorm_mul]
