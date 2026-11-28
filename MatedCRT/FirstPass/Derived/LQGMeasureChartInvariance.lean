import MatedCRT.FirstPass.Derived.LQGMeasureChartOpenProperty
import MatedCRT.FirstPass.Derived.LQGMeasureChartPerturb
import MatedCRT.FirstPass.Derived.LQGMeasureChartStraightenExponent
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift

/-!
# Invariances of the coordinate-change property and of the circle approximations

Deterministic transformations of a field `h` on the plane under which the coordinate change of its LQG measure on
open sets (`OpenChartProp`, the smooth approximations of Sheffield–Wang, arXiv:1605.06171v2, §3.2) and the
convergence of its circle approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` along `ε = 2^{-k}` (Duplantier–Sheffield,
arXiv:0808.1560v2, Proposition 1.1) are preserved, with the limiting measure transformed accordingly:

* adding a continuous function `v` multiplies the measure by `e^{γ v}` (`OpenChartProp.addFun`); a constant `c`
  multiplies it by `e^{γ c}` (`OpenChartProp.addConst`). For an inverse chart `φ = ψ⁻¹` the pulled-back field gains the
  continuous function `v ∘ φ` (change of variables `x = φ(w)`), and the smooth approximations of the field plus a
  continuous function converge to `e^{γ v ∘ φ}` times the limit (`isVagueLimitOn_smoothApprox_add`);
* the translate `LQGMetric.affineComp 1 z h = h(· + z)` (whose pairing is `⟨h(· + z), u⟩ = ⟨h, u(· − z)⟩`) has the
  translated measure `μ(· + z)`, the image of `μ` under `x ↦ x − z` (`OpenChartProp.affineComp`): the chart `ψ` on `V`
  for the translate is the chart `ψ(· − z)` on `V + z` for `h`;
* the same for the circle approximations, as vague limits on the whole plane (`QuantumZipper.IsVagueLimitOn univ`):
  for any circle-average process (`isVagueLimitOn_univ_lqgApprox_add_circleAverage`,
  `isVagueLimitOn_univ_lqgApprox_add_const`, `isVagueLimitOn_univ_lqgApprox_comp_add`), and for the circle averages
  `LQGMetric.circleAvg` of `addConst`, `addFun` (where the defining limits of the circle averages of `h` exist; the
  circle averages of `v` converge locally uniformly) and `affineComp 1 z`.
-/

set_option autoImplicit false

noncomputable section

open scoped Classical

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

namespace Invariance

variable {V : Set ℂ} {ψ : ℂ → ℂ}

/-! ### Injective holomorphic maps on open sets -/

theorem invFunOn_eq_symm (hV : IsOpen V) (hψ : DifferentiableOn ℂ ψ V) (hinj : InjOn ψ V) {w : ℂ}
    (hw : w ∈ ψ '' V) : Function.invFunOn ψ V w = (QuantumZipper.CA.univalentOPH hV hψ hinj).symm w := by
  have hw' : w ∈ (QuantumZipper.CA.univalentOPH hV hψ hinj).target := hw
  refine hinj (Function.invFunOn_mem hw) ((QuantumZipper.CA.univalentOPH hV hψ hinj).map_target hw') ?_
  rw [Function.invFunOn_eq hw, QuantumZipper.CA.univalentOPH_apply_symm_apply hV hψ hinj hw]

theorem continuousOn_invFunOn (hV : IsOpen V) (hψ : DifferentiableOn ℂ ψ V) (hinj : InjOn ψ V) :
    ContinuousOn (Function.invFunOn ψ V) (ψ '' V) :=
  (QuantumZipper.CA.univalentOPH hV hψ hinj).continuousOn_symm.congr fun _ hw => invFunOn_eq_symm hV hψ hinj hw

theorem piecewise_preimage_inter (A : Set ℂ) :
    (V.piecewise ψ fun _ => (0 : ℂ)) ⁻¹' A ∩ V = V ∩ ψ ⁻¹' A := by
  ext z
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    rw [piecewise_eq_of_mem _ _ _ h2] at h1
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    refine ⟨?_, h2⟩
    rw [piecewise_eq_of_mem _ _ _ h2]
    exact h1

/-- **Change of variables `w = ψ(x)`** in the pairing of a continuous function with a transported test. -/
theorem integral_indicator_mul_eq (hV : IsOpen V) (hψ : DifferentiableOn ℂ ψ V) (hinj : InjOn ψ V)
    (u v : ℂ → ℝ) :
    ∫ x, V.indicator (fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) x * v x =
      ∫ w, (ψ '' V).indicator (fun w => v (Function.invFunOn ψ V w)) w * u w := by
  have hderiv : ∀ x ∈ V, HasFDerivWithinAt ψ (fderiv ℝ ψ x) V x := fun x hx =>
    ((hψ.differentiableAt (hV.mem_nhds hx)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have e1 : (fun x => V.indicator (fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) x * v x) =
      V.indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2 * v x := by
    funext x
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have e2 : (fun w => (ψ '' V).indicator (fun w => v (Function.invFunOn ψ V w)) w * u w) =
      (ψ '' V).indicator fun w => v (Function.invFunOn ψ V w) * u w := by
    funext w
    by_cases hw : w ∈ ψ '' V
    · rw [indicator_of_mem hw, indicator_of_mem hw]
    · rw [indicator_of_notMem hw, indicator_of_notMem hw, zero_mul]
  have hW : MeasurableSet (ψ '' V) := (QuantumZipper.CA.isOpen_image_of_injOn' hV hψ hinj).measurableSet
  rw [e1, e2, integral_indicator hV.measurableSet, integral_indicator hW,
    integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hV.measurableSet hderiv hinj]
  refine setIntegral_congr_fun hV.measurableSet fun x hx => ?_
  simp only [smul_eq_mul]
  rw [QuantumZipper.abs_det_fderiv_eq_normSq (hψ.differentiableAt (hV.mem_nhds hx)),
    hinj.leftInvOn_invFunOn hx]
  ring

/-- The transported test `V.indicator (u ∘ ψ |ψ'|²)` of a smooth `u` vanishing outside a compact `K ⊆ ψ(V)` is an
admissible test on the plane. -/
theorem admissible_indicator (hV : IsOpen V) (hψ : DifferentiableOn ℂ ψ V) (hinj : InjOn ψ V) {u : ℂ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ ψ '' V)
    (hu0 : ∀ w, w ∉ K → u w = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (V.indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) ∧
      HasCompactSupport (V.indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) ∧
      tsupport (V.indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) := by
  have hKx : IsCompact (Function.invFunOn ψ V '' K) :=
    hK.image_of_continuousOn ((continuousOn_invFunOn hV hψ hinj).mono hKW)
  have hKxV : Function.invFunOn ψ V '' K ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact Function.invFunOn_mem (hKW hw)
  have h0 : ∀ y, y ∉ Function.invFunOn ψ V '' K → (V.indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) y = 0 := by
    intro y hy
    by_cases hyV : y ∈ V
    · rw [indicator_of_mem hyV, hu0 (ψ y) fun h => hy ⟨ψ y, h, hinj.leftInvOn_invFunOn hyV⟩, zero_mul]
    · exact indicator_of_notMem hyV _
  refine ⟨?_, HasCompactSupport.intro hKx h0, subset_univ _⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hyV : y ∈ V
  · have hψcd : ContDiffAt ℝ (⊤ : ℕ∞) ψ y :=
      ((hψ.contDiffOn hV).restrict_scalars ℝ).contDiffAt (hV.mem_nhds hyV)
    have hψ'cd : ContDiffAt ℝ (⊤ : ℕ∞) (deriv ψ) y :=
      (((hψ.deriv hV).contDiffOn hV).restrict_scalars ℝ).contDiffAt (hV.mem_nhds hyV)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => u (ψ x)) y := by
      have h := hu.contDiffAt.comp y hψcd
      exact h
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ‖deriv ψ x‖ ^ 2) y := by
      have h := (contDiff_norm_sq ℝ).contDiffAt.comp y hψ'cd
      exact h
    refine (h1.mul h2).congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hyV] with x hx
    exact indicator_of_mem hx _
  · have hyK : y ∉ Function.invFunOn ψ V '' K := fun h => hyV (hKxV h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hKx.isClosed.isOpen_compl.mem_nhds hyK] with x hx
    exact h0 x hx

/-- `⟨h + v, T⟩ = ⟨h, T⟩ + ∫ T v` for an admissible test `T`. -/
theorem pairFun_addFun (h : LQGMetric.DistC) (v : C(ℂ, ℝ)) {T : ℂ → ℝ}
    (hT : ContDiff ℝ (⊤ : ℕ∞) T ∧ HasCompactSupport T ∧ tsupport T ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)) :
    pairFun (V := ⊤) (LQGMetric.addFun h v) T = pairFun (V := ⊤) h T + ∫ x, T x * v x := by
  unfold pairFun
  rw [dite_eq_left hT, dite_eq_left hT]
  show h ⟨T, hT.1, hT.2.1, hT.2.2⟩ + LQGMetric.ofCont v ⟨T, hT.1, hT.2.1, hT.2.2⟩ = _
  rw [LQGMetric.ofCont_apply]
  rfl

/-! ### Translations -/

theorem sub_eq_addRight (z : ℂ) : (fun x : ℂ => x - z) = ⇑(Homeomorph.addRight (-z)) := by
  funext x
  simp [sub_eq_add_neg]

theorem measurableEmbedding_sub (z : ℂ) : MeasurableEmbedding fun x : ℂ => x - z := by
  rw [sub_eq_addRight]
  exact (Homeomorph.addRight (-z)).measurableEmbedding

theorem hasCompactSupport_comp_sub {g : ℂ → ℝ} (hg : HasCompactSupport g) (z : ℂ) :
    HasCompactSupport fun x => g (x - z) := by
  have h := hg.comp_homeomorph (Homeomorph.addRight (-z))
  rwa [← sub_eq_addRight] at h

theorem isCompact_preimage_sub {K : Set ℂ} (hK : IsCompact K) (z : ℂ) :
    IsCompact ((fun x : ℂ => x - z) ⁻¹' K) := by
  rw [sub_eq_addRight]
  exact (Homeomorph.addRight (-z)).isCompact_preimage.2 hK

/-- `⟨h(· + z), T⟩ = ⟨h, T(· − z)⟩` for every function `T`. -/
theorem pairFun_affineComp (h : LQGMetric.DistC) (z : ℂ) (T : ℂ → ℝ) :
    pairFun (V := ⊤) (LQGMetric.affineComp 1 z h) T = pairFun (V := ⊤) h (fun y => T (y - z)) := by
  by_cases hT : ContDiff ℝ (⊤ : ℕ∞) T ∧ HasCompactSupport T ∧ tsupport T ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)
  · have hT' : ContDiff ℝ (⊤ : ℕ∞) (fun y => T (y - z)) ∧ HasCompactSupport (fun y => T (y - z)) ∧
        tsupport (fun y => T (y - z)) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) :=
      ⟨hT.1.comp (contDiff_id.sub contDiff_const), hasCompactSupport_comp_sub hT.2.1 z, subset_univ _⟩
    unfold pairFun
    rw [dite_eq_left hT, dite_eq_left hT', LQGMetric.GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
    congr 1
    ext y
    rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero, Complex.ofReal_one, div_one]
    rfl
  · have hT' : ¬(ContDiff ℝ (⊤ : ℕ∞) (fun y => T (y - z)) ∧ HasCompactSupport (fun y => T (y - z)) ∧
        tsupport (fun y => T (y - z)) ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)) := by
      rintro ⟨h1, h2, -⟩
      apply hT
      refine ⟨?_, ?_, subset_univ _⟩
      · have h3 := h1.comp (contDiff_id.add (contDiff_const (c := z)))
        convert h3 using 1
        funext y
        simp
      · have h3 := hasCompactSupport_comp_sub h2 (-z)
        convert h3 using 1
        funext x
        simp
    unfold pairFun
    rw [dite_eq_right hT, dite_eq_right hT']

/-- The circle approximations of a translated circle-average process are the translated circle approximations. -/
theorem lqgApprox_comp_add (γ : ℝ) (hc : ℝ → ℂ → ℝ) (z : ℂ) (ε : ℝ) :
    HarmonicBalls.lqgApprox γ (fun s w => hc s (w + z)) ε =
      (HarmonicBalls.lqgApprox γ hc ε).map fun x => x - z := by
  have hemb := measurableEmbedding_sub z
  ext A hA
  rw [hemb.map_apply]
  unfold HarmonicBalls.lqgApprox
  rw [withDensity_apply _ hA, withDensity_apply _ (hemb.measurable hA), ← lintegral_indicator hA,
    ← lintegral_indicator (hemb.measurable hA)]
  conv_rhs => rw [← lintegral_add_right_eq_self _ z]
  congr 1
  funext w
  by_cases hw : w ∈ A
  · have hw' : w + z ∈ (fun x : ℂ => x - z) ⁻¹' A := by
      show w + z - z ∈ A
      rwa [add_sub_cancel_right]
    rw [indicator_of_mem hw, indicator_of_mem hw']
  · have hw' : w + z ∉ (fun x : ℂ => x - z) ⁻¹' A := by
      show w + z - z ∉ A
      rwa [add_sub_cancel_right]
    rw [indicator_of_notMem hw, indicator_of_notMem hw']

/-- Vague convergence on the plane is preserved by the translation `x ↦ x − z`. -/
theorem isVagueLimitOn_univ_map_sub {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (H : QuantumZipper.IsVagueLimitOn univ μs μ) (z : ℂ) :
    QuantumZipper.IsVagueLimitOn univ (fun k => (μs k).map fun x => x - z) (μ.map fun x => x - z) := by
  have hemb := measurableEmbedding_sub z
  obtain ⟨-, hfin, ht⟩ := H
  refine ⟨by rw [compl_univ, measure_empty], fun K hK _ => ?_, fun g hg hgs _ => ?_⟩
  · rw [hemb.map_apply]
    exact hfin _ (isCompact_preimage_sub hK z) (subset_univ _)
  · simp only [hemb.integral_map]
    exact ht (fun x => g (x - z)) (hg.comp (continuous_id.sub continuous_const)) (hasCompactSupport_comp_sub hgs z)
      (subset_univ _)

end Invariance

open Invariance

/-! ### The coordinate-change property -/

/-- **Adding a continuous function to the field multiplies its LQG measure by `e^{γ v}`** in the coordinate-change
property on open sets. -/
theorem OpenChartProp.addFun {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {h : LQGMetric.DistC} {μ : Measure ℂ}
    (H : OpenChartProp γ f h μ) (v : C(ℂ, ℝ)) :
    OpenChartProp γ f (LQGMetric.addFun h v) (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * v z))) := by
  intro V hV ψ hinj hψ hbdd
  obtain ⟨ν, hν, hνA⟩ := H V hV ψ hinj hψ hbdd
  have hW : IsOpen (ψ '' V) := QuantumZipper.CA.isOpen_image_of_injOn' hV hψ hinj
  have hvc : ContinuousOn (fun w => v (Function.invFunOn ψ V w)) (ψ '' V) :=
    v.continuous.comp_continuousOn (continuousOn_invFunOn hV hψ hinj)
  set b : ℂ → ℝ := (ψ '' V).indicator fun w => v (Function.invFunOn ψ V w) with hb_def
  have hbc : ContinuousOn b (ψ '' V) := hvc.congr fun w hw => indicator_of_mem hw _
  have hbm : Measurable b := measurable_indicator_of_continuousOn hW hvc
  have hG' : ∀ ε : ℝ, 0 < ε → ∀ z, closedBall z ε ⊆ ψ '' V →
      pullbackPairingOn γ (LQGMetric.addFun h v) V ψ (fun w => mollScale f ε (z - w)) =
        pullbackPairingOn γ h V ψ (fun w => mollScale f ε (z - w)) + ∫ w, b w * mollScale f ε (z - w) := by
    intro ε hε z hz
    have hadm := admissible_indicator hV hψ hinj (u := fun w => mollScale f ε (z - w))
      (contDiff_const.mul (hf.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)))
      (isCompact_closedBall z ε) hz fun w hw => Straighten.mollScale_sub_eq_zero hf hε hw
    simp only [pullbackPairingOn]
    rw [pairFun_addFun h v hadm, integral_indicator_mul_eq hV hψ hinj (fun w => mollScale f ε (z - w)) v,
      hb_def]
    ring
  refine ⟨ν.withDensity fun w => ENNReal.ofReal (Real.exp (γ * b w)),
    isVagueLimitOn_smoothApprox_add hf hW hbc hG' hν, fun A hA hAW => ?_⟩
  have hψm : Measurable (V.piecewise ψ fun _ => (0 : ℂ)) :=
    hψ.continuousOn.measurable_piecewise continuousOn_const hV.measurableSet
  have hνmap : ν = Measure.map (V.piecewise ψ fun _ => (0 : ℂ)) (μ.restrict V) := by
    ext B hB
    rw [Measure.map_apply hψm hB, Measure.restrict_apply (hψm hB), piecewise_preimage_inter]
    have h1 : ν (B \ ψ '' V) = 0 := measure_mono_null (fun x hx => hx.2) hν.1
    rw [← measure_inter_add_sdiff B hW.measurableSet, h1, add_zero,
      hνA _ (hB.inter hW.measurableSet) inter_subset_right]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hx, hxB, -⟩
      exact ⟨hx, hxB⟩
    · rintro ⟨hx, hxB⟩
      exact ⟨hx, hxB, mem_image_of_mem ψ hx⟩
  have hFm : Measurable fun w => ENNReal.ofReal (Real.exp (γ * b w)) :=
    (hbm.const_mul γ).exp.ennreal_ofReal
  have hpm : MeasurableSet (V ∩ ψ ⁻¹' A) := by
    rw [← piecewise_preimage_inter]
    exact (hψm hA).inter hV.measurableSet
  rw [withDensity_apply _ hA, hνmap, setLIntegral_map hA hFm hψm, Measure.restrict_restrict (hψm hA),
    piecewise_preimage_inter, withDensity_apply _ hpm]
  refine setLIntegral_congr_fun hpm fun x hx => ?_
  simp only [piecewise_eq_of_mem _ _ _ hx.1, hb_def, indicator_of_mem (mem_image_of_mem ψ hx.1),
    hinj.leftInvOn_invFunOn hx.1]

/-- **Adding a constant `c` to the field multiplies its LQG measure by `e^{γ c}`** in the coordinate-change property
on open sets. -/
theorem OpenChartProp.addConst {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {h : LQGMetric.DistC} {μ : Measure ℂ}
    (H : OpenChartProp γ f h μ) (c : ℝ) :
    OpenChartProp γ f (LQGMetric.addConst h c) (ENNReal.ofReal (Real.exp (γ * c)) • μ) := by
  have h1 := H.addFun hf (ContinuousMap.const ℂ c)
  have e : (fun z => ENNReal.ofReal (Real.exp (γ * (ContinuousMap.const ℂ c) z))) =
      fun _ => ENNReal.ofReal (Real.exp (γ * c)) := rfl
  rw [e, withDensity_const] at h1
  exact h1

/-- **Translating the field translates its LQG measure** in the coordinate-change property on open sets: for
`h(· + z) = LQGMetric.affineComp 1 z h`, the measure is the image of `μ` under `x ↦ x − z`. -/
theorem OpenChartProp.affineComp {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {h : LQGMetric.DistC} {μ : Measure ℂ}
    (H : OpenChartProp γ f h μ) (z : ℂ) :
    OpenChartProp γ f (LQGMetric.affineComp 1 z h) (μ.map fun x => x - z) := by
  intro V hV ψ hinj hψ hbdd
  set V₀ : Set ℂ := (fun y => y - z) ⁻¹' V with hV₀
  set ψ₀ : ℂ → ℂ := fun y => ψ (y - z) with hψ₀
  have hV₀o : IsOpen V₀ := hV.preimage (continuous_id.sub continuous_const)
  have hinj₀ : InjOn ψ₀ V₀ := fun a ha b hb hab =>
    sub_left_inj.1 (hinj (show a - z ∈ V from ha) (show b - z ∈ V from hb) hab)
  have hdiff₀ : DifferentiableOn ℂ ψ₀ V₀ := fun y hy =>
    ((hψ.differentiableAt (hV.mem_nhds (show y - z ∈ V from hy))).comp y
      (differentiableAt_id.sub_const z)).differentiableWithinAt
  have himg : ψ₀ '' V₀ = ψ '' V := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y - z, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x + z, ?_, ?_⟩
      · show x + z - z ∈ V
        rwa [add_sub_cancel_right]
      · show ψ (x + z - z) = ψ x
        rw [add_sub_cancel_right]
  have hbdd₀ : Bornology.IsBounded (ψ₀ '' V₀) := by
    rw [himg]
    exact hbdd
  obtain ⟨ν, hν, hνA⟩ := H V₀ hV₀o ψ₀ hinj₀ hdiff₀ hbdd₀
  rw [himg] at hν hνA
  have hW : IsOpen (ψ '' V) := QuantumZipper.CA.isOpen_image_of_injOn' hV hψ hinj
  -- the inverse of `ψ₀` is the inverse of `ψ` shifted by `z`
  have hinv : ∀ w ∈ ψ '' V, Function.invFunOn ψ₀ V₀ w = Function.invFunOn ψ V w + z := by
    intro w hw
    have hw₀ : w ∈ ψ₀ '' V₀ := by
      rw [himg]
      exact hw
    have hmem : Function.invFunOn ψ V w + z ∈ V₀ := by
      show Function.invFunOn ψ V w + z - z ∈ V
      rw [add_sub_cancel_right]
      exact Function.invFunOn_mem hw
    refine hinj₀ (Function.invFunOn_mem hw₀) hmem ?_
    rw [Function.invFunOn_eq hw₀]
    show w = ψ (Function.invFunOn ψ V w + z - z)
    rw [add_sub_cancel_right, Function.invFunOn_eq hw]
  have hderiv : ∀ w ∈ ψ '' V,
      deriv (Function.invFunOn ψ₀ V₀) w = deriv (Function.invFunOn ψ V) w := by
    intro w hw
    have hev : Function.invFunOn ψ₀ V₀ =ᶠ[𝓝 w] fun w' => Function.invFunOn ψ V w' + z := by
      filter_upwards [hW.mem_nhds hw] with w' hw'
      exact hinv w' hw'
    rw [hev.deriv_eq, deriv_add_const]
  have hkey : ∀ ε : ℝ, 0 < ε → ∀ w, closedBall w ε ⊆ ψ '' V →
      pullbackPairingOn γ (LQGMetric.affineComp 1 z h) V ψ (fun w' => mollScale f ε (w - w')) =
        pullbackPairingOn γ h V₀ ψ₀ (fun w' => mollScale f ε (w - w')) := by
    intro ε hε w hw
    simp only [pullbackPairingOn]
    rw [pairFun_affineComp]
    have e1 : (fun y => V.indicator (fun x => mollScale f ε (w - ψ x) * ‖deriv ψ x‖ ^ 2) (y - z)) =
        V₀.indicator fun y => mollScale f ε (w - ψ₀ y) * ‖deriv ψ₀ y‖ ^ 2 := by
      funext y
      by_cases hy : y - z ∈ V
      · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ V₀ from hy), hψ₀, deriv_comp_sub_const]
      · rw [indicator_of_notMem hy, indicator_of_notMem (show y ∉ V₀ from hy)]
    have e2 : ∫ w', Real.log ‖deriv (Function.invFunOn ψ V) w'‖ * mollScale f ε (w - w') =
        ∫ w', Real.log ‖deriv (Function.invFunOn ψ₀ V₀) w'‖ * mollScale f ε (w - w') := by
      refine integral_congr_ae (Eventually.of_forall fun w' => ?_)
      by_cases hw' : w' ∈ closedBall w ε
      · simp only
        rw [hderiv w' (hw hw')]
      · simp only [Straighten.mollScale_sub_eq_zero hf hε hw', mul_zero]
    rw [e1, e2]
  refine ⟨ν, ?_, fun A hA hAW => ?_⟩
  · have heq : ∀ k, smoothApprox γ f (ψ '' V) (pullbackPairingOn γ (LQGMetric.affineComp 1 z h) V ψ)
        (HarmonicBalls.dyadicScale k) =
        smoothApprox γ f (ψ '' V) (pullbackPairingOn γ h V₀ ψ₀) (HarmonicBalls.dyadicScale k) := by
      intro k
      unfold smoothApprox
      congr 1
      funext w
      split_ifs with hw
      · unfold smoothExponent
        rw [hkey _ (HarmonicBalls.dyadicScale_pos k) w hw]
      · rfl
    simp only [heq]
    exact hν
  · rw [hνA A hA hAW, (measurableEmbedding_sub z).map_apply]
    rfl

/-! ### Circle approximations -/

/-- **Circle approximations, adding a continuous function**: if the circle approximations of a process `hc` converge
vaguely on the plane to `μ`, those of `hc + (circle averages of v)` converge to `e^{γ v} μ`. -/
theorem isVagueLimitOn_univ_lqgApprox_add_circleAverage {γ : ℝ} {hc : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (H : QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ hc (HarmonicBalls.dyadicScale k)) μ) (v : C(ℂ, ℝ)) :
    QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (fun s z => hc s z + Real.circleAverage v z s)
        (HarmonicBalls.dyadicScale k))
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * v z))) :=
  isVagueLimitOn_lqgApprox_add isOpen_univ v.continuous.continuousOn (fun _ _ _ _ => rfl) H

/-- **Circle approximations, adding a constant**: `hc + c` gives `e^{γ c} μ`. -/
theorem isVagueLimitOn_univ_lqgApprox_add_const {γ : ℝ} {hc : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (H : QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ hc (HarmonicBalls.dyadicScale k)) μ) (c : ℝ) :
    QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (fun s z => hc s z + c) (HarmonicBalls.dyadicScale k))
      (ENNReal.ofReal (Real.exp (γ * c)) • μ) := by
  have h1 := isVagueLimitOn_univ_lqgApprox_add_circleAverage H (ContinuousMap.const ℂ c)
  have e : (fun s z => hc s z + Real.circleAverage (ContinuousMap.const ℂ c) z s) = fun s z => hc s z + c := by
    funext s z
    rw [show (⇑(ContinuousMap.const ℂ c)) = fun _ => c from rfl, Real.circleAverage_const]
  have e' : (fun z => ENNReal.ofReal (Real.exp (γ * (ContinuousMap.const ℂ c) z))) =
      fun _ => ENNReal.ofReal (Real.exp (γ * c)) := rfl
  rw [e, e', withDensity_const] at h1
  exact h1

/-- **Circle approximations, translation**: the process `hc(·, · + z)` gives the image of `μ` under `x ↦ x − z`. -/
theorem isVagueLimitOn_univ_lqgApprox_comp_add {γ : ℝ} {hc : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (H : QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ hc (HarmonicBalls.dyadicScale k)) μ) (z : ℂ) :
    QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (fun s w => hc s (w + z)) (HarmonicBalls.dyadicScale k))
      (μ.map fun x => x - z) := by
  simp only [lqgApprox_comp_add]
  exact isVagueLimitOn_univ_map_sub H z

/-- **The circle averages of `h + c`**: if the circle approximations of `LQGMetric.circleAvg h` converge vaguely on
the plane to `μ` and the defining limits of the circle averages of `h` exist at the dyadic radii, the circle
approximations of `h + c` converge to `e^{γ c} μ`. -/
theorem isVagueLimitOn_univ_lqgApprox_circleAvg_addConst {γ : ℝ} {h : LQGMetric.DistC} {μ : Measure ℂ}
    (hlim : ∀ (k : ℕ) (w : ℂ), ∃ a : ℝ,
      Tendsto (fun n => LQGMetric.CircleAvg.mollAvg h n w (HarmonicBalls.dyadicScale k)) atTop (𝓝 a))
    (H : QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg h) (HarmonicBalls.dyadicScale k)) μ) (c : ℝ) :
    QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg (LQGMetric.addConst h c))
        (HarmonicBalls.dyadicScale k))
      (ENNReal.ofReal (Real.exp (γ * c)) • μ) := by
  have e : ∀ k, HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg (LQGMetric.addConst h c))
      (HarmonicBalls.dyadicScale k) =
      HarmonicBalls.lqgApprox γ (fun s w => LQGMetric.circleAvg h s w + c) (HarmonicBalls.dyadicScale k) := by
    intro k
    unfold HarmonicBalls.lqgApprox
    congr 1
    funext w
    obtain ⟨a, ha⟩ := hlim k w
    rw [LQGMetric.CircleAvg.circleAvg_addConst_of_tendsto ha c]
  simp only [e]
  exact isVagueLimitOn_univ_lqgApprox_add_const H c

/-- **The circle averages of `h + v`**, `v` continuous: under the hypotheses of
`isVagueLimitOn_univ_lqgApprox_circleAvg_addConst`, the circle approximations of `h + v` converge to `e^{γ v} μ`. -/
theorem isVagueLimitOn_univ_lqgApprox_circleAvg_addFun {γ : ℝ} {h : LQGMetric.DistC} {μ : Measure ℂ}
    (hlim : ∀ (k : ℕ) (w : ℂ), ∃ a : ℝ,
      Tendsto (fun n => LQGMetric.CircleAvg.mollAvg h n w (HarmonicBalls.dyadicScale k)) atTop (𝓝 a))
    (H : QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg h) (HarmonicBalls.dyadicScale k)) μ)
    (v : C(ℂ, ℝ)) :
    QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg (LQGMetric.addFun h v))
        (HarmonicBalls.dyadicScale k))
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * v z))) := by
  have hsub : LQGMetric.addFun h v - LQGMetric.ofCont v = h := add_sub_cancel_right h _
  have e : ∀ k, HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg (LQGMetric.addFun h v))
      (HarmonicBalls.dyadicScale k) =
      HarmonicBalls.lqgApprox γ (fun s w => LQGMetric.circleAvg h s w + Real.circleAverage v w s)
        (HarmonicBalls.dyadicScale k) := by
    intro k
    unfold HarmonicBalls.lqgApprox
    congr 1
    funext w
    obtain ⟨a, ha⟩ := hlim k w
    have ha' : Tendsto (fun n => LQGMetric.CircleAvg.mollAvg (LQGMetric.addFun h v - LQGMetric.ofCont v) n w
        (HarmonicBalls.dyadicScale k)) atTop (𝓝 a) := by
      rw [hsub]
      exact ha
    rw [(LQGMetric.CircleAvg.circleAvg_eq_sub_ofCont_add ha').2, hsub]
  simp only [e]
  exact isVagueLimitOn_univ_lqgApprox_add_circleAverage H v

/-- **The circle averages of the translate `h(· + z)`**: if the circle approximations of `LQGMetric.circleAvg h`
converge vaguely on the plane to `μ`, those of `LQGMetric.affineComp 1 z h` converge to the image of `μ` under
`x ↦ x − z`. -/
theorem isVagueLimitOn_univ_lqgApprox_circleAvg_affineComp {γ : ℝ} {h : LQGMetric.DistC} {μ : Measure ℂ}
    (H : QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg h) (HarmonicBalls.dyadicScale k)) μ) (z : ℂ) :
    QuantumZipper.IsVagueLimitOn univ
      (fun k => HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg (LQGMetric.affineComp 1 z h))
        (HarmonicBalls.dyadicScale k))
      (μ.map fun x => x - z) := by
  have e : LQGMetric.circleAvg (LQGMetric.affineComp 1 z h) = fun s w => LQGMetric.circleAvg h s (w + z) := by
    funext s w
    exact LQGMetric.GM.circleAvg_affineComp_one_at h s z w
  rw [e]
  exact isVagueLimitOn_univ_lqgApprox_comp_add H z

end LQGMeasureChart

end MatedCRT
