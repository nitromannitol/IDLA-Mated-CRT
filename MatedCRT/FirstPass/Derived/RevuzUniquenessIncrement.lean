import MatedCRT.FirstPass.Derived.RevuzUniquenessAdapted
import MatedCRT.FirstPass.Derived.RevuzWeightedDensity
import MatedCRT.FirstPass.Derived.PlanarOptionalTimeStrongMarkov
import MatedCRT.FirstPass.Derived.PCAFStartUpgrade
import MatedCRT.FirstPass.Derived.PlanarBrownianStoppedOccupationBound

/-!
# Martingale increments of the difference of two clocks with the same Revuz measure

Let `A`, `A'` be positive continuous additive functionals of planar Brownian motion with the same Revuz measure `μ`,
let `h ≥ 0` be Borel with `∫ h dμ < ∞`, and write `N_t = A^h_t - A'^h_t` for the difference of the window integrals
`A^h_t = ∫_{(0,t]} h(B_s) dĀ_s`. We prove that for a starting point `x` with `E_x[A^h_{s+δ}] < ∞` and
`E_x[A'^h_{s+δ}] < ∞`, a time `s > 0` and a bounded functional `G` of the canonical filtration at time `s`,
`E_x[G (N_{s+δ} - N_s)] = 0`.

Along almost every path the increment `A^h_{s+δ} - A^h_s` is the window integral `A^h_δ ∘ θ_s` of the shifted path.
By the simple Markov property at time `s`, `E_x[V · A^h_δ ∘ θ_s] = E_x[V · a^h_δ(B_s)]` for every `F_s`-measurable
`V ≥ 0`, with `a^h_δ(y) = E_y[A^h_δ]`. The expectations `a^h_δ` and `a'^h_δ` agree Lebesgue-almost everywhere, and
the law of `B_s` under `P_x` is absolutely continuous, so `a^h_δ(B_s) = a'^h_δ(B_s)` almost surely
(Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4; Revuz–Yor (1999), Chapter X, Theorem 2.6).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **Additivity of the window integral along a path.** For a PCAF `A`, almost surely
`A^h_{s+δ} = A^h_s + A^h_δ ∘ θ_s`. -/
theorem ae_clockWindowIntegral_add_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (z : ℂ) {h : ℂ → ℝ≥0∞} (hh : Measurable h) (s δ : ℝ≥0) :
    ∀ᵐ ω ∂planarLaw z, clockWindowIntegral A h ((s + δ : ℝ≥0) : ℝ) ω =
      clockWindowIntegral A h s ω + clockWindowIntegral A h δ (LatticeProb.pathShift ω s) := by
  filter_upwards [hA.path z, ae_setLIntegral_Ioc_shift_window_eq hA z s hh δ] with ω hp hw
  have hreg : (fun u => regularize A u ω) = fun u => A u ω :=
    funext (regularize_eq_of_continuous_monotone hp.2.1 hp.2.2)
  rw [← hw]
  unfold clockWindowIntegral
  rw [hreg, NNReal.coe_add, ← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
    Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s) (le_add_of_nonneg_right δ.coe_nonneg)]

/-- **Simple Markov property at a fixed time, with a weight of the past.** For an `F_s`-measurable `V ≥ 0` and a
measurable functional `F ≥ 0`, `E_x[V · F ∘ θ_s] = E_x[V · E_{B_s}[F]]`. -/
theorem lintegral_mul_pathShift_planarLaw_eq (x : ℂ) {s : ℝ≥0} {V : ContinuousPath ℂ → ℝ≥0∞}
    (hV : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) s] V) {F : ContinuousPath ℂ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, V ω * F (LatticeProb.pathShift ω s) ∂planarLaw x =
      ∫⁻ ω, V ω * ∫⁻ ω', F ω' ∂planarLaw (ω s) ∂planarLaw x := by
  have hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω : ContinuousPath ℂ | ((s : ℝ≥0) : WithTop ℝ≥0) < t} := fun t => by
    by_cases hst : ((s : ℝ≥0) : WithTop ℝ≥0) < t
    · simp only [hst, ofPred_true]
      exact @MeasurableSet.univ _ (ContinuousPath.canonicalFiltration (alpha := ℂ) t)
    · simp only [hst, ofPred_false]
      exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := ℂ) t)
  have hVm : Measurable V := hV.mono ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le s) le_rfl
  have hV' : ∀ B : Set ℝ≥0∞, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (V ⁻¹' B ∩ {ω : ContinuousPath ℂ | ((s : ℝ≥0) : WithTop ℝ≥0) < t}) := fun B hB t => by
    by_cases hst : ((s : ℝ≥0) : WithTop ℝ≥0) < t
    · simp only [hst, ofPred_true, inter_univ]
      exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).mono (WithTop.coe_lt_coe.1 hst).le _ (hV hB)
    · simp only [hst, ofPred_false, inter_empty]
      exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := ℂ) t)
  have hH : Measurable fun p : ℝ≥0∞ × ContinuousPath ℂ => p.1 * F p.2 :=
    measurable_fst.mul (hF.comp measurable_snd)
  have key := OptionalTime.lintegral_planarLaw_shift_optionalTime_param x (fun _ => ((s : ℝ≥0) : WithTop ℝ≥0)) hT V hVm
    hV' hH
  have huniv : {ω : ContinuousPath ℂ | ((s : ℝ≥0) : WithTop ℝ≥0) < ⊤} = univ :=
    eq_univ_of_forall fun _ => WithTop.coe_lt_top s
  simp only [huniv, Measure.restrict_univ, WithTop.untopD_coe] at key
  have hs : ∀ ω : ContinuousPath ℂ, LatticeProb.pathShift ω s = ContinuousPath.shift s ω :=
    fun ω => congrFun (pathShift_eq_shift s) ω
  simp_rw [hs]
  rw [key]
  exact lintegral_congr fun ω => lintegral_const_mul _ hF

/-- A Lebesgue-almost-everywhere property holds at the position `B_s`, `s > 0`, almost surely under every `P_x`. -/
theorem ae_eval_of_ae_volume (x : ℂ) {s : ℝ≥0} (hs : s ≠ 0) {p : ℂ → Prop}
    (hp : ∀ᵐ y ∂(volume : Measure ℂ), p y) : ∀ᵐ ω ∂planarLaw x, p (ω s) := by
  have h1 : ∀ᵐ y ∂HarmonicBalls.planarGaussian x s, p y :=
    (planarGaussian_absolutelyContinuous x hs).ae_le hp
  rw [← KilledOccupation.map_eval_planarBrownianMotion x s] at h1
  exact ae_of_ae_map (continuous_eval_const s).measurable.aemeasurable h1

/-- **The shifted window integrals have the same weighted expectations.** For PCAFs with the same Revuz measure,
`∫ h dμ < ∞`, `s > 0` and an `F_s`-measurable `V ≥ 0`, `E_x[V · A^h_δ ∘ θ_s] = E_x[V · A'^h_δ ∘ θ_s]`. -/
theorem lintegral_mul_clockWindowIntegral_pathShift_eq {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') (hμ : revuz planarLaw A = revuz planarLaw A')
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞) (x : ℂ) {s : ℝ≥0}
    (hs : s ≠ 0) (δ : ℝ≥0) {V : ContinuousPath ℂ → ℝ≥0∞}
    (hV : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) s] V) :
    ∫⁻ ω, V ω * clockWindowIntegral A h δ (LatticeProb.pathShift ω s) ∂planarLaw x =
      ∫⁻ ω, V ω * clockWindowIntegral A' h δ (LatticeProb.pathShift ω s) ∂planarLaw x := by
  rw [lintegral_mul_pathShift_planarLaw_eq x hV (measurable_clockWindowIntegral hA.meas hh _),
    lintegral_mul_pathShift_planarLaw_eq x hV (measurable_clockWindowIntegral hA'.meas hh _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_eval_of_ae_volume x hs
    (ae_lintegral_clockWindowIntegral_eq_of_revuz_eq hA hA' hμ hh hfin δ)] with ω hω
  rw [hω]

/-- **Martingale increments of the difference of two clocks.** Let `A`, `A'` be PCAFs of planar Brownian motion
with the same Revuz measure `μ`, `h ≥ 0` Borel with `∫ h dμ < ∞`, and `N_t = A^h_t - A'^h_t`. If
`E_x[A^h_{s+δ}]` and `E_x[A'^h_{s+δ}]` are finite, `s > 0`, and `G` is a functional of the canonical filtration at
time `s` with `|G| ≤ 1`, then `E_x[G (N_{s+δ} - N_s)] = 0`. -/
theorem integral_mul_clockWindowIntegral_increment_eq_zero {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') (hμ : revuz planarLaw A = revuz planarLaw A')
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞) {x : ℂ} {s : ℝ≥0}
    (hs : s ≠ 0) (δ : ℝ≥0)
    (hx : ∫⁻ ω, clockWindowIntegral A h ((s + δ : ℝ≥0) : ℝ) ω ∂planarLaw x ≠ ∞)
    (hx' : ∫⁻ ω, clockWindowIntegral A' h ((s + δ : ℝ≥0) : ℝ) ω ∂planarLaw x ≠ ∞)
    {G : ContinuousPath ℂ → ℝ} (hG : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) s] G)
    (hG1 : ∀ ω, |G ω| ≤ 1) :
    ∫ ω, G ω * (((clockWindowIntegral A h ((s + δ : ℝ≥0) : ℝ) ω).toReal -
        (clockWindowIntegral A' h ((s + δ : ℝ≥0) : ℝ) ω).toReal) -
      ((clockWindowIntegral A h s ω).toReal - (clockWindowIntegral A' h s ω).toReal)) ∂planarLaw x = 0 := by
  set μx := planarLaw x
  have hle := (ContinuousPath.canonicalFiltration (alpha := ℂ)).le s
  have hGm : Measurable G := hG.mono hle le_rfl
  -- the shifted window integrals
  set X : ContinuousPath ℂ → ℝ≥0∞ := fun ω => clockWindowIntegral A h δ (LatticeProb.pathShift ω s) with hXdef
  set Y : ContinuousPath ℂ → ℝ≥0∞ := fun ω => clockWindowIntegral A' h δ (LatticeProb.pathShift ω s) with hYdef
  have hshm : Measurable fun ω : ContinuousPath ℂ => LatticeProb.pathShift ω s := by
    rw [pathShift_eq_shift s]
    exact (ContinuousPath.continuous_shift_fixed s).measurable
  have hXm : Measurable X := (measurable_clockWindowIntegral hA.meas hh _).comp hshm
  have hYm : Measurable Y := (measurable_clockWindowIntegral hA'.meas hh _).comp hshm
  have hadd := ae_clockWindowIntegral_add_eq hA x hh s δ
  have hadd' := ae_clockWindowIntegral_add_eq hA' x hh s δ
  have hlt := ae_lt_top (measurable_clockWindowIntegral hA.meas hh _) hx
  have hlt' := ae_lt_top (measurable_clockWindowIntegral hA'.meas hh _) hx'
  have hXlt : ∀ᵐ ω ∂μx, X ω < ∞ := by
    filter_upwards [hadd, hlt] with ω h1 h2
    rw [h1] at h2
    exact lt_of_le_of_lt le_add_self h2
  have hYlt : ∀ᵐ ω ∂μx, Y ω < ∞ := by
    filter_upwards [hadd', hlt'] with ω h1 h2
    rw [h1] at h2
    exact lt_of_le_of_lt le_add_self h2
  have hXfin : ∫⁻ ω, X ω ∂μx ≠ ∞ := by
    refine ne_top_of_le_ne_top hx (lintegral_mono_ae ?_)
    filter_upwards [hadd] with ω h1
    rw [h1]
    exact le_add_self
  have hYfin : ∫⁻ ω, Y ω ∂μx ≠ ∞ := by
    refine ne_top_of_le_ne_top hx' (lintegral_mono_ae ?_)
    filter_upwards [hadd'] with ω h1
    rw [h1]
    exact le_add_self
  -- the increment is the difference of the shifted window integrals
  have hinc : (fun ω => G ω * (((clockWindowIntegral A h ((s + δ : ℝ≥0) : ℝ) ω).toReal -
        (clockWindowIntegral A' h ((s + δ : ℝ≥0) : ℝ) ω).toReal) -
      ((clockWindowIntegral A h s ω).toReal - (clockWindowIntegral A' h s ω).toReal))) =ᵐ[μx]
      fun ω => G ω * (X ω).toReal - G ω * (Y ω).toReal := by
    filter_upwards [hadd, hadd', hlt, hlt'] with ω h1 h2 h3 h4
    rw [h1] at h3 ⊢
    rw [h2] at h4 ⊢
    rw [ENNReal.toReal_add (ENNReal.add_lt_top.1 h3).1.ne (ENNReal.add_lt_top.1 h3).2.ne,
      ENNReal.toReal_add (ENNReal.add_lt_top.1 h4).1.ne (ENNReal.add_lt_top.1 h4).2.ne]
    ring
  -- the weighted measures agree on the past
  have htrim : (μx.withDensity X).trim hle = (μx.withDensity Y).trim hle := by
    refine @Measure.ext _ (ContinuousPath.canonicalFiltration (alpha := ℂ) s) _ _ fun S hS => ?_
    rw [trim_measurableSet_eq hle hS, trim_measurableSet_eq hle hS, withDensity_apply _ (hle _ hS),
      withDensity_apply _ (hle _ hS)]
    have e : ∀ Z : ContinuousPath ℂ → ℝ≥0∞, (fun ω => S.indicator 1 ω * Z ω) = S.indicator Z :=
      fun Z => funext fun ω => by by_cases hω : ω ∈ S <;> simp [hω]
    rw [← lintegral_indicator (hle _ hS), ← lintegral_indicator (hle _ hS), ← e X, ← e Y]
    exact lintegral_mul_clockWindowIntegral_pathShift_eq hA hA' hμ hh hfin x hs δ
      (by
        let _ : MeasurableSpace (ContinuousPath ℂ) := ContinuousPath.canonicalFiltration (alpha := ℂ) s
        exact measurable_const.indicator hS)
  have hGX : ∫ ω, G ω * (X ω).toReal ∂μx = ∫ ω, G ω * (Y ω).toReal ∂μx := by
    have hXe : ∫ ω, G ω * (X ω).toReal ∂μx = ∫ ω, G ω ∂(μx.withDensity X).trim hle := by
      rw [← integral_trim hle hG.stronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hXm hXlt]
      simp only [smul_eq_mul, mul_comm]
    have hYe : ∫ ω, G ω * (Y ω).toReal ∂μx = ∫ ω, G ω ∂(μx.withDensity Y).trim hle := by
      rw [← integral_trim hle hG.stronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hYm hYlt]
      simp only [smul_eq_mul, mul_comm]
    rw [hXe, hYe, htrim]
  have hint : ∀ Z : ContinuousPath ℂ → ℝ≥0∞, Measurable Z → ∫⁻ ω, Z ω ∂μx ≠ ∞ →
      Integrable (fun ω => G ω * (Z ω).toReal) μx := fun Z hZm hZfin => by
    refine (integrable_toReal_of_lintegral_ne_top hZm.aemeasurable hZfin).mono'
      (hGm.mul hZm.ennreal_toReal).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg (hG1 ω)
  rw [integral_congr_ae hinc, integral_sub (hint X hXm hXfin) (hint Y hYm hYfin), hGX, sub_self]

end MatedCRT
