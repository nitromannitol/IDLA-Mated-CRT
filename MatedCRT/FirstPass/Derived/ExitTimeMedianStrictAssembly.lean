import MatedCRT.FirstPass.Derived.ExitTimeMedianStrictPositivity
import MatedCRT.FirstPass.Derived.ExitTimeClockAtExit
import MatedCRT.FirstPass.Derived.ExitTimeGaussianIndependence
import MatedCRT.FirstPass.Derived.ExitTimeFieldSplit
import MatedCRT.FirstPass.Derived.ExitTimeMeasurableVersion
import MatedCRT.FirstPass.Derived.ExitTimeTildeFieldIndependence

/-!
# The annealed exit-time law of Liouville Brownian motion from `B_{1/2}` charges every interval

Let `T(ω, b) = lbmExitTime (S.clock ω) (ball 0 (1/2)) b` be the exit time of Liouville Brownian motion from the disc
of radius `1/2`, driven by a planar Brownian path `b` from `0`, in the environment `ω`. In the mating-of-trees
coupling the circle-average field on `B_{1/2}` is `B_{t₀} + h̃` with `t₀ = log (5/3)` (`splitTime`), where `B_{t₀}`
is a centred Gaussian of variance `t₀` independent of the lateral field `X` and of the later radial increments
`u ↦ B_{t₀ + u} - B_{t₀}`, of which `h̃` is a function. The LQG clock factors accordingly, so that a jointly
measurable version `T*` of `T` is `e^{γ B_{t₀}} T̃*`, with `T̃*` a measurable function `Ψ` of the lateral field, the
later radial increments and the Brownian path. Then `T*` charges every interval `(a, c]` with `0 < a < c`, and the
annealed distribution function `G s = ∫ P^0[T(ω, ·) ≤ s] dP(ω)` is strictly above `1/2` to the right of its lower
median `S.m₀`.

Here the factorised version enters through the hypotheses `hTm` (`T*` measurable), `hT` (`T*(ω, ·) = T(ω, ·)`
`P^0`-a.s. for `S.P`-a.e. `ω`), `hΨ` (`Ψ` measurable) and `hsplit` (`T* = e^{γ B_{t₀}} Ψ(X, (B_{t₀+u} - B_{t₀})_u, b)`
`S.P ⊗ P^0`-a.s.); `Ψ` may be real-valued or, through `MatedCRTEnv.IsValid.ae_prod_exitTime_eq_ofReal_exp_mul_toReal`,
`[0, ∞]`-valued.

* `ofReal_mem_Ioc_ofReal_iff`: `ofReal x ∈ (ofReal a, ofReal c]` iff `x ∈ (a, c]`, for `a > 0`.
* `measure_prod_mem_Ioc_pos_of_ae_eq_ofReal_exp_mul`: under `P.prod Q`, a positive variable `T* = e^{θ Y} Ψ(Z, b)`
  with `Y` centred Gaussian, `Y ⊥ Z` under `P`, charges every interval `(a, c]`; `Y` and `Z` need not be
  measurable, only `Y` a.e. measurable and `Z` with a measurable modification in the sense of a.e. equal preimages
  of measurable sets.
* `ae_prod_fst_of_ae`, `ae_prod_mem_of_ae_ae_eq`, `measure_prod_preimage_eq_lintegral_of_ae_ae_eq`: a jointly
  measurable version `T*` of a sectionwise defined `T` computes the annealed law of `T`.
* `half_lt_lintegral_measure_le_of_medianOf_lt`: the strict median bound for the annealed law of `T`.
* `MatedCRTEnv.IsValid.measure_prod_exitTime_mem_Ioc_pos_of_split`: positivity on intervals for a version `T*` that
  factors as `e^{γ B_{t₀}} Ψ(X, (B_{t₀+u} - B_{t₀})_u, b)`.
* `MatedCRTEnv.IsValid.ae_prod_lt_top_of_ae_ae_eq_exitTime`: every jointly measurable version of the exit time is
  almost surely finite.
* `ae_eq_ofReal_mul_toReal_of_ae_eq_ofReal_mul`, `MatedCRTEnv.IsValid.ae_prod_exitTime_eq_ofReal_exp_mul_toReal`:
  a factorisation with a `[0, ∞]`-valued `Ψ` is one with the real-valued `Ψ.toReal`.
* `MatedCRTEnv.IsValid.lintegral_exitTime_mem_Ioc_pos_of_split`,
  `MatedCRTEnv.IsValid.measure_prod_mem_Ioc_pos_of_ae_ae_eq_exitTime_of_split`: the annealed exit-time law, and the
  law of every jointly measurable version of the exit time, charge every interval `(a, c]` with `0 < a < c`.
* `MatedCRTEnv.IsValid.half_lt_measure_prod_le_of_medianOf_lt_of_split`,
  `MatedCRTEnv.IsValid.half_lt_lintegral_exitTime_le_of_m₀_lt_of_split`: the distribution function exceeds `1/2`
  strictly above its lower median; in particular `G s > 1/2` for every `s > S.m₀`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- For `a > 0` and `c ≥ 0`, `ofReal x ∈ (ofReal a, ofReal c]` if and only if `x ∈ (a, c]`. -/
theorem ofReal_mem_Ioc_ofReal_iff {a c x : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ENNReal.ofReal x ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c) ↔ x ∈ Ioc a c := by
  simp only [mem_Ioc, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le, ENNReal.ofReal_le_ofReal_iff hc]

/-- The split time `t₀ = log (5/3)` is positive. -/
theorem splitTime_ne_zero : splitTime ≠ 0 := by
  intro h
  have h1 : ((splitTime : ℝ≥0) : ℝ) = 0 := by rw [h, NNReal.coe_zero]
  have h2 : ((splitTime : ℝ≥0) : ℝ) = Real.log (5 / 3) := rfl
  have h3 : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num)
  linarith

section Abstract

variable {Ω β Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace Ξ]

/-- **Positivity of a log-normal factorisation on intervals, product form.** Under `P.prod Q`, let
`T* = e^{θ Y} Ψ(Z, b)` almost surely with `T* > 0` almost surely, where `Y` has the centred Gaussian law of variance
`v ≠ 0` under `P` and is independent of `Z`, and `Ψ` is measurable. `Y` is only assumed a.e. measurable, and `Z` to
have a measurable modification `Z'` in the sense of a.e. equal preimages of measurable sets. Then `T*` charges every
interval `(a, c]` with `0 < a < c`. -/
theorem measure_prod_mem_Ioc_pos_of_ae_eq_ofReal_exp_mul {P : Measure Ω} {Q : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {Y : Ω → ℝ} {Z Z' : Ω → Ξ}
    (hY : AEMeasurable Y P) (hZ' : Measurable Z')
    (hZZ : ∀ Γ, MeasurableSet Γ → Z ⁻¹' Γ =ᵐ[P] Z' ⁻¹' Γ) {v : ℝ≥0} (hv : v ≠ 0)
    (hYlaw : P.map Y = gaussianReal 0 v) (hind : IndepFun Y Z P) {Ψ : Ξ × β → ℝ} (hΨ : Measurable Ψ)
    {θ : ℝ} (hθ : 0 < θ) {Tstar : Ω × β → ℝ≥0∞} (hT0 : ∀ᵐ p ∂(P.prod Q), 0 < Tstar p)
    (hsplit : ∀ᵐ p ∂(P.prod Q), Tstar p = ENNReal.ofReal (Real.exp (θ * Y p.1) * Ψ (Z p.1, p.2)))
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < (P.prod Q) {p | Tstar p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)} := by
  obtain ⟨Y', hY'm, hYeq⟩ := hY
  have hYY : ∀ s, MeasurableSet s → Y ⁻¹' s =ᵐ[P] Y' ⁻¹' s := fun s _ => by
    filter_upwards [hYeq] with ω hω
    change (Y ω ∈ s) = (Y' ω ∈ s)
    rw [hω]
  -- the triple `(Y ∘ fst, (Z ∘ fst, snd))` and its measurable modification
  have hF : ∀ Γ : Set (ℝ × (Ξ × β)), MeasurableSet Γ →
      (fun p : Ω × β => (Y p.1, (Z p.1, p.2))) ⁻¹' Γ =ᵐ[P.prod Q]
        (fun p : Ω × β => (Y' p.1, (Z' p.1, p.2))) ⁻¹' Γ := by
    intro Γ hΓ
    refine preimage_ae_eq_prodMk (f := fun p : Ω × β => Y p.1) (f' := fun p => Y' p.1)
      (g := fun p : Ω × β => (Z p.1, p.2)) (g' := fun p => (Z' p.1, p.2))
      (preimage_comp_fst_ae_eq (Q := Q) hYY) ?_ hΓ
    intro s hs
    exact preimage_ae_eq_prodMk (f := fun p : Ω × β => Z p.1) (f' := fun p => Z' p.1)
      (g := fun p : Ω × β => p.2) (g' := fun p => p.2) (preimage_comp_fst_ae_eq (Q := Q) hZZ)
      (fun _ _ => Filter.EventuallyEq.rfl) hs
  -- independence and law for the modification
  have hind' : IndepFun Y' Z' P := indepFun_of_preimage_ae_eq hYY hZZ hind
  have hindp : IndepFun (fun p : Ω × β => Y' p.1) (fun p => Ψ (Z' p.1, p.2)) (P.prod Q) :=
    indepFun_comp_fst_comp_prodMk_snd hY'm hZ' hind' hΨ
  have hlaw : (P.prod Q).map (fun p : Ω × β => Y' p.1) = gaussianReal 0 v := by
    rw [show (fun p : Ω × β => Y' p.1) = Y' ∘ Prod.fst from rfl,
      ← Measure.map_map hY'm measurable_fst, Measure.map_fst_prod, measure_univ, one_smul,
      ← Measure.map_congr hYeq, hYlaw]
  -- positivity of the factor `Ψ`, first for `Z`, then for the modification
  have hW : ∀ᵐ p ∂(P.prod Q), 0 < Ψ (Z p.1, p.2) := by
    filter_upwards [hT0, hsplit] with p h0 heq
    rw [heq, ENNReal.ofReal_pos] at h0
    exact pos_of_mul_pos_right h0 (Real.exp_pos _).le
  have hW' : ∀ᵐ p ∂(P.prod Q), 0 < Ψ (Z' p.1, p.2) := by
    have hm : MeasurableSet {q : ℝ × (Ξ × β) | 0 < Ψ q.2} :=
      measurableSet_lt measurable_const (hΨ.comp measurable_snd)
    filter_upwards [(hF _ hm).mem_iff, hW] with p hp1 hp2
    exact hp1.1 hp2
  -- the event `T* ∈ (a, c]` through the modification
  have hE : MeasurableSet {q : ℝ × (Ξ × β) | Real.exp (θ * q.1) * Ψ q.2 ∈ Ioc a c} :=
    measurableSet_Ioc.preimage
      ((Real.measurable_exp.comp (measurable_fst.const_mul θ)).mul (hΨ.comp measurable_snd))
  have hset : {p | Tstar p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)} =ᵐ[P.prod Q]
      (fun p : Ω × β => (Y' p.1, (Z' p.1, p.2))) ⁻¹'
        {q : ℝ × (Ξ × β) | Real.exp (θ * q.1) * Ψ q.2 ∈ Ioc a c} := by
    refine EventuallyEq.trans ?_ (hF _ hE)
    filter_upwards [hsplit] with p hp
    change (Tstar p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)) =
      (Real.exp (θ * Y p.1) * Ψ (Z p.1, p.2) ∈ Ioc a c)
    rw [hp, ofReal_mem_Ioc_ofReal_iff ha (ha.trans hac).le]
  rw [measure_congr hset]
  exact measure_exp_mul_mem_Ioc_pos (hY'm.comp measurable_fst)
    (hΨ.comp ((hZ'.comp measurable_fst).prodMk measurable_snd)) hv hlaw hW' hindp hθ ha hac

/-- A property of the first coordinate holding `P`-almost surely holds `P.prod Q`-almost surely (no measurability
needed). -/
theorem ae_prod_fst_of_ae {P : Measure Ω} {Q : Measure β} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {q : Ω → Prop} (h : ∀ᵐ ω ∂P, q ω) : ∀ᵐ p ∂(P.prod Q), q p.1 := by
  rw [ae_iff] at h ⊢
  rw [show {p : Ω × β | ¬ q p.1} = Prod.fst ⁻¹' {ω | ¬ q ω} from rfl, measure_prod_preimage_fst]
  exact h

/-- A property of a sectionwise defined `T` holding for `P`-a.e. `ω` and `Q`-a.e. `b` holds `P.prod Q`-a.e. for a
jointly measurable version `T*` of `T`. -/
theorem ae_prod_mem_of_ae_ae_eq {P : Measure Ω} {Q : Measure β} [SFinite P] [SFinite Q]
    {Tstar : Ω × β → ℝ≥0∞} (hTm : Measurable Tstar) {T : Ω → β → ℝ≥0∞}
    (hT : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, Tstar (ω, b) = T ω b) {E : Set ℝ≥0∞} (hE : MeasurableSet E)
    (h : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, T ω b ∈ E) : ∀ᵐ p ∂(P.prod Q), Tstar p ∈ E := by
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (hTm hE)).2 ?_
  filter_upwards [hT, h] with ω h1 h2
  filter_upwards [h1, h2] with b hb1 hb2
  show Tstar (ω, b) ∈ E
  rw [hb1]
  exact hb2

/-- A jointly measurable version `T*` of a sectionwise defined `T` computes the annealed law of `T`:
`(P.prod Q) {T* ∈ E} = ∫ Q {T(ω, ·) ∈ E} dP(ω)`. -/
theorem measure_prod_preimage_eq_lintegral_of_ae_ae_eq {P : Measure Ω} {Q : Measure β} [SFinite Q]
    {Tstar : Ω × β → ℝ≥0∞} (hTm : Measurable Tstar) {T : Ω → β → ℝ≥0∞}
    (hT : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, Tstar (ω, b) = T ω b) {E : Set ℝ≥0∞} (hE : MeasurableSet E) :
    (P.prod Q) {p | Tstar p ∈ E} = ∫⁻ ω, Q {b | T ω b ∈ E} ∂P := by
  rw [show {p | Tstar p ∈ E} = Tstar ⁻¹' E from rfl, Measure.prod_apply (hTm hE)]
  refine lintegral_congr_ae ?_
  filter_upwards [hT] with ω hω
  refine measure_congr ?_
  filter_upwards [hω] with b hb
  change (Tstar (ω, b) ∈ E) = (T ω b ∈ E)
  rw [hb]

/-- **Strict median bound for an annealed law.** Let `T` be defined sectionwise, with a jointly measurable version
`T*` under `P.prod Q`. If `T` is almost surely finite and `T*` charges every interval `(a, c]` with `0 < a < c`,
then the annealed distribution function `G s = ∫ Q {T(ω, ·) ≤ s} dP(ω)` is strictly above `1/2` to the right of its
lower median. -/
theorem half_lt_lintegral_measure_le_of_medianOf_lt {P : Measure Ω} {Q : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {Tstar : Ω × β → ℝ≥0∞} (hTm : Measurable Tstar)
    {T : Ω → β → ℝ≥0∞} (hT : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, Tstar (ω, b) = T ω b)
    (hfin : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, T ω b < ∞)
    (hpos : ∀ a c : ℝ, 0 < a → a < c →
      0 < (P.prod Q) {p | Tstar p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)})
    {s : ℝ} (hs : medianOf (fun r => ∫⁻ ω, Q {b | T ω b ≤ ENNReal.ofReal r} ∂P) < s) :
    (1 / 2 : ℝ≥0∞) < ∫⁻ ω, Q {b | T ω b ≤ ENNReal.ofReal s} ∂P := by
  have hG : (fun r => ∫⁻ ω, Q {b | T ω b ≤ ENNReal.ofReal r} ∂P) =
      fun r => (P.prod Q) {p | Tstar p ≤ ENNReal.ofReal r} := by
    funext r
    exact (measure_prod_preimage_eq_lintegral_of_ae_ae_eq hTm hT measurableSet_Iic).symm
  rw [hG] at hs
  rw [congrFun hG s]
  exact half_lt_measure_le_of_medianOf_lt hTm
    (ae_prod_mem_of_ae_ae_eq hTm hT measurableSet_Iio hfin) hpos hs

end Abstract

section Environment

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The exit time of Liouville Brownian motion from `B_{1/2}` charges every interval**, for a jointly measurable
version `T*` of it under `S.P.prod P^0` that factors as `T* = e^{γ B_{t₀}} Ψ(X, (B_{t₀ + u} - B_{t₀})_u, b)` with a
measurable `Ψ`, where `(X, B, …)` is a mating-of-trees coupling of the environment and `t₀ = log (5/3)`. -/
theorem MatedCRTEnv.IsValid.measure_prod_exitTime_mem_Ioc_pos_of_split {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ}
    (hΨ : Measurable Ψ)
    (hsplit : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
        Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)))
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < (S.P.prod (planarBrownianMotion 0))
      {p | Tstar p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)} := by
  have := hS.isProbabilityMeasure
  obtain ⟨hind, hlaw⟩ := isMatingOfTreesCoupling_indepFun_eval_prodMk_increments hcpl splitTime
  have hBae : ∀ u, AEMeasurable (B u) S.P := hcpl.bm_B.toIsPreBrownianReal.aemeasurable
  obtain ⟨Z', hZ'm, hZZ⟩ :=
    exists_measurable_preimage_ae_eq_prodMk_increments hcpl.gff.measurable hBae splitTime
  have hT0 : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)), Tstar p ∈ Ioi 0 := by
    refine ae_prod_mem_of_ae_ae_eq hTm hT measurableSet_Ioi ?_
    filter_upwards [MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_pos_lt_top hS] with ω hω
    filter_upwards [hω] with b hb
    exact hb.1
  exact measure_prod_mem_Ioc_pos_of_ae_eq_ofReal_exp_mul (hBae splitTime) hZ'm hZZ
    splitTime_ne_zero hlaw hind hΨ hγ hT0 hsplit ha hac

/-- **(hfin) Every jointly measurable version of the exit time is almost surely finite.** If `T*` is measurable on
`Ω × ContinuousPath ℂ` and `T*(ω, ·) = τ^{LBM}_{B_{1/2}}` `P^0`-a.s. for `S.P`-a.e. `ω`, then `T* < ∞`
`S.P ⊗ P^0`-almost surely. -/
theorem MatedCRTEnv.IsValid.ae_prod_lt_top_of_ae_ae_eq_exitTime {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) :
    ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)), Tstar p < ∞ := by
  have := hS.isProbabilityMeasure
  refine ae_prod_mem_of_ae_ae_eq (E := Iio ∞) hTm hT measurableSet_Iio ?_
  filter_upwards [MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_pos_lt_top hS] with ω hω
  filter_upwards [hω] with b hb
  exact hb.2

/-- If `T = e^f Ψ` almost everywhere, with `T` almost everywhere finite, `f > 0` real and `Ψ` valued in `[0, ∞]`,
then `T = ofReal (f · Ψ.toReal)` almost everywhere. -/
theorem ae_eq_ofReal_mul_toReal_of_ae_eq_ofReal_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T Ψ : α → ℝ≥0∞} {f : α → ℝ} (hfin : ∀ᵐ x ∂μ, T x < ∞) (hf : ∀ x, 0 < f x)
    (h : ∀ᵐ x ∂μ, T x = ENNReal.ofReal (f x) * Ψ x) :
    ∀ᵐ x ∂μ, T x = ENNReal.ofReal (f x * (Ψ x).toReal) := by
  filter_upwards [hfin, h] with x hx hTx
  have hΨ : Ψ x ≠ ∞ := by
    intro hΨ
    rw [hTx, hΨ, ENNReal.mul_top (ENNReal.ofReal_pos.2 (hf x)).ne'] at hx
    exact lt_irrefl _ hx
  rw [hTx, ENNReal.ofReal_mul (hf x).le, ENNReal.ofReal_toReal hΨ]

/-- A factorisation `T* = e^{γ B_{t₀}} Ψ(X, (B_{t₀+u} - B_{t₀})_u, b)` of a jointly measurable version `T*` of the
exit time with a `[0, ∞]`-valued `Ψ` is one with the real-valued `Ψ.toReal` (measurable if `Ψ` is), since `T*` is
almost surely finite. -/
theorem MatedCRTEnv.IsValid.ae_prod_exitTime_eq_ofReal_exp_mul_toReal {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {X : Ω → MatedCRTHarmonic.MatedCRT.Field} {B : ℝ≥0 → Ω → ℝ}
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ≥0∞}
    (hsplit : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1)) *
        Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)) :
    ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
        (Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)).toReal) :=
  ae_eq_ofReal_mul_toReal_of_ae_eq_ofReal_mul (hS.ae_prod_lt_top_of_ae_ae_eq_exitTime hTm hT)
    (fun _ => Real.exp_pos _) hsplit

/-- **(hpos) The annealed exit-time law of Liouville Brownian motion from `B_{1/2}` charges every interval**, given a
jointly measurable version `T*` of the exit time that factors as `T* = e^{γ B_{t₀}} Ψ(X, (B_{t₀+u} - B_{t₀})_u, b)`
with a measurable `Ψ`: `∫ P^0[τ^{LBM}_{B_{1/2}} ∈ (a, c]] dP > 0` for all `0 < a < c`. -/
theorem MatedCRTEnv.IsValid.lintegral_exitTime_mem_Ioc_pos_of_split {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ}
    (hΨ : Measurable Ψ)
    (hsplit : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
        Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)))
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < ∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)}
      ∂S.P := by
  rw [← measure_prod_preimage_eq_lintegral_of_ae_ae_eq hTm hT measurableSet_Ioc]
  exact hS.measure_prod_exitTime_mem_Ioc_pos_of_split hγ hcpl hTm hT hΨ hsplit ha hac

/-- **(hpos) Every jointly measurable version of the exit time charges every interval.** Given a factorised version
`T*` as in `MatedCRTEnv.IsValid.measure_prod_exitTime_mem_Ioc_pos_of_split`, every measurable `V` on
`Ω × ContinuousPath ℂ` with `V(ω, ·) = τ^{LBM}_{B_{1/2}}` `P^0`-a.s. for `S.P`-a.e. `ω` (for instance the version of
`MatedCRTEnv.IsValid.exists_measurable_lbmExitTime_ball_half_version`) satisfies `(S.P ⊗ P^0) {V ∈ (a, c]} > 0` for
all `0 < a < c`. -/
theorem MatedCRTEnv.IsValid.measure_prod_mem_Ioc_pos_of_ae_ae_eq_exitTime_of_split {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ}
    (hΨ : Measurable Ψ)
    (hsplit : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
        Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)))
    {V : Ω × ContinuousPath ℂ → ℝ≥0∞} (hVm : Measurable V)
    (hV : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      V (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    0 < (S.P.prod (planarBrownianMotion 0))
      {p | V p ∈ Ioc (ENNReal.ofReal a) (ENNReal.ofReal c)} := by
  rw [measure_prod_preimage_eq_lintegral_of_ae_ae_eq hVm hV measurableSet_Ioc]
  exact hS.lintegral_exitTime_mem_Ioc_pos_of_split hγ hcpl hTm hT hΨ hsplit ha hac

/-- **(hstrict) Strict median bound for every jointly measurable version of the exit time**, in the form of
`half_lt_measure_le_of_medianOf_lt` with `μ = S.P ⊗ P^0`, given a factorised version `T*` as in
`MatedCRTEnv.IsValid.measure_prod_exitTime_mem_Ioc_pos_of_split`: the distribution function of `V` is strictly above
`1/2` to the right of its lower median. -/
theorem MatedCRTEnv.IsValid.half_lt_measure_prod_le_of_medianOf_lt_of_split {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ}
    (hΨ : Measurable Ψ)
    (hsplit : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
        Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)))
    {V : Ω × ContinuousPath ℂ → ℝ≥0∞} (hVm : Measurable V)
    (hV : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      V (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) {s : ℝ}
    (hs : medianOf (fun r => (S.P.prod (planarBrownianMotion 0)) {p | V p ≤ ENNReal.ofReal r}) < s) :
    (1 / 2 : ℝ≥0∞) < (S.P.prod (planarBrownianMotion 0)) {p | V p ≤ ENNReal.ofReal s} := by
  have := hS.isProbabilityMeasure
  exact half_lt_measure_le_of_medianOf_lt hVm (hS.ae_prod_lt_top_of_ae_ae_eq_exitTime hVm hV)
    (fun a c ha hac => hS.measure_prod_mem_Ioc_pos_of_ae_ae_eq_exitTime_of_split hγ hcpl hTm hT hΨ
      hsplit hVm hV ha hac) hs

/-- **(hstrict) Strict median bound for the annealed exit-time law of Liouville Brownian motion from `B_{1/2}`**,
given a factorised version `T*` as in `MatedCRTEnv.IsValid.measure_prod_exitTime_mem_Ioc_pos_of_split`: the annealed
distribution function `G s = ∫ P^0[τ^{LBM}_{B_{1/2}} ≤ s] dP` exceeds `1/2` for every `s` strictly larger than its
lower median `m₀ = S.m₀` (eq:mo). -/
theorem MatedCRTEnv.IsValid.half_lt_lintegral_exitTime_le_of_m₀_lt_of_split {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    {Tstar : Ω × ContinuousPath ℂ → ℝ≥0∞} (hTm : Measurable Tstar)
    (hT : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      Tstar (ω, b) = lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b)
    {Ψ : (MatedCRTHarmonic.MatedCRT.Field × (ℝ≥0 → ℝ)) × ContinuousPath ℂ → ℝ}
    (hΨ : Measurable Ψ)
    (hsplit : ∀ᵐ p ∂(S.P.prod (planarBrownianMotion 0)),
      Tstar p = ENNReal.ofReal (Real.exp (γ * B splitTime p.1) *
        Ψ ((X p.1, fun u : ℝ≥0 => B (splitTime + u) p.1 - B splitTime p.1), p.2)))
    (s : ℝ) (hs : S.m₀ < s) :
    (1 / 2 : ℝ≥0∞) < ∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal s} ∂S.P := by
  have := hS.isProbabilityMeasure
  have hfin : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion 0,
      lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b < ∞ := by
    filter_upwards [MatedCRTEnv.IsValid.ae_lbmExitTime_ball_half_pos_lt_top hS] with ω hω
    filter_upwards [hω] with b hb
    exact hb.2
  exact half_lt_lintegral_measure_le_of_medianOf_lt
    (T := fun ω b => lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) hTm hT hfin
    (fun a c ha hac => hS.measure_prod_exitTime_mem_Ioc_pos_of_split hγ hcpl hTm hT hΨ hsplit ha hac) hs

end Environment

end MatedCRT
