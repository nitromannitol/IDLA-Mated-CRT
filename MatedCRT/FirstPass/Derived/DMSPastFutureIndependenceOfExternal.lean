import MatedCRT.External.DMSPastFutureIndependence
import MatedCRT.FirstPass.Derived.WindowChartBGIndependence

/-!
# Independence of the past and future curve-decorated quantum surfaces at every time

Duplantier–Miller–Sheffield (arXiv:1409.7055v4), Theorem 1.9, gives the independence of the past and future
curve-decorated quantum surfaces of the `γ`-quantum cone decorated by space-filling SLE at time `0`, and the
invariance (1.9) of the law of the curve-decorated quantum surface under shifting by `t` units of LQG area time and
recentring (the cited input `DMSPastFutureIndependence`). This file derives the independence at every time `s`, the
named hypothesis `DMS21PastFutureIndependence` of `WindowChartBGIndependence.lean` used in Berestycki–Gwynne (2020),
proof of Lemma 7.21, (7.35).

The argument. Translations `z ↦ z + b` are re-embeddings of curve-decorated quantum surfaces
(`isCurveDecoratedReembedding_add`), so the recentring in (1.9) does not change the curve-decorated quantum surface of
the time-shifted pair `(h, η'(· + s))`. A re-embedding over all times restricts to a re-embedding over any set of
times (`IsCurveDecoratedReembedding.restrict`, by the open mapping theorem for the injective conformal map), so the
`σ`-algebras of the past and of the future are contained in the one over all times, on which (1.9) identifies the
laws of `(h, η')` and `(h, η'(· + s))`. Hence the past and future of the shifted pair at time `0` are independent,
and they generate the past and future of `(h, η')` at time `s`
(`comap_le_comap_curveTimeShift`).

## Main statements

* `curveDecoratedSurfaceSigma_eq`: the `σ`-algebra of the cited input is `curveSurfaceSigma`.
* `dms21PastFutureIndependence_of_external`: `DMS21PastFutureIndependence 𝒮` from `DMSPastFutureIndependence`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT

namespace DMSPastFuture

/-- The `σ`-algebra of the curve-decorated quantum surface of the cited input is `curveSurfaceSigma`. -/
theorem curveDecoratedSurfaceSigma_eq (γ : ℝ) (T : Set ℝ) :
    curveDecoratedSurfaceSigma γ T = curveSurfaceSigma γ T :=
  rfl

/-! ### Translations are re-embeddings -/

theorem isCurveDecoratedReembedding_add (γ : ℝ) (T : Set ℝ) (h : LQGMetric.DistC) (η₁ η₂ : C(ℝ, ℂ)) (b : ℂ)
    (hη : ∀ u, η₂ u + b = η₁ u) :
    IsCurveDecoratedReembedding γ T h η₁ (LQGMetric.affineComp 1 b h) η₂ (fun z => z + b) := by
  have himg : (fun z => z + b) '' (η₂ '' T) = η₁ '' T := by
    rw [image_image]
    simp only [hη]
  have hint : (fun z => z + b) '' interior (η₂ '' T) = interior (η₁ '' T) := by
    rw [← himg]
    exact (Homeomorph.addRight b).image_interior (η₂ '' T)
  have hderiv : ∀ x : ℂ, deriv (fun z : ℂ => z + b) x = 1 := fun x => by simp
  refine ⟨fun t _ => hη t, (add_left_injective b).injOn, (by fun_prop), (by fun_prop), hint, ?_⟩
  intro φ ψ hφ hψ hψ0
  have hψeq : ψ = LQGMetric.testAffinePull 1 b φ := by
    ext y
    rw [LQGMetric.testAffinePull_apply 1 b one_ne_zero, Complex.ofReal_one, div_one]
    by_cases hy : y ∈ (fun z => z + b) '' interior (η₂ '' T)
    · obtain ⟨x, hx, rfl⟩ := hy
      have hx' := hψ x hx
      simp only [hderiv, norm_one, one_pow, mul_one] at hx'
      simp only [add_sub_cancel_right]
      exact hx'
    · rw [hψ0 y hy]
      exact (image_eq_zero_of_notMem_tsupport fun hmem => hy ⟨y - b, hφ hmem, sub_add_cancel y b⟩).symm
  subst hψeq
  simp only [hderiv, norm_one, Real.log_one, zero_mul, integral_zero, mul_zero, add_zero]
  show (1 ^ 2 : ℝ)⁻¹ * h (LQGMetric.testAffinePull 1 b φ) = h (LQGMetric.testAffinePull 1 b φ)
  simp

/-! ### Time shifts -/

/-- The curve `η(· + c)`. -/
def timeShiftCurve (c : ℝ) (η : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun u => η (u + c), by fun_prop⟩

/-- The pair `(h, η(· + c))`. -/
def curveTimeShift (c : ℝ) (p : LQGMetric.DistC × C(ℝ, ℂ)) : LQGMetric.DistC × C(ℝ, ℂ) :=
  (p.1, timeShiftCurve c p.2)

theorem curveTimeShift_neg_curveTimeShift (c : ℝ) (p : LQGMetric.DistC × C(ℝ, ℂ)) :
    curveTimeShift (-c) (curveTimeShift c p) = p := by
  refine Prod.ext rfl (ContinuousMap.ext fun u => ?_)
  simp only [curveTimeShift, timeShiftCurve, ContinuousMap.coe_mk, neg_add_cancel_right]

private theorem measurableSpace_continuousMap_eq_comap_coe :
    (@ContinuousMap.measurableSpace ℝ ℂ _ _ : MeasurableSpace C(ℝ, ℂ)) =
      MeasurableSpace.comap (fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ)) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

theorem measurable_timeShiftCurve (c : ℝ) : Measurable (timeShiftCurve c) := by
  have h : Measurable fun η : C(ℝ, ℂ) => fun t : ℝ => η (t + c) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval (t + c)
  intro A hA
  have hA' : MeasurableSet[MeasurableSpace.comap (fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ)) MeasurableSpace.pi] A := by
    rw [← measurableSpace_continuousMap_eq_comap_coe]
    exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  exact h hB

theorem measurable_curveTimeShift (c : ℝ) : Measurable (curveTimeShift c) :=
  measurable_fst.prodMk ((measurable_timeShiftCurve c).comp measurable_snd)

/-- The pair `(h(· + η(t)), η(· + t) - η(t))` of (1.9) has the curve-decorated quantum surface of `(h, η(· + t))`. -/
theorem isSameCurveDecoratedSurface_recentre (γ : ℝ) (T : Set ℝ) (t : ℝ) (p : LQGMetric.DistC × C(ℝ, ℂ)) :
    IsSameCurveDecoratedSurface γ T (curveTimeShift t p) (lqgAreaTimeRecentre t p) :=
  ⟨fun z => z + p.2 t, isCurveDecoratedReembedding_add γ T p.1 (curveTimeShift t p).2
    (lqgAreaTimeRecentre t p).2 (p.2 t) fun _ => sub_add_cancel _ _⟩

/-- A re-embedding over the times `T` is one, for the time-shifted curves, over the times `T' = T - c`. -/
theorem isCurveDecoratedReembedding_timeShift {γ : ℝ} {T T' : Set ℝ} {c : ℝ} (hT : ∀ u, u ∈ T' ↔ u + c ∈ T)
    {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ}
    (hf : IsCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) :
    IsCurveDecoratedReembedding γ T' h₁ (timeShiftCurve c η₁) h₂ (timeShiftCurve c η₂) f := by
  have himg : ∀ η : C(ℝ, ℂ), timeShiftCurve c η '' T' = η '' T := by
    intro η
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u + c, (hT u).1 hu, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t - c, (hT (t - c)).2 (by rwa [sub_add_cancel]), ?_⟩
      simp only [timeShiftCurve, ContinuousMap.coe_mk, sub_add_cancel]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  rw [IsCurveDecoratedReembedding, himg, himg]
  exact ⟨fun u hu => h1 (u + c) ((hT u).1 hu), h2, h3, h4, h5, h6⟩

/-- The past (resp. future) of `(h, η)` after the time `s` generates no more than the past (resp. future) of
`(h, η(· + s))` after the time `0`: the `σ`-algebra of `p` over `T'` is contained in the one of the shifted pair over
`T = T' - s`. -/
theorem comap_le_comap_curveTimeShift (γ : ℝ) {T T' : Set ℝ} {c : ℝ} (hT : ∀ u, u ∈ T' ↔ u + -c ∈ T)
    {Ω : Type*} (p : Ω → LQGMetric.DistC × C(ℝ, ℂ)) :
    MeasurableSpace.comap p (curveDecoratedSurfaceSigma γ T') ≤
      MeasurableSpace.comap (fun ω => curveTimeShift c (p ω)) (curveDecoratedSurfaceSigma γ T) := by
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨curveTimeShift (-c) ⁻¹' A, ⟨measurable_curveTimeShift (-c) hA.1, fun p₁ p₂ hp => ?_⟩, ?_⟩
  · obtain ⟨f, hf⟩ := hp
    exact hA.2 (curveTimeShift (-c) p₁) (curveTimeShift (-c) p₂) ⟨f, isCurveDecoratedReembedding_timeShift hT hf⟩
  · ext ω
    simp only [mem_preimage, curveTimeShift_neg_curveTimeShift]

/-! ### Restriction of a re-embedding over all times -/

/-- A re-embedding over all times is a re-embedding over every set of times `T`. The only nontrivial point is that
`f` maps the interior of `η₂(T)` onto the interior of `η₁(T)`: `f` is injective and holomorphic on the interior of
`η₂(ℝ)`, hence an open map there (open mapping theorem). -/
theorem isCurveDecoratedReembedding_restrict {γ : ℝ} {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ}
    (hf : IsCurveDecoratedReembedding γ univ h₁ η₁ h₂ η₂ f) (T : Set ℝ) :
    IsCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have hT₂ : η₂ '' T ⊆ η₂ '' univ := image_mono (subset_univ T)
  have hW : interior (η₂ '' T) ⊆ interior (η₂ '' univ) := interior_mono hT₂
  have hopen : ∀ W ⊆ interior (η₂ '' univ), IsOpen W → IsOpen (f '' W) := by
    intro W hWV hWo
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hWo x hx
    have han : AnalyticOnNhd ℂ f (Metric.ball x r) :=
      (h4.mono (hball.trans hWV)).analyticOnNhd Metric.isOpen_ball
    rcases han.is_constant_or_isOpen (convex_ball x r).isPreconnected with ⟨w, hw⟩ | hop
    · exfalso
      have hx' : x + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball x r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg (half_pos hr).le]
        exact half_lt_self hr
      have heq : f (x + ((r / 2 : ℝ) : ℂ)) = f x := by
        rw [hw _ hx', hw _ (Metric.mem_ball_self hr)]
      have hxV : x ∈ η₂ '' univ := interior_subset (hWV (hball (Metric.mem_ball_self hr)))
      have hx'V : x + ((r / 2 : ℝ) : ℂ) ∈ η₂ '' univ := interior_subset (hWV (hball hx'))
      have hcontra := h2 hx'V hxV heq
      simp [hr.ne'] at hcontra
    · exact Filter.mem_of_superset ((hop _ subset_rfl Metric.isOpen_ball).mem_nhds
        ⟨x, Metric.mem_ball_self hr, rfl⟩) (image_mono hball)
  have h5T : f '' interior (η₂ '' T) = interior (η₁ '' T) := by
    apply Subset.antisymm
    · apply interior_maximal
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨t, ht, rfl⟩ := interior_subset hx
        exact ⟨t, ht, (h1 t (mem_univ t)).symm⟩
      · exact hopen _ hW isOpen_interior
    · intro y hy
      have hyV : y ∈ f '' interior (η₂ '' univ) := by
        rw [h5]
        exact interior_mono (image_mono (subset_univ T)) hy
      obtain ⟨x, hx, rfl⟩ := hyV
      refine ⟨x, ?_, rfl⟩
      have hWo : IsOpen (interior (η₂ '' univ) ∩ f ⁻¹' interior (η₁ '' T)) :=
        (h3.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_interior
      refine interior_maximal ?_ hWo ⟨hx, hy⟩
      rintro z ⟨hzV, hz⟩
      obtain ⟨t, ht, hft⟩ := interior_subset hz
      have hzt : z = η₂ t := h2 (interior_subset hzV) (mem_image_of_mem η₂ (mem_univ t))
        (by rw [h1 t (mem_univ t)]; exact hft.symm)
      exact ⟨t, ht, hzt.symm⟩
  refine ⟨fun t _ => h1 t (mem_univ t), h2.mono hT₂, h3.mono hT₂, h4.mono hW, h5T, ?_⟩
  intro φ ψ hφ hψ hψ0
  refine h6 φ ψ (hφ.trans hW) (fun x hx => ?_) (fun y hy => hψ0 y fun hy' => hy (image_mono hW hy'))
  by_cases hxT : x ∈ interior (η₂ '' T)
  · exact hψ x hxT
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hmem => hxT (hφ hmem)
    have hfx : f x ∉ f '' interior (η₂ '' T) := by
      rintro ⟨w, hw, hfw⟩
      have hwx : w = x := h2 (interior_subset (hW hw)) (interior_subset hx) hfw
      exact hxT (hwx ▸ hw)
    rw [hψ0 _ hfx, hφx, zero_mul]

/-- The `σ`-algebra of the curve-decorated quantum surface over `T` is contained in the one over all times. -/
theorem curveDecoratedSurfaceSigma_le_univ (γ : ℝ) (T : Set ℝ) :
    curveDecoratedSurfaceSigma γ T ≤ curveDecoratedSurfaceSigma γ univ :=
  fun _ hA => ⟨hA.1, fun p₁ p₂ hp => by
    obtain ⟨f, hf⟩ := hp
    exact hA.2 p₁ p₂ ⟨f, isCurveDecoratedReembedding_restrict hf T⟩⟩

end DMSPastFuture

open DMSPastFuture in
/-- **Independence of the past and future curve-decorated quantum surfaces at every time** (Duplantier–Miller–Sheffield,
Theorem 1.9 with the stationarity (1.9); Berestycki–Gwynne (2020), (7.35)), from the cited input
`DMSPastFutureIndependence`. A valid environment carries a mating-of-trees coupling whose cone field and curve agree
almost surely with its field and curve. -/
theorem dms21PastFutureIndependence_of_external (hDMS : DMSPastFutureIndependence) (𝒮 : SpaceFillingSLEModel) :
    DMS21PastFutureIndependence 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS H hH hHae η' hη' hηae s
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηc, η₀, hcpl, hae⟩ := hS.matingOfTrees
  have hHc : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ = H ω φ := by
    filter_upwards [hHae, hae] with ω h1 h2 φ
    exact (h2.2 φ).symm.trans (h1 φ)
  have hηc : ∀ᵐ ω ∂S.P, η' ω = ηc ω := by
    filter_upwards [hηae, hae] with ω h1 h2
    exact DFunLike.coe_injective (h1.trans h2.1.symm)
  obtain ⟨hstat, hind⟩ :=
    hDMS γ hγ hγ2 Ω S.P X X₀ hIG₀ B B' B₀ B₀' U ηL ηc η₀ S.bm hcpl H hH hHc η' hη' hηc
  have hlaw : ∀ C, MeasurableSet[curveDecoratedSurfaceSigma γ univ] C →
      S.P ((fun ω => curveTimeShift s (H ω, η' ω)) ⁻¹' C) = S.P ((fun ω => (H ω, η' ω)) ⁻¹' C) := by
    intro C hC
    rw [hstat s C hC]
    congr 1
    ext ω
    exact hC.2 _ _ (isSameCurveDecoratedSurface_recentre γ univ s (H ω, η' ω))
  have hq : Indep
      (MeasurableSpace.comap (fun ω => curveTimeShift s (H ω, η' ω)) (curveDecoratedSurfaceSigma γ (Iic 0)))
      (MeasurableSpace.comap (fun ω => curveTimeShift s (H ω, η' ω)) (curveDecoratedSurfaceSigma γ (Ici 0)))
      S.P := by
    rw [Indep_iff]
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    have hAu := curveDecoratedSurfaceSigma_le_univ γ _ A hA
    have hBu := curveDecoratedSurfaceSigma_le_univ γ _ B hB
    rw [← preimage_inter, hlaw _ (hAu.inter hBu), hlaw _ hAu, hlaw _ hBu, preimage_inter]
    exact (Indep_iff _ _ _).1 hind _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have hpast := comap_le_comap_curveTimeShift γ (T := Iic 0) (T' := Iic s) (c := s)
    (fun u => by rw [mem_Iic, mem_Iic]; constructor <;> intro h <;> linarith) (fun ω => (H ω, η' ω))
  have hfut := comap_le_comap_curveTimeShift γ (T := Ici 0) (T' := Ici s) (c := s)
    (fun u => by rw [mem_Ici, mem_Ici]; constructor <;> intro h <;> linarith) (fun ω => (H ω, η' ω))
  rw [← curveDecoratedSurfaceSigma_eq, ← curveDecoratedSurfaceSigma_eq]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hq hpast) hfut

end MatedCRT
