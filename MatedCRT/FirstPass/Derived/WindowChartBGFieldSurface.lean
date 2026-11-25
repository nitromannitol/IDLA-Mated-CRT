import MatedCRT.FirstPass.Derived.WindowChartBGIndependence
import MatedCRT.FirstPass.Derived.WindowChartFieldMeasurable
import MatedCRT.FirstPass.Derived.ValidCurveFixedTime
import MatedCRT.FirstPass.Derived.LQGDataEncode
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward

/-!
# The chart field of a window is a function of the past (or future) curve-decorated quantum surface

Berestycki–Gwynne (2020), arXiv:2003.10320, proof of Lemma 7.21 (2003.10320.txt lines 3775-3776): "By definition,
`(h^D, η^D)` (resp. `(h̃^D, η̃^D)`) is determined by the first (resp. second) quantum surface in (7.35)". This file
proves this step, `BG20WindowFieldSurfaceInput`, for the chart field `windowFieldBG` of the inverse chart
`windowChartBG` (normalized by `φ(0) = η(u)` and `φ(1) = η(a')`).

Let `f` re-embed the curve-decorated quantum surface `(η₂(T), h₂, η₂|_T)` onto `(η₁(T), h₁, η₁|_T)`
(`IsSurfaceReembedding`), with `[a, b] ⊆ T`. Then:

* `f` maps the interior of `η₂([a, b])` onto the interior of `η₁([a, b])` (open mapping theorem for the injective
  holomorphic map `f`), hence the window `U₂` (the component containing `η₂(u)`) onto the window `U₁`, its closure onto
  the closure and its frontier onto the frontier (`f` is a homeomorphism of the compact set `η₂([a, b])` onto its image);
* a window has an inverse chart iff the other one has (`IsSurfaceReembedding.exists_isInverseChart_iff`), the time `a'`
  of the two windows is the same (`IsSurfaceReembedding.windowStartBG_eq`) and, unless `η₂(a') = η₂(u)`, the inverse
  charts satisfy `ψ₁ ∘ f = ψ₂` on the closure of `U₂` (`IsSurfaceReembedding.windowChartBG_comp`): two conformal maps of
  the disc onto `U₁` centred at `η₁(u)` differ by a rotation (Schwarz lemma), which the normalization at `η(a')` fixes;
* the chart fields agree (`IsSurfaceReembedding.windowFieldBG_eq`): with `φ₁ = f ∘ φ₂`, the coordinate change
  `h₂ = h₁ ∘ f + Q log |f'|` applied to the transported test function `(ρ ∘ ψ₂) |ψ₂'|²`, the change of variables
  `x = φ₂(w)` (Jacobian `|φ₂'|²`, `integral_mul_chartTestFun`) and `log |φ₁'| = log |f' ∘ φ₂| + log |φ₂'|`.

The chart field set to `0` on the event `η(a') = η(u)` (`windowFieldSurfaceBG`) is therefore a Borel function of
(field, curve) which is invariant under re-embedding, i.e. measurable for `curveSurfaceSigma γ T`
(`measurable_curveSurfaceSigma_windowFieldSurfaceBG`). In a valid environment the event `η(a') = η(u)` is null, since
`a' < u` and the curve visits `η(u)` only at the time `u` almost surely (`MatedCRTEnv.IsValid.ae_fixedTime_singleton_fibre`),
which gives `bg20WindowFieldSurfaceInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-! ### Window geometry and the time `a'` -/

theorem windowDomain_subset_interior (η : C(ℝ, ℂ)) (a u b : ℝ) :
    windowDomain η a u b ⊆ interior (η '' Icc a b) := by
  unfold windowDomain
  exact connectedComponentIn_subset _ _

theorem closure_windowDomain_subset_image (η : C(ℝ, ℂ)) (a u b : ℝ) :
    closure (windowDomain η a u b) ⊆ η '' Icc a b :=
  closure_minimal (windowDomain_subset_image η a u b) (isCompact_Icc.image η.continuous).isClosed

/-- The time `a'` lies in `[a, u]` and the curve at `a'` lies in the closure of the window. -/
theorem windowStartBG_mem {a u b : ℝ} (hau : a ≤ u) {η : C(ℝ, ℂ)}
    (h : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) :
    windowStartBG a u b η ∈ Icc a u ∧ η (windowStartBG a u b η) ∈ closure (windowDomain η a u b) := by
  rw [windowStartBG, ite_eq_left h]
  obtain ⟨ψ, hψ⟩ := h
  set S := {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)}
  have huS : u ∈ S := ⟨⟨hau, le_rfl⟩, fun t ht => by
    rw [le_antisymm ht.2 ht.1]
    exact subset_closure hψ.mem⟩
  have hbdd : BddBelow S := ⟨a, fun s hs => hs.1.1⟩
  have hα : sInf S ∈ Icc a u := ⟨le_csInf ⟨u, huS⟩ fun s hs => hs.1.1, csInf_le hbdd huS⟩
  refine ⟨hα, ?_⟩
  rcases hα.2.eq_or_lt with heq | hlt
  · rw [heq]
    exact subset_closure hψ.mem
  · have hIoc : ∀ t ∈ Ioc (sInf S) u, η t ∈ closure (windowDomain η a u b) := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt ⟨u, huS⟩ ht.1
      exact hs.2 t ⟨hst.le, ht.2⟩
    have hcl : sInf S ∈ closure (Ioc (sInf S) u) := by
      rw [closure_Ioc hlt.ne]
      exact ⟨le_rfl, hlt.le⟩
    refine closure_minimal ?_ isClosed_closure
      (image_closure_subset_closure_image η.continuous (mem_image_of_mem η hcl))
    rintro _ ⟨t, ht, rfl⟩
    exact hIoc t ht

theorem windowStartBG_mem_Icc {a u b : ℝ} (hau : a ≤ u) (η : C(ℝ, ℂ)) : windowStartBG a u b η ∈ Icc a u := by
  by_cases h : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ
  · exact (windowStartBG_mem hau h).1
  · rw [windowStartBG, ite_eq_right h]
    exact ⟨le_rfl, hau⟩

/-- **`a' < u`.** If the window has an inverse chart, the curve stays in the window on a time interval ending at `u`. -/
theorem windowStartBG_lt {a u b : ℝ} (hau : a < u) (η : C(ℝ, ℂ)) : windowStartBG a u b η < u := by
  by_cases h : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ
  · rw [windowStartBG, ite_eq_left h]
    obtain ⟨ψ, hψ⟩ := h
    have hev : ∀ᶠ t in 𝓝 u, η t ∈ windowDomain η a u b :=
      η.continuous.continuousAt.preimage_mem_nhds ((isOpen_windowDomain η a u b).mem_nhds hψ.mem)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hmem : max a (u - δ / 2) ∈
        {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)} := by
      refine ⟨⟨le_max_left _ _, max_le hau.le (by linarith)⟩, fun t ht => subset_closure (hball ?_)⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2, le_max_right a (u - δ / 2)]
    exact (csInf_le ⟨a, fun s hs => hs.1.1⟩ hmem).trans_lt (max_lt hau (by linarith))
  · rw [windowStartBG, ite_eq_right h]
    exact hau

/-- The normalized inverse chart of Berestycki–Gwynne is an inverse chart whenever the window has one. -/
theorem isInverseChart_windowChartBG {a u b : ℝ} {η : C(ℝ, ℂ)}
    (h : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) :
    IsInverseChart (windowDomain η a u b) (η u) (windowChartBG a u b η) := by
  obtain ⟨ψ, hψ⟩ := h
  exact (isInverseChart_windowChart hψ).of_apply_eq_mul (norm_windowRotBG a u b η) (windowChartBG_apply a u b η)

/-! ### Chart fields -/

theorem chartFieldPairing_eq_of_isInverseChart {γ : ℝ} {h : LQGMetric.DistC} {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (hc : IsInverseChart U z ψ ∧ IsOpen U ∧ Bornology.IsBounded U) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    chartFieldPairing γ h U z ψ ρ = h (chartTest hc.1 hc.2.1 hc.2.2 ρ) +
      MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (chartMap U ψ) w‖ * ρ w := by
  rw [chartFieldPairing, dite_eq_left hc]

theorem windowFieldBG_eq_zero_of_not {γ a u b : ℝ} {p : LQGMetric.DistC × C(ℝ, ℂ)}
    (hn : ¬∃ ψ, IsInverseChart (windowDomain p.2 a u b) (p.2 u) ψ) : windowFieldBG γ a u b p = 0 := by
  funext ρ
  show chartFieldPairing γ p.1 (windowDomain p.2 a u b) (p.2 u) (windowChartBG a u b p.2) ρ = 0
  rw [chartFieldPairing, dite_eq_right fun hc => hn ⟨_, hc.1⟩]

theorem testFunction_eq_zero_of_notMem_ball (ρ : 𝓓(unitDiscOpens, ℝ)) {w : ℂ} (hw : w ∉ ball (0 : ℂ) 1) :
    ρ w = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hw (ρ.tsupport_subset h)

/-- `log |g| ρ` is integrable for `g` continuous and non-vanishing on the disc and `ρ` a test function on the disc. -/
theorem integrable_log_norm_mul_test {g : ℂ → ℂ} (hg : ContinuousOn g (ball 0 1))
    (hg0 : ∀ w ∈ ball (0 : ℂ) 1, g w ≠ 0) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    Integrable fun w => Real.log ‖g w‖ * ρ w := by
  have hK : IsCompact (tsupport ρ) := ρ.hasCompactSupport
  have hKD : tsupport ρ ⊆ ball (0 : ℂ) 1 := ρ.tsupport_subset
  have hc : ContinuousOn (fun w => Real.log ‖g w‖ * ρ w) (tsupport ρ) :=
    (((hg.mono hKD).norm).log fun w hw => norm_ne_zero_iff.2 (hg0 w (hKD hw))).mul
      ρ.contDiff.continuous.continuousOn
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 (hc.integrableOn_compact hK)
  exact (Function.support_mul_subset_right _ _).trans (subset_tsupport _)

/-- **Change of variables in the chart pairing.** For a conformal map `φ` of the disc onto `U` and `ψ` inverting it on
the disc and holomorphic on `U`, `∫ g(x) (ρ ∘ ψ)(x) |ψ'(x)|² 1_U(x) dx = ∫ g(φ(w)) ρ(w) dw`. -/
theorem integral_mul_chartTestFun {U : Set ℂ} {φ : ℂ → ℂ} (hφ : IsDiscMap U φ) {ψ : C(ℂ, ℂ)}
    (hψφ : ∀ w ∈ ball (0 : ℂ) 1, ψ (φ w) = w) (hψd : DifferentiableOn ℂ ψ U) (g : ℂ → ℝ)
    (ρ : 𝓓(unitDiscOpens, ℝ)) :
    ∫ x, g x * chartTestFun U ψ ρ x = ∫ w, g (φ w) * ρ w := by
  have hU : IsOpen U := hφ.isOpen
  have hinj : InjOn φ (ball 0 1) := hφ.injOn.mono ball_subset_closedBall
  have hderiv : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt φ (fderiv ℝ φ w) (ball 0 1) w := fun w hw =>
    ((hφ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have h1 : ∫ x, g x * chartTestFun U ψ ρ x =
      ∫ x in φ '' ball 0 1, g x * (ρ (ψ x) * ‖deriv ψ x‖ ^ 2) := by
    rw [hφ.image_ball, ← integral_indicator hU.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    unfold chartTestFun
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  have h2 : ∫ w, g (φ w) * ρ w = ∫ w in ball (0 : ℂ) 1, g (φ w) * ρ w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by
      rw [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero]).symm
  rw [h1, integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) isOpen_ball.measurableSet hderiv hinj, h2]
  refine setIntegral_congr_fun isOpen_ball.measurableSet fun w hw => ?_
  have hφd : DifferentiableAt ℂ φ w := hφ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
  have hφU : φ w ∈ U := hφ.image_ball ▸ mem_image_of_mem φ hw
  have hψd' : DifferentiableAt ℂ ψ (φ w) := hψd.differentiableAt (hU.mem_nhds hφU)
  have hchain : deriv ψ (φ w) * deriv φ w = 1 := by
    rw [← deriv_comp w hψd' hφd]
    have hev : (⇑ψ ∘ φ) =ᶠ[𝓝 w] id := by
      filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
      exact hψφ w' hw'
    rw [hev.deriv_eq, deriv_id]
  have hn : ‖deriv ψ (φ w)‖ ^ 2 * ‖deriv φ w‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, hchain, norm_one, one_pow]
  simp only [smul_eq_mul]
  rw [QuantumZipper.abs_det_fderiv_eq_normSq hφd, hψφ w hw]
  calc ‖deriv φ w‖ ^ 2 * (g (φ w) * (ρ w * ‖deriv ψ (φ w)‖ ^ 2))
      = g (φ w) * ρ w * (‖deriv ψ (φ w)‖ ^ 2 * ‖deriv φ w‖ ^ 2) := by ring
    _ = g (φ w) * ρ w := by rw [hn, mul_one]

/-- A conformal map of the disc onto `U` followed by a map injective and continuous near the closure of `U`,
holomorphic on `U`, and mapping `U` and its frontier onto `V` and its frontier, is a conformal map onto `V`. -/
theorem IsDiscMap.comp_of_injOn {U V : Set ℂ} {φ f : ℂ → ℂ} (hφ : IsDiscMap U φ) {S : Set ℂ}
    (hS : closure U ⊆ S) (hinj : InjOn f S) (hcont : ContinuousOn f S) (hdiff : DifferentiableOn ℂ f U)
    (hU : f '' U = V) (hfr : f '' frontier U = frontier V) : IsDiscMap V (f ∘ φ) := by
  have hmaps : MapsTo φ (closedBall 0 1) S := fun w hw =>
    hS (hφ.image_closedBall ▸ mem_image_of_mem φ hw)
  have hmapsb : MapsTo φ (ball 0 1) U := fun w hw => hφ.image_ball ▸ mem_image_of_mem φ hw
  refine ⟨hcont.comp hφ.continuousOn hmaps, hinj.comp hφ.injOn hmaps,
    hdiff.comp hφ.differentiableOn hmapsb, ?_, ?_⟩
  · rw [image_comp, hφ.image_ball, hU]
  · rw [image_comp, hφ.image_sphere, hfr]

/-- The pairs (field, curve) whose curve does not visit `η(u)` at the time `a'` of the window `(a, u, b)`. -/
def windowFieldGoodSetBG (a u b : ℝ) : Set (LQGMetric.DistC × C(ℝ, ℂ)) :=
  {p | p.2 (windowStartBG a u b p.2) ≠ p.2 u}

/-- **The chart field of the window as a function of the curve-decorated quantum surface**: the chart field
`windowFieldBG` on `windowFieldGoodSetBG`, and `0` off it. -/
noncomputable def windowFieldSurfaceBG (γ a u b : ℝ) : LQGMetric.DistC × C(ℝ, ℂ) → 𝓓(unitDiscOpens, ℝ) → ℝ :=
  (windowFieldGoodSetBG a u b).indicator (windowFieldBG γ a u b)

/-! ### Re-embeddings of curve-decorated quantum surfaces and windows -/

section Reembedding

variable {γ : ℝ} {T : Set ℝ} {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ} {a u b : ℝ}

/-- A re-embedding maps the interior of `η₂(J)` onto the interior of `η₁(J)` for every `J ⊆ T` (open mapping theorem
for the injective holomorphic map `f`). -/
theorem IsSurfaceReembedding.image_interior_image {J : Set ℝ} (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : J ⊆ T) : f '' interior (η₂ '' J) = interior (η₁ '' J) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hf
  have hJT : interior (η₂ '' J) ⊆ interior (η₂ '' T) := interior_mono (image_mono hJ)
  apply Subset.antisymm
  · apply interior_maximal
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := interior_subset hx
      exact ⟨t, ht, (h1 t (hJ ht)).symm⟩
    · exact QuantumZipper.CA.isOpen_image_of_injOn isOpen_interior h4 (h2.mono interior_subset) isOpen_interior
        hJT
  · intro y hy
    have hyV : y ∈ f '' interior (η₂ '' T) := by
      rw [h5]
      exact interior_mono (image_mono hJ) hy
    obtain ⟨x, hx, rfl⟩ := hyV
    refine ⟨x, ?_, rfl⟩
    have hWo : IsOpen (interior (η₂ '' T) ∩ f ⁻¹' interior (η₁ '' J)) :=
      (h3.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_interior
    refine interior_maximal ?_ hWo ⟨hx, hy⟩
    rintro z ⟨hzV, hz⟩
    obtain ⟨t, ht, hft⟩ := interior_subset hz
    have hzt : z = η₂ t := h2 (interior_subset hzV) (mem_image_of_mem η₂ (hJ ht))
      (by rw [h1 t (hJ ht)]; exact hft.symm)
    exact ⟨t, ht, hzt.symm⟩

/-- A re-embedding maps the window of `η₂` onto the window of `η₁`. -/
theorem IsSurfaceReembedding.image_windowDomain (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) : f '' windowDomain η₂ a u b = windowDomain η₁ a u b := by
  have hI := hf.image_interior_image hJ
  obtain ⟨h1, h2, -, h4, -⟩ := hf
  have hIT : interior (η₂ '' Icc a b) ⊆ η₂ '' T := interior_subset.trans (image_mono hJ)
  have hdI : DifferentiableOn ℂ f (interior (η₂ '' Icc a b)) := h4.mono (interior_mono (image_mono hJ))
  have hiI : InjOn f (interior (η₂ '' Icc a b)) := h2.mono hIT
  obtain ⟨e, hes, het, hef⟩ : ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source = interior (η₂ '' Icc a b) ∧
      e.target = interior (η₁ '' Icc a b) ∧ ∀ x, e x = f x :=
    ⟨QuantumZipper.CA.univalentOPH isOpen_interior hdI hiI, rfl, by
      rw [QuantumZipper.CA.univalentOPH_target, hI], fun _ => rfl⟩
  have hz : f (η₂ u) = η₁ u := h1 u (hJ hu)
  unfold windowDomain
  by_cases hz₂ : η₂ u ∈ interior (η₂ '' Icc a b)
  · have hz₁ : η₁ u ∈ interior (η₁ '' Icc a b) := by
      rw [← hI, ← hz]
      exact mem_image_of_mem f hz₂
    apply Subset.antisymm
    · rw [← hz]
      refine (isPreconnected_connectedComponentIn.image f
        (hdI.continuousOn.mono (connectedComponentIn_subset _ _))).subset_connectedComponentIn
        (mem_image_of_mem f (mem_connectedComponentIn hz₂)) ?_
      rw [← hI]
      exact image_mono (connectedComponentIn_subset _ _)
    · have hsub : e.symm '' connectedComponentIn (interior (η₁ '' Icc a b)) (η₁ u) ⊆
          connectedComponentIn (interior (η₂ '' Icc a b)) (η₂ u) := by
        refine (isPreconnected_connectedComponentIn.image e.symm
          (e.continuousOn_symm.mono ?_)).subset_connectedComponentIn ?_ ?_
        · rw [het]
          exact connectedComponentIn_subset _ _
        · refine ⟨η₁ u, mem_connectedComponentIn hz₁, ?_⟩
          have h := e.left_inv (show η₂ u ∈ e.source by rw [hes]; exact hz₂)
          rwa [hef, hz] at h
        · rintro _ ⟨y', hy', rfl⟩
          rw [← hes]
          exact e.map_target (by rw [het]; exact connectedComponentIn_subset _ _ hy')
      intro y hy
      refine ⟨e.symm y, hsub ⟨y, hy, rfl⟩, ?_⟩
      rw [← hef]
      exact e.right_inv (by rw [het]; exact connectedComponentIn_subset _ _ hy)
  · have hz₁ : η₁ u ∉ interior (η₁ '' Icc a b) := by
      rw [← hI, ← hz]
      rintro ⟨x, hx, hfx⟩
      obtain rfl : x = η₂ u := h2 (hIT hx) (mem_image_of_mem η₂ (hJ hu)) hfx
      exact hz₂ hx
    rw [connectedComponentIn_eq_empty hz₂, connectedComponentIn_eq_empty hz₁, image_empty]

/-- A re-embedding maps the closure of the window of `η₂` onto the closure of the window of `η₁`. -/
theorem IsSurfaceReembedding.image_closure_windowDomain (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) :
    f '' closure (windowDomain η₂ a u b) = closure (windowDomain η₁ a u b) := by
  have hW := hf.image_windowDomain hJ hu
  obtain ⟨-, -, h3, -⟩ := hf
  have hcl := closure_windowDomain_subset_image η₂ a u b
  have hc : ContinuousOn f (closure (windowDomain η₂ a u b)) := h3.mono (hcl.trans (image_mono hJ))
  apply Subset.antisymm
  · rw [← hW]
    exact hc.image_closure
  · refine closure_minimal ?_ ?_
    · rw [← hW]
      exact image_mono subset_closure
    · exact (((isCompact_Icc.image η₂.continuous).of_isClosed_subset isClosed_closure hcl).image_of_continuousOn
        hc).isClosed

/-- A re-embedding maps the frontier of the window of `η₂` onto the frontier of the window of `η₁`. -/
theorem IsSurfaceReembedding.image_frontier_windowDomain (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) :
    f '' frontier (windowDomain η₂ a u b) = frontier (windowDomain η₁ a u b) := by
  have hW := hf.image_windowDomain hJ hu
  have hC := hf.image_closure_windowDomain hJ hu
  obtain ⟨-, h2, -⟩ := hf
  have hcl : closure (windowDomain η₂ a u b) ⊆ η₂ '' T :=
    (closure_windowDomain_subset_image η₂ a u b).trans (image_mono hJ)
  rw [(isOpen_windowDomain η₂ a u b).frontier_eq, (isOpen_windowDomain η₁ a u b).frontier_eq, ← hC, ← hW]
  ext y
  constructor
  · rintro ⟨x, ⟨hxc, hxU⟩, rfl⟩
    refine ⟨mem_image_of_mem f hxc, ?_⟩
    rintro ⟨x', hx', hfx⟩
    obtain rfl : x' = x := h2 (hcl (subset_closure hx')) (hcl hxc) hfx
    exact hxU hx'
  · rintro ⟨⟨x, hxc, rfl⟩, hxU⟩
    exact ⟨x, ⟨hxc, fun hx => hxU (mem_image_of_mem f hx)⟩, rfl⟩

/-- **Inverse charts under re-embedding.** The window of `η₁` has an inverse chart iff the window of `η₂` has one: an
inverse chart `ψ₁` pulls back to `ψ₁ ∘ f` (extended continuously off the closure of the window, Tietze), and a
conformal map `φ₂` of the disc onto the window of `η₂` pushes forward to `f ∘ φ₂`. -/
theorem IsSurfaceReembedding.exists_isInverseChart_iff (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) :
    (∃ ψ, IsInverseChart (windowDomain η₁ a u b) (η₁ u) ψ) ↔
      ∃ ψ, IsInverseChart (windowDomain η₂ a u b) (η₂ u) ψ := by
  have hW := hf.image_windowDomain hJ hu
  have hC := hf.image_closure_windowDomain hJ hu
  have hF := hf.image_frontier_windowDomain hJ hu
  obtain ⟨h1, h2, h3, h4, -⟩ := hf
  have hcl : closure (windowDomain η₂ a u b) ⊆ η₂ '' T :=
    (closure_windowDomain_subset_image η₂ a u b).trans (image_mono hJ)
  have hUint : windowDomain η₂ a u b ⊆ interior (η₂ '' T) :=
    (windowDomain_subset_interior η₂ a u b).trans (interior_mono (image_mono hJ))
  have hz : f (η₂ u) = η₁ u := h1 u (hJ hu)
  constructor
  · rintro ⟨ψ₁, hψ₁⟩
    have hc : ContinuousOn (fun x => ψ₁ (f x)) (closure (windowDomain η₂ a u b)) :=
      ψ₁.continuous.comp_continuousOn (h3.mono hcl)
    obtain ⟨ψ, hψ⟩ := ContinuousMap.exists_restrict_eq isClosed_closure
      (⟨fun x : closure (windowDomain η₂ a u b) => ψ₁ (f x), hc.domRestrict⟩ :
        C(closure (windowDomain η₂ a u b), ℂ))
    have hψx : ∀ x ∈ closure (windowDomain η₂ a u b), ψ x = ψ₁ (f x) := fun x hx =>
      DFunLike.congr_fun hψ ⟨x, hx⟩
    have hmem : η₂ u ∈ windowDomain η₂ a u b := by
      have h := hψ₁.mem
      rw [← hW] at h
      obtain ⟨x, hx, hfx⟩ := h
      obtain rfl : x = η₂ u :=
        h2 (hcl (subset_closure hx)) (mem_image_of_mem η₂ (hJ hu)) (hfx.trans hz.symm)
      exact hx
    refine ⟨ψ, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hψx _ (subset_closure hmem), hz, hψ₁.apply_point]
    · intro x hx y hy hxy
      rw [hψx x hx, hψx y hy] at hxy
      have hfx : f x ∈ closure (windowDomain η₁ a u b) := hC ▸ mem_image_of_mem f hx
      have hfy : f y ∈ closure (windowDomain η₁ a u b) := hC ▸ mem_image_of_mem f hy
      exact h2 (hcl hx) (hcl hy) (hψ₁.injOn hfx hfy hxy)
    · refine (hψ₁.differentiableOn.comp (h4.mono hUint) fun x hx => ?_).congr fun x hx =>
        hψx x (subset_closure hx)
      exact hW ▸ mem_image_of_mem f hx
    · calc ψ '' windowDomain η₂ a u b = ψ₁ '' (f '' windowDomain η₂ a u b) := by
            rw [image_image]
            exact image_congr fun x hx => hψx x (subset_closure hx)
        _ = ball 0 1 := by rw [hW, hψ₁.image_eq]
    · calc ψ '' frontier (windowDomain η₂ a u b) = ψ₁ '' (f '' frontier (windowDomain η₂ a u b)) := by
            rw [image_image]
            exact image_congr fun x hx => hψx x (frontier_subset_closure hx)
        _ = sphere 0 1 := by rw [hF, hψ₁.image_frontier]
  · rintro ⟨ψ₂, hψ₂⟩
    obtain ⟨φ, hφ, hφ0, -⟩ :=
      hψ₂.exists_isDiscMap (isOpen_windowDomain η₂ a u b) (isBounded_windowDomain η₂ a u b)
    obtain ⟨ψ, hψ, -⟩ := (hφ.comp_of_injOn hcl h2 h3 (h4.mono hUint) hW hF).exists_isInverseChart
    refine ⟨ψ, ?_⟩
    rwa [Function.comp_apply, hφ0, hz] at hψ

/-- **The time `a'` is invariant under re-embedding.** -/
theorem IsSurfaceReembedding.windowStartBG_eq (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hau : a < u) (hub : u < b) :
    windowStartBG a u b η₁ = windowStartBG a u b η₂ := by
  have hu : u ∈ Icc a b := ⟨hau.le, hub.le⟩
  have hiff := hf.exists_isInverseChart_iff hJ hu
  have hC := hf.image_closure_windowDomain hJ hu
  obtain ⟨h1, h2, -⟩ := hf
  have hcl : closure (windowDomain η₂ a u b) ⊆ η₂ '' T :=
    (closure_windowDomain_subset_image η₂ a u b).trans (image_mono hJ)
  by_cases h₂ : ∃ ψ, IsInverseChart (windowDomain η₂ a u b) (η₂ u) ψ
  · rw [windowStartBG, windowStartBG, ite_eq_left (hiff.2 h₂), ite_eq_left h₂]
    congr 1
    ext s
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hs => forall₂_congr fun t ht => ?_
    have htT : t ∈ T := hJ ⟨hs.1.trans ht.1, ht.2.trans hub.le⟩
    rw [← h1 t htT, ← hC]
    exact h2.mem_image_iff hcl (mem_image_of_mem η₂ htT)
  · rw [windowStartBG, windowStartBG, ite_eq_right (mt hiff.1 h₂), ite_eq_right h₂]

/-- The normalized inverse charts (`φ'(0) > 0`) of the two windows differ by a rotation after `f`. -/
theorem IsSurfaceReembedding.exists_windowChart_comp (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) (h₂ : ∃ ψ, IsInverseChart (windowDomain η₂ a u b) (η₂ u) ψ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x ∈ closure (windowDomain η₂ a u b),
      windowChart a u b η₁ (f x) = c * windowChart a u b η₂ x := by
  have hW := hf.image_windowDomain hJ hu
  have hF := hf.image_frontier_windowDomain hJ hu
  obtain ⟨ψ₁, hψ₁⟩ := (hf.exists_isInverseChart_iff hJ hu).2 h₂
  obtain ⟨ψ₂, hψ₂⟩ := h₂
  obtain ⟨h1, h2, h3, h4, -⟩ := hf
  have hcl : closure (windowDomain η₂ a u b) ⊆ η₂ '' T :=
    (closure_windowDomain_subset_image η₂ a u b).trans (image_mono hJ)
  have hUint : windowDomain η₂ a u b ⊆ interior (η₂ '' T) :=
    (windowDomain_subset_interior η₂ a u b).trans (interior_mono (image_mono hJ))
  have hN₂ := isNormalizedDiscMap_windowDiscMap hψ₂
  have hN₁ := isNormalizedDiscMap_windowDiscMap hψ₁
  set φ₂ := windowDiscMap a u b η₂
  set φ₁ := windowDiscMap a u b η₁
  have hD : IsDiscMap (windowDomain η₁ a u b) (f ∘ ⇑φ₂) :=
    hN₂.isDiscMap.comp_of_injOn hcl h2 h3 (h4.mono hUint) hW hF
  obtain ⟨c, hc, hDc, hre, him⟩ := hD.exists_normalized
  have hNc : IsNormalizedDiscMap (windowDomain η₁ a u b) (η₁ u) (fun w => (f ∘ ⇑φ₂) (c * w)) := by
    refine ⟨hDc, ?_, hre, him⟩
    show f (φ₂ (c * 0)) = η₁ u
    rw [mul_zero, hN₂.apply_zero]
    exact h1 u (hJ hu)
  have heq := hN₁.eqOn hNc
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun x hx => ?_⟩
  have hx' : x ∈ ⇑φ₂ '' closedBall 0 1 := by
    rw [hN₂.isDiscMap.image_closedBall]
    exact hx
  obtain ⟨v, hv, rfl⟩ := hx'
  have hv' : c⁻¹ * v ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, norm_inv, hc, inv_one, one_mul]
    exact mem_closedBall_zero_iff.1 hv
  have hfx : f (φ₂ v) = φ₁ (c⁻¹ * v) := by
    rw [heq hv']
    show f (φ₂ v) = f (φ₂ (c * (c⁻¹ * v)))
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [hfx]
  show discInverseExt φ₁ (φ₁ (c⁻¹ * v)) = c⁻¹ * discInverseExt φ₂ (φ₂ v)
  rw [discInverseExt_apply_image hN₁.isDiscMap.injOn hv', discInverseExt_apply_image hN₂.isDiscMap.injOn hv]

/-- **The inverse charts of Berestycki–Gwynne are transported by a re-embedding**: `ψ₁ ∘ f = ψ₂` on the closure of the
window of `η₂`, unless the curve visits `η₂(u)` at the time `a'`. -/
theorem IsSurfaceReembedding.windowChartBG_comp (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hau : a < u) (hub : u < b)
    (h₂ : ∃ ψ, IsInverseChart (windowDomain η₂ a u b) (η₂ u) ψ)
    (hne : η₂ (windowStartBG a u b η₂) ≠ η₂ u) {x : ℂ} (hx : x ∈ closure (windowDomain η₂ a u b)) :
    windowChartBG a u b η₁ (f x) = windowChartBG a u b η₂ x := by
  have hu : u ∈ Icc a b := ⟨hau.le, hub.le⟩
  obtain ⟨c, hc, hcx⟩ := hf.exists_windowChart_comp hJ hu h₂
  have hα := hf.windowStartBG_eq hJ hau hub
  obtain ⟨hαI, hαcl⟩ := windowStartBG_mem hau.le h₂
  obtain ⟨h1, -⟩ := hf
  have hαT : windowStartBG a u b η₂ ∈ T := hJ ⟨hαI.1, hαI.2.trans hub.le⟩
  obtain ⟨ψ₂, hψ₂⟩ := h₂
  have hC := isInverseChart_windowChart hψ₂
  have hw : windowChart a u b η₂ (η₂ (windowStartBG a u b η₂)) ≠ 0 := fun h0 =>
    hne (hC.injOn hαcl (subset_closure hC.mem) (h0.trans hC.apply_point.symm))
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hcw : c * windowChart a u b η₂ (η₂ (windowStartBG a u b η₂)) ≠ 0 := mul_ne_zero hc0 hw
  have key : ∀ r W Y : ℂ, r * (c * W)⁻¹ * (c * Y) = r * W⁻¹ * Y := fun r W Y => by
    rw [mul_inv_rev]
    calc r * (W⁻¹ * c⁻¹) * (c * Y) = r * W⁻¹ * Y * (c * c⁻¹) := by ring
      _ = r * W⁻¹ * Y := by rw [mul_inv_cancel₀ hc0, mul_one]
  rw [windowChartBG_apply, windowChartBG_apply, windowRotBG, windowRotBG, hα, ← h1 _ hαT, hcx _ hαcl, hcx x hx]
  unfold unitRotation
  rw [ite_eq_right hcw, ite_eq_right hw, norm_mul, hc, one_mul]
  exact key _ _ _

/-- **The chart field is invariant under re-embedding** (Berestycki–Gwynne (2020), (2.1) and (7.34)), unless the curve
visits `η₂(u)` at the time `a'`. -/
theorem IsSurfaceReembedding.windowFieldBG_eq (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hau : a < u) (hub : u < b) (hne : η₂ (windowStartBG a u b η₂) ≠ η₂ u) :
    windowFieldBG γ a u b (h₂, η₂) = windowFieldBG γ a u b (h₁, η₁) := by
  have hu : u ∈ Icc a b := ⟨hau.le, hub.le⟩
  have hiff := hf.exists_isInverseChart_iff hJ hu
  by_cases hch : ∃ ψ, IsInverseChart (windowDomain η₂ a u b) (η₂ u) ψ
  swap
  · rw [windowFieldBG_eq_zero_of_not (p := (h₂, η₂)) hch,
      windowFieldBG_eq_zero_of_not (p := (h₁, η₁)) (mt hiff.1 hch)]
  have hψ₂ := isInverseChart_windowChartBG hch
  have hψ₁ := isInverseChart_windowChartBG (hiff.2 hch)
  have hW := hf.image_windowDomain hJ hu
  have hF := hf.image_frontier_windowDomain hJ hu
  have hcomp : ∀ x ∈ closure (windowDomain η₂ a u b), windowChartBG a u b η₁ (f x) = windowChartBG a u b η₂ x :=
    fun x hx => hf.windowChartBG_comp hJ hau hub hch hne hx
  obtain ⟨-, h2, h3, h4, -, h6⟩ := hf
  have hcl : closure (windowDomain η₂ a u b) ⊆ η₂ '' T :=
    (closure_windowDomain_subset_image η₂ a u b).trans (image_mono hJ)
  have hUint : windowDomain η₂ a u b ⊆ interior (η₂ '' T) :=
    (windowDomain_subset_interior η₂ a u b).trans (interior_mono (image_mono hJ))
  have hinjI : InjOn f (interior (η₂ '' T)) := h2.mono interior_subset
  -- a conformal map `φ₂` of the disc onto the window of `η₂` inverted by `ψ₂`, and `φ₁ = f ∘ φ₂`
  obtain ⟨φ₂, hφ₂, -, hφψ₂⟩ :=
    hψ₂.exists_isDiscMap (isOpen_windowDomain η₂ a u b) (isBounded_windowDomain η₂ a u b)
  have hφU : ∀ w ∈ ball (0 : ℂ) 1, φ₂ w ∈ windowDomain η₂ a u b := fun w hw =>
    hφ₂.image_ball ▸ mem_image_of_mem φ₂ hw
  have hψφ₂ : ∀ v ∈ closedBall (0 : ℂ) 1, windowChartBG a u b η₂ (φ₂ v) = v := fun v hv => by
    have hv' : φ₂ v ∈ closure (windowDomain η₂ a u b) := hφ₂.image_closedBall ▸ mem_image_of_mem φ₂ hv
    have hmem : windowChartBG a u b η₂ (φ₂ v) ∈ closedBall (0 : ℂ) 1 := by
      rw [closure_eq_self_union_frontier] at hv'
      rcases hv' with h | h
      · exact ball_subset_closedBall (hψ₂.image_eq ▸ mem_image_of_mem _ h)
      · exact sphere_subset_closedBall (hψ₂.image_frontier ▸ mem_image_of_mem _ h)
    exact hφ₂.injOn hmem hv (hφψ₂ _ hv')
  have hφ₁ : IsDiscMap (windowDomain η₁ a u b) (f ∘ ⇑φ₂) := hφ₂.comp_of_injOn hcl h2 h3 (h4.mono hUint) hW hF
  have hψφ₁ : ∀ v ∈ closedBall (0 : ℂ) 1, windowChartBG a u b η₁ ((f ∘ ⇑φ₂) v) = v := fun v hv => by
    rw [Function.comp_apply, hcomp _ (hφ₂.image_closedBall ▸ mem_image_of_mem φ₂ hv), hψφ₂ v hv]
  have hf'0 : ∀ w ∈ ball (0 : ℂ) 1, deriv f (φ₂ w) ≠ 0 := fun w hw =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_interior h4 hinjI (hUint (hφU w hw))
  have hc₂ : IsInverseChart (windowDomain η₂ a u b) (η₂ u) (windowChartBG a u b η₂) ∧
      IsOpen (windowDomain η₂ a u b) ∧ Bornology.IsBounded (windowDomain η₂ a u b) :=
    ⟨hψ₂, isOpen_windowDomain η₂ a u b, isBounded_windowDomain η₂ a u b⟩
  have hc₁ : IsInverseChart (windowDomain η₁ a u b) (η₁ u) (windowChartBG a u b η₁) ∧
      IsOpen (windowDomain η₁ a u b) ∧ Bornology.IsBounded (windowDomain η₁ a u b) :=
    ⟨hψ₁, isOpen_windowDomain η₁ a u b, isBounded_windowDomain η₁ a u b⟩
  funext ρ
  show chartFieldPairing γ h₂ (windowDomain η₂ a u b) (η₂ u) (windowChartBG a u b η₂) ρ =
    chartFieldPairing γ h₁ (windowDomain η₁ a u b) (η₁ u) (windowChartBG a u b η₁) ρ
  -- the coordinate change `h₂ = h₁ ∘ f + Q log |f'|` on the transported test function
  have hKs := isCompact_closure_inter_preimage hψ₂ (isOpen_windowDomain η₂ a u b)
    (isBounded_windowDomain η₂ a u b) ρ.hasCompactSupport ρ.tsupport_subset
  have hsupp : tsupport (chartTest hc₂.1 hc₂.2.1 hc₂.2.2 ρ : ℂ → ℝ) ⊆ interior (η₂ '' T) := by
    unfold tsupport
    refine (closure_minimal (fun x hx => ?_) hKs.1.isClosed).trans (hKs.2.trans hUint)
    by_contra hxK
    exact hx (chartTestFun_eq_zero_of_notMem _ hxK)
  have hcoord : ∀ x ∈ interior (η₂ '' T),
      (chartTest hc₁.1 hc₁.2.1 hc₁.2.2 ρ) (f x) * ‖deriv f x‖ ^ 2 = (chartTest hc₂.1 hc₂.2.1 hc₂.2.2 ρ) x := by
    intro x hx
    rw [chartTest_apply, chartTest_apply]
    unfold chartTestFun
    by_cases hxU : x ∈ windowDomain η₂ a u b
    · have hfx : f x ∈ windowDomain η₁ a u b := hW ▸ mem_image_of_mem f hxU
      simp only [indicator_of_mem hfx, indicator_of_mem hxU]
      rw [hcomp x (subset_closure hxU)]
      have hfd : DifferentiableAt ℂ f x := h4.differentiableAt (isOpen_interior.mem_nhds hx)
      have hψ₁d : DifferentiableAt ℂ (windowChartBG a u b η₁) (f x) :=
        hψ₁.differentiableOn.differentiableAt ((isOpen_windowDomain η₁ a u b).mem_nhds hfx)
      have hd : deriv (windowChartBG a u b η₂) x = deriv (windowChartBG a u b η₁) (f x) * deriv f x := by
        rw [← deriv_comp x hψ₁d hfd]
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [(isOpen_windowDomain η₂ a u b).mem_nhds hxU] with y hy
        exact (hcomp y (subset_closure hy)).symm
      rw [hd, norm_mul, mul_pow]
      ring
    · have hfx : f x ∉ windowDomain η₁ a u b := by
        rw [← hW]
        rintro ⟨y, hy, hfy⟩
        obtain rfl : y = x := h2 (interior_subset (hUint hy)) (interior_subset hx) hfy
        exact hxU hy
      simp only [indicator_of_notMem hfx, indicator_of_notMem hxU, zero_mul]
  have hzero : ∀ y, y ∉ f '' interior (η₂ '' T) → (chartTest hc₁.1 hc₁.2.1 hc₁.2.2 ρ) y = 0 := by
    intro y hy
    rw [chartTest_apply]
    unfold chartTestFun
    refine indicator_of_notMem (fun hyU => hy ?_) _
    rw [← hW] at hyU
    exact image_mono hUint hyU
  have hpair := h6 _ _ hsupp hcoord hzero
  -- the change of variables `x = φ₂(w)` and `φ₁ = f ∘ φ₂`
  have hI1 : ∫ x, Real.log ‖deriv f x‖ * (chartTest hc₂.1 hc₂.2.1 hc₂.2.2 ρ) x =
      ∫ w, Real.log ‖deriv f (φ₂ w)‖ * ρ w :=
    integral_mul_chartTestFun hφ₂ (fun w hw => hψφ₂ w (ball_subset_closedBall hw)) hψ₂.differentiableOn
      (fun x => Real.log ‖deriv f x‖) ρ
  have hI2 : ∫ w, Real.log ‖deriv (chartMap (windowDomain η₂ a u b) (windowChartBG a u b η₂)) w‖ * ρ w =
      ∫ w, Real.log ‖deriv φ₂ w‖ * ρ w := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · dsimp only
      rw [deriv_chartMap_eq_of_isDiscMap hφ₂ hψ₂ hψφ₂ hw]
    · simp only [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero]
  have hI3 : ∫ w, Real.log ‖deriv (chartMap (windowDomain η₁ a u b) (windowChartBG a u b η₁)) w‖ * ρ w =
      ∫ w, (Real.log ‖deriv f (φ₂ w)‖ * ρ w + Real.log ‖deriv φ₂ w‖ * ρ w) := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · have hfd : DifferentiableAt ℂ f (φ₂ w) := h4.differentiableAt (isOpen_interior.mem_nhds (hUint (hφU w hw)))
      have hφd : DifferentiableAt ℂ φ₂ w := hφ₂.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
      dsimp only
      rw [deriv_chartMap_eq_of_isDiscMap hφ₁ hψ₁ hψφ₁ hw, deriv_comp w hfd hφd, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (hf'0 w hw)) (norm_ne_zero_iff.2 (hφ₂.deriv_ne_zero hw)), add_mul]
    · simp only [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero, add_zero]
  have hA : Integrable fun w => Real.log ‖deriv f (φ₂ w)‖ * ρ w :=
    integrable_log_norm_mul_test (g := fun w => deriv f (φ₂ w))
      ((h4.deriv isOpen_interior).continuousOn.comp hφ₂.differentiableOn.continuousOn
        fun w hw => hUint (hφU w hw)) hf'0 ρ
  have hB : Integrable fun w => Real.log ‖deriv φ₂ w‖ * ρ w :=
    integrable_log_norm_mul_test (hφ₂.differentiableOn.deriv isOpen_ball).continuousOn
      (fun w hw => hφ₂.deriv_ne_zero hw) ρ
  rw [chartFieldPairing_eq_of_isInverseChart hc₂, chartFieldPairing_eq_of_isInverseChart hc₁, hpair, hI1, hI2,
    hI3, integral_add hA hB]
  ring

/-- **The chart field off the event `η(a') = η(u)` is invariant under re-embedding.** -/
theorem IsSurfaceReembedding.windowFieldSurfaceBG_eq (hf : IsSurfaceReembedding γ T h₁ η₁ h₂ η₂ f)
    (hJ : Icc a b ⊆ T) (hau : a < u) (hub : u < b) :
    windowFieldSurfaceBG γ a u b (h₂, η₂) = windowFieldSurfaceBG γ a u b (h₁, η₁) := by
  have hu : u ∈ Icc a b := ⟨hau.le, hub.le⟩
  have hα := hf.windowStartBG_eq hJ hau hub
  have hαI := windowStartBG_mem_Icc (b := b) hau.le η₂
  have hiff : η₁ (windowStartBG a u b η₁) = η₁ u ↔ η₂ (windowStartBG a u b η₂) = η₂ u := by
    obtain ⟨h1, h2, -⟩ := hf
    have hαT : windowStartBG a u b η₂ ∈ T := hJ ⟨hαI.1, hαI.2.trans hub.le⟩
    rw [hα, ← h1 _ hαT, ← h1 u (hJ hu)]
    exact h2.eq_iff (mem_image_of_mem η₂ hαT) (mem_image_of_mem η₂ (hJ hu))
  unfold windowFieldSurfaceBG
  by_cases hne : η₂ (windowStartBG a u b η₂) = η₂ u
  · rw [indicator_of_notMem (show (h₂, η₂) ∉ windowFieldGoodSetBG a u b from fun h => h hne),
      indicator_of_notMem (show (h₁, η₁) ∉ windowFieldGoodSetBG a u b from fun h => h (hiff.2 hne))]
  · rw [indicator_of_mem (show (h₂, η₂) ∈ windowFieldGoodSetBG a u b from hne),
      indicator_of_mem (show (h₁, η₁) ∈ windowFieldGoodSetBG a u b from fun h => hne (hiff.1 h))]
    exact hf.windowFieldBG_eq hJ hau hub hne

end Reembedding

/-! ### Measurability for the `σ`-algebra of the curve-decorated quantum surface -/

/-- A Borel function of (field, curve) taking the same value at two pairs with the same curve-decorated quantum
surface over `T` is measurable for `curveSurfaceSigma γ T`. -/
theorem measurable_curveSurfaceSigma_of_forall_eq {γ : ℝ} {T : Set ℝ} {β : Type*} [MeasurableSpace β]
    {F : LQGMetric.DistC × C(ℝ, ℂ) → β} (hF : Measurable F)
    (hinv : ∀ p₁ p₂, SameCurveSurface γ T p₁ p₂ → F p₁ = F p₂) :
    Measurable[curveSurfaceSigma γ T] F := fun _ hA =>
  ⟨hF hA, fun p₁ p₂ h => by rw [mem_preimage, mem_preimage, hinv p₁ p₂ h]⟩

/-- **The chart field of a window is a Borel function of (field, curve).** -/
theorem measurable_windowFieldBG (γ a u b : ℝ) : Measurable (windowFieldBG γ a u b) := by
  let E₀ : LQGData := MatedCRT.FirstPass.Derived.LQGData.encode 0
  let K₀ : PathLawFamily := ContinuousMap.const ℂ
    (⟨Measure.dirac (ContinuousMap.const _ (0 : ℂ)), inferInstance⟩ : ProbabilityMeasure (ContinuousPath ℂ))
  have hι : Measurable fun p : LQGMetric.DistC × C(ℝ, ℂ) =>
      ((((LQGMetric.pairJ ⊤ p.1, E₀), p.2), K₀) : JointSample) :=
    (((measurable_pairJ_top.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd).prodMk
      measurable_const
  have heq : windowFieldBG γ a u b = (fun q : JointSample => windowChartField γ a u b (windowChartBG a u b q.1.2) q) ∘
      (fun p : LQGMetric.DistC × C(ℝ, ℂ) => ((((LQGMetric.pairJ ⊤ p.1, E₀), p.2), K₀) : JointSample)) := by
    funext p
    show windowFieldBG γ a u b p = windowFieldBG γ a u b (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ p.1), p.2)
    rw [LQGMetric.pairJInv_pairJ]
  rw [heq]
  exact (measurable_windowChartField_windowChartBG γ a u b).comp hι

theorem measurableSet_windowFieldGoodSetBG (a u b : ℝ) : MeasurableSet (windowFieldGoodSetBG a u b) := by
  have h1 : Measurable fun p : LQGMetric.DistC × C(ℝ, ℂ) => p.2 (windowStartBG a u b p.2) :=
    (ContinuousEval.continuous_eval (F := C(ℝ, ℂ))).measurable.comp
      (measurable_snd.prodMk ((measurable_windowStartBG a u b).comp measurable_snd))
  have h2 : Measurable fun p : LQGMetric.DistC × C(ℝ, ℂ) => p.2 u :=
    (continuous_eval_const (F := C(ℝ, ℂ)) u).measurable.comp measurable_snd
  exact (measurableSet_eq_fun h1 h2).compl

theorem measurable_windowFieldSurfaceBG (γ a u b : ℝ) : Measurable (windowFieldSurfaceBG γ a u b) :=
  (measurable_windowFieldBG γ a u b).indicator (measurableSet_windowFieldGoodSetBG a u b)

/-- **The chart field is a function of the curve-decorated quantum surface over `T ⊇ [a, b]`.** -/
theorem measurable_curveSurfaceSigma_windowFieldSurfaceBG {γ : ℝ} {T : Set ℝ} {a u b : ℝ} (hJ : Icc a b ⊆ T)
    (hau : a < u) (hub : u < b) : Measurable[curveSurfaceSigma γ T] (windowFieldSurfaceBG γ a u b) := by
  refine measurable_curveSurfaceSigma_of_forall_eq (measurable_windowFieldSurfaceBG γ a u b) ?_
  rintro ⟨h₁, η₁⟩ ⟨h₂, η₂⟩ ⟨f, hf⟩
  exact (hf.windowFieldSurfaceBG_eq hJ hau hub).symm

/-! ### The step of the proof of Lemma 7.21 -/

/-- **Berestycki–Gwynne (2020), proof of Lemma 7.21 (2003.10320.txt lines 3775-3776): the chart field of a window is
determined by the past (resp. future) curve-decorated quantum surface (`BG20WindowFieldSurfaceInput`).** The function
is `windowFieldSurfaceBG`: the chart field `windowFieldBG`, set to `0` on the event `η(a') = η(u)`. It is measurable for
`curveSurfaceSigma γ (Iic s)` when `b < s` and for `curveSurfaceSigma γ (Ici s)` when `s < a`
(`measurable_curveSurfaceSigma_windowFieldSurfaceBG`), and it agrees with the chart field almost surely: `a' < u`
(`windowStartBG_lt`) and the curve of a valid environment visits `η(u)` only at the time `u` almost surely
(`MatedCRTEnv.IsValid.ae_fixedTime_singleton_fibre`). -/
theorem bg20WindowFieldSurfaceInput (𝒮 : SpaceFillingSLEModel) : BG20WindowFieldSurfaceInput 𝒮 := by
  intro γ _ _ Ω _ S hS η' _ hae H _ _ a u b s hau hub
  have hae' : ∀ᵐ ω ∂S.P, windowFieldBG γ a u b (H ω, η' ω) = windowFieldSurfaceBG γ a u b (H ω, η' ω) := by
    filter_upwards [hS.ae_fixedTime_singleton_fibre u, hae] with ω hω hηω
    have hne : η' ω (windowStartBG a u b (η' ω)) ≠ η' ω u := by
      intro h
      rw [hηω] at h
      exact (windowStartBG_lt hau (η' ω)).ne (hω _ h)
    exact (indicator_of_mem (show (H ω, η' ω) ∈ windowFieldGoodSetBG a u b from hne) _).symm
  exact ⟨fun hbs => ⟨windowFieldSurfaceBG γ a u b,
      measurable_curveSurfaceSigma_windowFieldSurfaceBG (Icc_subset_Iic_self.trans (Iic_subset_Iic.2 hbs.le))
        hau hub, hae'⟩,
    fun hsa => ⟨windowFieldSurfaceBG γ a u b,
      measurable_curveSurfaceSigma_windowFieldSurfaceBG (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hsa.le))
        hau hub, hae'⟩⟩

end MatedCRT
