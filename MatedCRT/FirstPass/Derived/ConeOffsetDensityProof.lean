import MatedCRT.FirstPass.Derived.GMS21Lemma33Cone

/-!
# The density of the two signed offsets of a quantum cone

`ConeOffsetDensity` (`GMS21Lemma33Cone.lean`) states that for a mating-of-trees coupling, cutoffs `a > 0`,
`0 < δ < M` and either cone (`β = γ` or `β = 0`), the offsets `(-μ(ηL([-a, 0])), μ(ηL([0, a])))` are random
variables and the joint law of the outer data `(ηL, μ|{δ < |z| < M})` and the offsets is absolutely continuous
with respect to the law of the outer data times Lebesgue measure on `ℝ²` (Gwynne–Miller–Sheffield,
arXiv:1705.11161, proof of Lemma 3.3).

The argument. Almost surely there are two disjoint rational closed disks `D₋, D₊ ⊂ B_{min(1, δ)}(0) \ {0}`
which `ηL` visits only during `(-a, 0)` and `(0, a)` respectively (`ηL` is continuous, surjective, proper,
rooted at `0` and parametrized by Lebesgue measure, so points visited at two times form a null set). Smooth
bumps `f_±` supported in `D_±` change the area measure by the factor `exp(γ(x₋ f₋ + x₊ f₊))`; this tilt
leaves the outer data unchanged and moves the two offsets by the strictly monotone `C¹` functions
`x ↦ ∫_{ηL(J_±)} exp(γ x f_±) dμ`. The law of `(ηL, μ)` is absolutely continuous with respect to the law of
every such tilt (`ConeAreaBumpTilt`: Cameron–Martin for the whole-plane GFF and Girsanov for the radial
Brownian motion, with the Weyl scaling of the area measure), and averaging over the tilt parameter
`x ∈ ℝ²` gives the density (`absolutelyContinuous_map_prod_volume_of_tilts`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

/-! ### Null preimages under one- and two-dimensional diffeomorphisms -/

/-- A differentiable injective map `ℝ → ℝ` with nowhere vanishing derivative pulls back Lebesgue-null sets to
Lebesgue-null sets. -/
theorem volume_preimage_eq_zero_of_hasDerivAt {g g' : ℝ → ℝ} (hd : ∀ t, HasDerivAt g (g' t) t)
    (h0 : ∀ t, g' t ≠ 0) (hinj : Function.Injective g) {N : Set ℝ} (hN : volume N = 0) :
    volume (g ⁻¹' N) = 0 := by
  obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
  have hgm : Measurable g := (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt).measurable
  have hs : MeasurableSet (g ⁻¹' N') := hgm hN'm
  refine measure_mono_null (preimage_mono hNN') ?_
  have key := lintegral_image_eq_lintegral_abs_deriv_mul hs (fun t _ => (hd t).hasDerivWithinAt)
    hinj.injOn (fun _ => 1)
  have himg : volume (g '' (g ⁻¹' N')) = 0 := measure_mono_null (image_preimage_subset g N') hN'0
  simp only [mul_one, lintegral_one, Measure.restrict_apply_univ] at key
  rw [himg] at key
  have hg' : ∀ t, g' t = deriv g t := fun t => (hd t).deriv.symm
  have hm : Measurable fun t => ENNReal.ofReal |g' t| := by
    have : (fun t => ENNReal.ofReal |g' t|) = fun t => ENNReal.ofReal |deriv g t| := by
      funext t; rw [hg' t]
    rw [this]
    exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_deriv g))
  have hfalse : ∀ᵐ t ∂(volume.restrict (g ⁻¹' N')), False := by
    filter_upwards [(lintegral_eq_zero_iff hm).1 key.symm] with t ht
    have ht' : ENNReal.ofReal |g' t| = 0 := ht
    exact h0 t (abs_nonpos_iff.1 (ENNReal.ofReal_eq_zero.1 ht'))
  simpa using ae_iff.1 hfalse

/-- A product of two maps `ℝ → ℝ` that pull back Lebesgue-null sets to Lebesgue-null sets pulls back
Lebesgue-null subsets of `ℝ²` to Lebesgue-null sets. -/
theorem volume_preimage_eq_zero_of_fin_two {g₀ g₁ : ℝ → ℝ} (hm₀ : Measurable g₀) (hm₁ : Measurable g₁)
    (h₀ : ∀ N : Set ℝ, volume N = 0 → volume (g₀ ⁻¹' N) = 0)
    (h₁ : ∀ N : Set ℝ, volume N = 0 → volume (g₁ ⁻¹' N) = 0) {N : Set (Fin 2 → ℝ)} (hN : volume N = 0) :
    volume ((fun x : Fin 2 → ℝ => ![g₀ (x 0), g₁ (x 1)]) ⁻¹' N) = 0 := by
  have hpm : Measurable (Prod.map g₀ g₁) := hm₀.prodMap hm₁
  have key : ∀ {N : Set (ℝ × ℝ)}, volume N = 0 → volume (Prod.map g₀ g₁ ⁻¹' N) = 0 := by
    intro N hN
    obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN
    refine measure_mono_null (preimage_mono hNN') ?_
    rw [Measure.volume_eq_prod] at hN'0 ⊢
    have hB := ae_iff.1 ((Measure.measure_prod_null hN'm).1 hN'0)
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), volume (Prod.mk (g₀ x) ⁻¹' N') = 0 :=
      ae_iff.2 (h₀ _ hB)
    refine (Measure.measure_prod_null (hpm hN'm)).2 ?_
    filter_upwards [hae] with x hx
    exact h₁ _ hx
  have q : Measure.QuasiMeasurePreserving (Prod.map g₀ g₁) (volume : Measure (ℝ × ℝ)) volume :=
    ⟨hpm, Measure.AbsolutelyContinuous.mk fun s hs h => by rw [Measure.map_apply hpm hs]; exact key h⟩
  have he := (volume_preserving_finTwoArrow ℝ).quasiMeasurePreserving
  have hes := (volume_preserving_finTwoArrow ℝ).symm.quasiMeasurePreserving
  have hcomp := hes.comp (q.comp he)
  have hfun : (fun x : Fin 2 → ℝ => ![g₀ (x 0), g₁ (x 1)]) =
      (MeasurableEquiv.finTwoArrow).symm ∘ Prod.map g₀ g₁ ∘ MeasurableEquiv.finTwoArrow := by
    funext x
    ext i
    fin_cases i <;> rfl
  rw [hfun]
  exact hcomp.preimage_null hN

/-! ### Absolute continuity from tilts -/

/-- **Density of two coordinates from tilts.** Let `ρ` be a finite measure on `Z` and `G : Z → Y × ℝ²`
measurable, with first coordinate the "outer data" and second the "offsets". Suppose that on each of countably
many events `E k` covering `ρ`-almost all of `Z`, there are maps `T k x` (`x ∈ ℝ²`, jointly measurable in
`(x, z)`) preserving `E k` and the outer data, such that `ρ` is absolutely continuous with respect to its image
under every `T k x`, and for `ρ`-almost every `z ∈ E k` the offsets `x ↦ (G (T k x z)).2` pull back
Lebesgue-null sets to Lebesgue-null sets. Then the image of `ρ` under `G` is absolutely continuous with respect
to the image of `ρ` under the outer data times Lebesgue measure. -/
theorem absolutelyContinuous_map_prod_volume_of_tilts {Z Y : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] {ρ : Measure Z} [IsFiniteMeasure ρ] {G : Z → Y × (Fin 2 → ℝ)} (hG : Measurable G)
    {ι : Type*} [Countable ι] (E : ι → Set Z) (hE : ∀ k, MeasurableSet (E k))
    (hcover : ∀ᵐ z ∂ρ, ∃ k, z ∈ E k) (T : ι → (Fin 2 → ℝ) → Z → Z)
    (hTm : ∀ k, Measurable fun p : (Fin 2 → ℝ) × Z => T k p.1 p.2)
    (hTE : ∀ k x z, T k x z ∈ E k ↔ z ∈ E k) (hac : ∀ k x, ρ ≪ ρ.map (T k x))
    (hGT : ∀ k x z, z ∈ E k → (G (T k x z)).1 = (G z).1)
    (hnull : ∀ k, ∀ᵐ z ∂ρ, z ∈ E k → ∀ N : Set (Fin 2 → ℝ), volume N = 0 →
      volume ((fun x => (G (T k x z)).2) ⁻¹' N) = 0) :
    ρ.map G ≪ (ρ.map fun z => (G z).1).prod volume := by
  have hO : Measurable fun z => (G z).1 := measurable_fst.comp hG
  refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
  rw [Measure.map_apply hG hS]
  have hsec : ∀ᵐ z ∂ρ, volume (Prod.mk (G z).1 ⁻¹' S) = 0 := by
    filter_upwards [ae_of_ae_map hO.aemeasurable ((Measure.measure_prod_null hS).1 hS0)] with z hz
      using hz
  have hk : ∀ k, ρ (G ⁻¹' S ∩ E k) = 0 := by
    intro k
    have hAm : MeasurableSet (G ⁻¹' S ∩ E k) := (hG hS).inter (hE k)
    have hTkm : ∀ x, Measurable (T k x) := fun x =>
      (hTm k).comp (measurable_const.prodMk measurable_id)
    set B : Set (Z × (Fin 2 → ℝ)) := {p | p.1 ∈ E k ∧ ((G p.1).1, (G (T k p.2 p.1)).2) ∈ S}
      with hBdef
    have hBm : MeasurableSet B :=
      ((hE k).preimage measurable_fst).inter (hS.preimage ((hO.comp measurable_fst).prodMk
        (measurable_snd.comp (hG.comp ((hTm k).comp (measurable_snd.prodMk measurable_fst))))))
    have hTx : ∀ x, (ρ.map (T k x)) (G ⁻¹' S ∩ E k) = ρ ((fun z => (z, x)) ⁻¹' B) := by
      intro x
      rw [Measure.map_apply (hTkm x) hAm]
      congr 1
      ext z
      change (G (T k x z) ∈ S ∧ T k x z ∈ E k) ↔ (z ∈ E k ∧ ((G z).1, (G (T k x z)).2) ∈ S)
      rw [hTE]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        rw [← hGT k x z h2]
        exact h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1⟩
        rw [← hGT k x z h1] at h2
        exact h2
    have h0 : (ρ.prod volume) B = 0 := by
      rw [Measure.prod_apply hBm]
      apply (lintegral_eq_zero_iff (measurable_measure_prodMk_left hBm)).2
      filter_upwards [hsec, hnull k] with z hz hnz
      show volume (Prod.mk z ⁻¹' B) = 0
      by_cases hEk : z ∈ E k
      · have hpre : Prod.mk z ⁻¹' B = (fun x => (G (T k x z)).2) ⁻¹' (Prod.mk (G z).1 ⁻¹' S) := by
          ext x
          exact and_iff_right hEk
        rw [hpre]
        exact hnz hEk _ hz
      · have hpre : Prod.mk z ⁻¹' B = ∅ := by
          ext x
          exact iff_of_false (fun h => hEk h.1) (mem_empty_iff_false x).1
        rw [hpre, measure_empty]
    rw [Measure.prod_apply_symm hBm] at h0
    have hint := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hBm)).1 h0
    by_contra hne
    have hF : ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), False := by
      filter_upwards [hint] with x hx
      exact hne (hac k x ((hTx x).trans hx))
    exact (isOpen_univ.measure_ne_zero (volume : Measure (Fin 2 → ℝ)) univ_nonempty)
      (by simpa using ae_iff.1 hF)
  have hsub : G ⁻¹' S ⊆ (⋃ k, (G ⁻¹' S ∩ E k)) ∪ {z | ¬ ∃ k, z ∈ E k} := by
    intro z hz
    by_cases h : ∃ k, z ∈ E k
    · obtain ⟨k, hk⟩ := h
      exact Or.inl (mem_iUnion.2 ⟨k, hz, hk⟩)
    · exact Or.inr h
  exact measure_mono_null hsub (measure_union_null (measure_iUnion_null hk) (ae_iff.1 hcover))

/-! ### The tilt input -/

/-- **The area measure of a quantum cone is quasi-invariant under smooth tilts away from the origin**
(Cameron–Martin for the whole-plane GFF, Girsanov for the radial Brownian motion and the Weyl scaling of the
area measure). PENDING TRUTH CHECK.

Let `X` be a whole-plane GFF and `B, B'` standard Brownian motions with the independence structure of the cone
data, `β ∈ {0, γ}`, `μ = quantumConeArea γ β X B B'` the `γ`-LQG area measure of the circle-average embedding
`coneField X (coneRadial γ β B B')` of the `β`-quantum cone, and `e` a random curve independent of `(X, B, B')`.
For every smooth `f` whose support is a compact subset of `B_1(0) \ {0}`, the law of `(e, μ)` is absolutely
continuous with respect to the law of `(e, e^{γ f} μ)`.

Argument: the field changes by a smooth bump `f` with zero average on every centred circle of radius at least one. Write
`f = f_lat + f̄` with `f̄` the rotation average of `f`, and `φ(t) = f̄_{e^{-t}}(0)`. The cone field depends on `X`
only through its lateral part `L`, and the cone field of `(L + f_lat, B + φ, B')` is
`coneField X (coneRadial γ β B B') + f`. The law of `(L + f_lat, B + φ, B')` is mutually absolutely continuous
with the law of `(L, B, B')`: Cameron–Martin for the lateral projection `L` of the whole-plane GFF (the
definition `IsWholePlaneGFF` leaves a field-dependent additive constant free, so the shift is taken on `L`, not
on `X`; Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, Proposition 1.36 and §1.7) and
Girsanov for `B + φ` (`φ` smooth with compact support in `(0, ∞)`). The area measure of `h + f` is `e^{γ f}`
times that of `h` (Weyl scaling; Bou-Rabee–Gwynne, arXiv:2211.04891, Fact 2.2(III); Duplantier–Sheffield,
Proposition 2.1 and Lemma 2.6). Proved as `coneAreaBumpTilt` (`ConeAreaBumpTiltProof.lean`). -/
def ConeAreaBumpTilt (γ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (β : ℝ) (X : Ω → Field)
    (B B' : ℝ≥0 → Ω → ℝ) (e : Ω → C(ℝ, ℂ)), γ ∈ Ioo (0 : ℝ) 2 → (β = 0 ∨ β = γ) →
    LQGMetric.IsWholePlaneGFF X P → IsBrownianReal B P → IsBrownianReal B' P →
    (IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) →
    Measurable e → IndepFun e (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P →
    ∀ f : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → tsupport f ⊆ ball (0 : ℂ) 1 \ {0} →
      P.map (fun ω => (e ω, quantumConeArea γ β X B B' ω)) ≪
        P.map (fun ω => (e ω, (quantumConeArea γ β X B B' ω).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * f z)))))

/-! ### Rational points and rational disks -/

/-- The point `q₁ + q₂ i` with rational coordinates. -/
def coneRatPoint (q : ℚ × ℚ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

/-- The closed disk with rational center `q.1` and rational radius `q.2`. -/
def coneRatDisk (q : (ℚ × ℚ) × ℚ) : Set ℂ := closedBall (coneRatPoint q.1) q.2

theorem exists_coneRatPoint_dist_lt (w : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ × ℚ, dist (coneRatPoint q) w < ε := by
  obtain ⟨q₁, h₁, h₁'⟩ := exists_rat_btwn (show w.re - ε / 4 < w.re + ε / 4 by linarith)
  obtain ⟨q₂, h₂, h₂'⟩ := exists_rat_btwn (show w.im - ε / 4 < w.im + ε / 4 by linarith)
  refine ⟨(q₁, q₂), ?_⟩
  have hre : (coneRatPoint (q₁, q₂) - w).re = q₁ - w.re := by simp [coneRatPoint]
  have him : (coneRatPoint (q₁, q₂) - w).im = q₂ - w.im := by simp [coneRatPoint]
  rw [dist_eq_norm]
  calc ‖coneRatPoint (q₁, q₂) - w‖ ≤ |(coneRatPoint (q₁, q₂) - w).re| + |(coneRatPoint (q₁, q₂) - w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 4 + ε / 4 := by
        rw [hre, him]
        exact add_lt_add (abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩)
          (abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩)
    _ < ε := by linarith

theorem exists_coneRatDisk_subset_ball (w : ℂ) {d : ℝ} (hd : 0 < d) :
    ∃ (c : ℚ × ℚ) (r : ℚ), 0 < (r : ℝ) ∧ closedBall (coneRatPoint c) r ⊆ ball w d := by
  obtain ⟨c, hc⟩ := exists_coneRatPoint_dist_lt w (half_pos hd)
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (half_pos hd)
  refine ⟨c, r, hr0, fun y hy => ?_⟩
  rw [mem_closedBall] at hy
  rw [mem_ball]
  have := dist_triangle y (coneRatPoint c) w
  linarith

/-! ### Curves parametrized by Lebesgue measure -/

section CurveGeometry

variable {e : C(ℝ, ℂ)}

/-- For a curve parametrized by Lebesgue measure, the images of adjacent intervals meet in a null set. -/
theorem volume_image_inter_image_adjacent
    (hvol : ∀ s t : ℝ, s ≤ t → volume (e '' Icc s t) = ENNReal.ofReal (t - s)) {s t u : ℝ} (hst : s ≤ t)
    (htu : t ≤ u) : volume (e '' Icc s t ∩ e '' Icc t u) = 0 := by
  have hB : MeasurableSet (e '' Icc t u) := (isCompact_Icc.image e.continuous).isClosed.measurableSet
  have h := measure_union_add_inter (μ := volume) (e '' Icc s t) hB
  rw [← image_union, Icc_union_Icc_eq_Icc hst htu, hvol s u (hst.trans htu), hvol s t hst, hvol t u htu,
    ← ENNReal.ofReal_add (sub_nonneg.2 hst) (sub_nonneg.2 htu),
    show t - s + (u - t) = u - s by ring] at h
  exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 (h.trans (add_zero _).symm)

/-- For a curve parametrized by Lebesgue measure, the points of `e([p, p'])` visited at a time outside
`(p, p')` form a null set. -/
theorem volume_image_Icc_inter_image_compl_Ioo
    (hvol : ∀ s t : ℝ, s ≤ t → volume (e '' Icc s t) = ENNReal.ofReal (t - s)) {p p' : ℝ} (hpp : p ≤ p') :
    volume (e '' Icc p p' ∩ e '' (Ioo p p')ᶜ) = 0 := by
  have hcov : e '' (Ioo p p')ᶜ ⊆ ⋃ n : ℕ, (e '' Icc (p - n) p ∪ e '' Icc p' (p' + n)) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ≤ p ∨ p' ≤ t := by
      by_contra h
      exact ht ⟨not_le.1 (not_or.1 h).1, not_le.1 (not_or.1 h).2⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (max (p - t) (t - p'))
    have h1 := le_max_left (p - t) (t - p')
    have h2 := le_max_right (p - t) (t - p')
    refine mem_iUnion.2 ⟨n, ?_⟩
    rcases ht' with h | h
    · exact Or.inl ⟨t, ⟨by linarith, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨h, by linarith⟩, rfl⟩
  refine measure_mono_null (inter_subset_inter_right _ hcov) ?_
  rw [inter_iUnion]
  refine measure_iUnion_null fun n => ?_
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [inter_union_distrib_left]
  refine measure_union_null ?_ ?_
  · rw [inter_comm]
    exact volume_image_inter_image_adjacent hvol (by linarith) hpp
  · exact volume_image_inter_image_adjacent hvol hpp (by linarith)

/-- A proper curve parametrized by Lebesgue measure has, for `p < p'`, a point `e(t)`, `t ∈ (p, p')`, with a
ball around it missed by `e(ℝ \ (p, p'))`. -/
theorem exists_ball_disjoint_image_compl (hprop : IsProperMap e)
    (hvol : ∀ s t : ℝ, s ≤ t → volume (e '' Icc s t) = ENNReal.ofReal (t - s)) {p p' : ℝ} (hpp : p < p') :
    ∃ t ∈ Ioo p p', ∃ r > 0, Disjoint (ball (e t) r) (e '' (Ioo p p')ᶜ) := by
  have hF : IsClosed (e '' (Ioo p p')ᶜ) := hprop.isClosedMap _ isOpen_Ioo.isClosed_compl
  have hpos : volume (e '' Icc p p') ≠ 0 := by
    rw [hvol p p' hpp.le, Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hne : (e '' Icc p p' \ e '' (Ioo p p')ᶜ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    exact hpos (measure_mono_null (subset_inter subset_rfl h)
      (volume_image_Icc_inter_image_compl_Ioo hvol hpp.le))
  obtain ⟨_, ⟨t, -, rfl⟩, hnot⟩ := hne
  have htI : t ∈ Ioo p p' := by
    by_contra h
    exact hnot ⟨t, h, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hF.isOpen_compl (e t) hnot
  exact ⟨t, htI, r, hr, Set.subset_compl_iff_disjoint_right.1 hball⟩

/-- A rational disk inside a prescribed open set, visited only during `(p, p')`. -/
theorem exists_coneRatDisk_only_during (hsurj : Function.Surjective e) (hprop : IsProperMap e)
    (hvol : ∀ s t : ℝ, s ≤ t → volume (e '' Icc s t) = ENNReal.ofReal (t - s)) {p p' : ℝ} (hpp : p < p')
    {V : Set ℂ} (hV : IsOpen V) (hIV : e '' Ioo p p' ⊆ V) :
    ∃ q : (ℚ × ℚ) × ℚ, 0 < (q.2 : ℝ) ∧ coneRatDisk q ⊆ V ∧ coneRatDisk q ⊆ e '' Ioo p p' ∧
      Disjoint (coneRatDisk q) (e '' (Ioo p p')ᶜ) := by
  obtain ⟨t, ht, r, hr, hdisj⟩ := exists_ball_disjoint_image_compl hprop hvol hpp
  obtain ⟨r', hr', hballV⟩ := Metric.isOpen_iff.1 hV (e t) (hIV ⟨t, ht, rfl⟩)
  obtain ⟨c, s, hs, hsub⟩ := exists_coneRatDisk_subset_ball (e t) (lt_min hr hr')
  have hdisj' : Disjoint (coneRatDisk (c, s)) (e '' (Ioo p p')ᶜ) :=
    hdisj.mono_left (hsub.trans (ball_subset_ball (min_le_left _ _)))
  refine ⟨(c, s), hs, hsub.trans ((ball_subset_ball (min_le_right _ _)).trans hballV), ?_, hdisj'⟩
  intro y hy
  obtain ⟨t', rfl⟩ := hsurj y
  refine ⟨t', ?_, rfl⟩
  by_contra h
  exact hdisj'.ne_of_mem hy ⟨t', h, rfl⟩ rfl

/-- **The curve event of a pair of rational disks**: the first disk is filled during `[-a, 0]` and missed
during `[0, a]`, the second is filled during `[0, a]` and missed during `[-a, 0]`. -/
def offsetCurveEvent (a : ℝ) (k : ((ℚ × ℚ) × ℚ) × ((ℚ × ℚ) × ℚ)) : Set C(ℝ, ℂ) :=
  {e | MapsTo e (Icc (-a) 0) (coneRatDisk k.2)ᶜ ∧ MapsTo e (Icc 0 a) (coneRatDisk k.1)ᶜ ∧
    coneRatDisk k.1 ⊆ e '' Icc (-a) 0 ∧ coneRatDisk k.2 ⊆ e '' Icc 0 a}

/-- **Two rational disks visited only during the two time blocks.** A continuous, surjective, proper curve
rooted at `0` and parametrized by Lebesgue measure has, for `a > 0` and `ρ > 0`, two rational disks in
`B_ρ(0) \ {0}` in its curve event. -/
theorem exists_offsetDisks (hsurj : Function.Surjective e) (hprop : IsProperMap e) (h0 : e 0 = 0)
    (hvol : ∀ s t : ℝ, s ≤ t → volume (e '' Icc s t) = ENNReal.ofReal (t - s)) {a ρ : ℝ} (ha : 0 < a)
    (hρ : 0 < ρ) :
    ∃ k : ((ℚ × ℚ) × ℚ) × ((ℚ × ℚ) × ℚ), 0 < (k.1.2 : ℝ) ∧ 0 < (k.2.2 : ℝ) ∧
      coneRatDisk k.1 ⊆ ball 0 ρ \ {0} ∧ coneRatDisk k.2 ⊆ ball 0 ρ \ {0} ∧ e ∈ offsetCurveEvent a k := by
  obtain ⟨τ, hτ, hτe⟩ := Metric.continuousAt_iff.1 e.continuous.continuousAt ρ hρ
  have hm0 : 0 < min a τ := lt_min ha hτ
  have hma : min a τ ≤ a := min_le_left _ _
  have hmτ : min a τ ≤ τ := min_le_right _ _
  have hsmall : ∀ t : ℝ, |t| < τ → e t ∈ ball (0 : ℂ) ρ := by
    intro t ht
    have h := hτe (show dist t 0 < τ by rwa [Real.dist_eq, sub_zero])
    rw [h0] at h
    exact h
  obtain ⟨qm, hqm0, hqmV, hqmin, hqmdis⟩ := exists_coneRatDisk_only_during hsurj hprop hvol
    (show -min a τ / 2 < -min a τ / 4 by linarith) isOpen_ball (by
      rintro _ ⟨t, ht, rfl⟩
      exact hsmall t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]))
  obtain ⟨qp, hqp0, hqpV, hqpin, hqpdis⟩ := exists_coneRatDisk_only_during hsurj hprop hvol
    (show min a τ / 4 < min a τ / 2 by linarith) isOpen_ball (by
      rintro _ ⟨t, ht, rfl⟩
      exact hsmall t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]))
  have h0m : (0 : ℂ) ∈ e '' (Ioo (-min a τ / 2) (-min a τ / 4))ᶜ :=
    ⟨0, fun h => by linarith [h.2], h0⟩
  have h0p : (0 : ℂ) ∈ e '' (Ioo (min a τ / 4) (min a τ / 2))ᶜ :=
    ⟨0, fun h => by linarith [h.1], h0⟩
  refine ⟨(qm, qp), hqm0, hqp0, fun y hy => ⟨hqmV hy, fun h => hqmdis.ne_of_mem hy h0m h⟩,
    fun y hy => ⟨hqpV hy, fun h => hqpdis.ne_of_mem hy h0p h⟩, ?_⟩
  show MapsTo e (Icc (-a) 0) (coneRatDisk qp)ᶜ ∧ MapsTo e (Icc 0 a) (coneRatDisk qm)ᶜ ∧
    coneRatDisk qm ⊆ e '' Icc (-a) 0 ∧ coneRatDisk qp ⊆ e '' Icc 0 a
  refine ⟨fun t ht hmem => hqpdis.ne_of_mem hmem ⟨t, fun h => by linarith [h.1, ht.2], rfl⟩ rfl,
    fun t ht hmem => hqmdis.ne_of_mem hmem ⟨t, fun h => by linarith [h.2, ht.1], rfl⟩ rfl,
    hqmin.trans (image_mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩),
    hqpin.trans (image_mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)⟩

end CurveGeometry

/-! ### Measurability of the curve event -/

theorem isClosed_setOf_mem_image {K : Set ℝ} (hK : IsCompact K) (y : ℂ) :
    IsClosed {e : C(ℝ, ℂ) | y ∈ e '' K} := by
  have hc : {e : C(ℝ, ℂ) | y ∈ e '' K}ᶜ = {e : C(ℝ, ℂ) | MapsTo e K {y}ᶜ} := by
    ext e
    constructor
    · intro h t ht hy
      exact h ⟨t, ht, hy⟩
    · rintro h ⟨t, ht, hy⟩
      exact h ht hy
  rw [← isOpen_compl_iff, hc]
  exact ContinuousMap.isOpen_setOfPred_mapsTo hK isOpen_compl_singleton

theorem measurableSet_setOf_coneRatDisk_subset_image {K : Set ℝ} (hK : IsCompact K) (q : (ℚ × ℚ) × ℚ)
    (hq : 0 < (q.2 : ℝ)) : MeasurableSet {e : C(ℝ, ℂ) | coneRatDisk q ⊆ e '' K} := by
  have heq : {e : C(ℝ, ℂ) | coneRatDisk q ⊆ e '' K} =
      ⋂ c : ℚ × ℚ, {e : C(ℝ, ℂ) | coneRatPoint c ∈ ball (coneRatPoint q.1) q.2 → coneRatPoint c ∈ e '' K} := by
    ext e
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h c hc
      exact h (ball_subset_closedBall hc)
    · intro h y hy
      have hcl : IsClosed (e '' K) := (hK.image e.continuous).isClosed
      rw [← hcl.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      have hy' : y ∈ closure (ball (coneRatPoint q.1) (q.2 : ℝ)) := by
        rw [closure_ball _ hq.ne']
        exact hy
      obtain ⟨y', hy'b, hyy'⟩ := Metric.mem_closure_iff.1 hy' (ε / 2) (half_pos hε)
      have hgap : 0 < (q.2 : ℝ) - dist y' (coneRatPoint q.1) := by
        rw [mem_ball] at hy'b
        linarith
      obtain ⟨c, hc⟩ := exists_coneRatPoint_dist_lt y' (lt_min (half_pos hε) hgap)
      have hm1 := min_le_left (ε / 2) ((q.2 : ℝ) - dist y' (coneRatPoint q.1))
      have hm2 := min_le_right (ε / 2) ((q.2 : ℝ) - dist y' (coneRatPoint q.1))
      have hcb : coneRatPoint c ∈ ball (coneRatPoint q.1) q.2 := by
        rw [mem_ball]
        have := dist_triangle (coneRatPoint c) y' (coneRatPoint q.1)
        linarith
      refine ⟨coneRatPoint c, h c hcb, ?_⟩
      have h3 := dist_triangle y y' (coneRatPoint c)
      have h4 := dist_comm y' (coneRatPoint c)
      linarith
  rw [heq]
  refine MeasurableSet.iInter fun c => ?_
  by_cases hc : coneRatPoint c ∈ ball (coneRatPoint q.1) (q.2 : ℝ)
  · have h1 : {e : C(ℝ, ℂ) | coneRatPoint c ∈ ball (coneRatPoint q.1) q.2 → coneRatPoint c ∈ e '' K} =
        {e : C(ℝ, ℂ) | coneRatPoint c ∈ e '' K} := by
      ext e
      exact ⟨fun h => h hc, fun h _ => h⟩
    rw [h1]
    exact (isClosed_setOf_mem_image hK _).measurableSet
  · have h1 : {e : C(ℝ, ℂ) | coneRatPoint c ∈ ball (coneRatPoint q.1) q.2 → coneRatPoint c ∈ e '' K} = univ := by
      ext e
      exact ⟨fun _ => trivial, fun _ h => absurd h hc⟩
    rw [h1]
    exact MeasurableSet.univ

theorem measurableSet_offsetCurveEvent (a : ℝ) (k : ((ℚ × ℚ) × ℚ) × ((ℚ × ℚ) × ℚ))
    (hk1 : 0 < (k.1.2 : ℝ)) (hk2 : 0 < (k.2.2 : ℝ)) : MeasurableSet (offsetCurveEvent a k) := by
  have hc : ∀ q : (ℚ × ℚ) × ℚ, IsOpen (coneRatDisk q)ᶜ := fun q => isClosed_closedBall.isOpen_compl
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (hc _)).measurableSet.inter
    ((ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (hc _)).measurableSet.inter
      ((measurableSet_setOf_coneRatDisk_subset_image isCompact_Icc k.1 hk1).inter
        (measurableSet_setOf_coneRatDisk_subset_image isCompact_Icc k.2 hk2)))

/-! ### The cover mass -/

/-- The union of the open rational balls of a finite family. -/
def ratCover (C : Finset ((ℚ × ℚ) × ℚ)) : Set ℂ := ⋃ q ∈ C, ball (coneRatPoint q.1) q.2

theorem isOpen_ratCover (C : Finset ((ℚ × ℚ) × ℚ)) : IsOpen (ratCover C) :=
  isOpen_biUnion fun _ _ => isOpen_ball

open scoped Classical in
/-- **The cover mass** of `e(J)` for `ν`: the infimum of `ν(U)` over the finite unions `U` of open rational balls
containing `e(J)`. It is measurable in `(e, ν)` and equals `ν(e(J))` when `ν` is finite near `e(J)`. -/
def coverMass (J : Set ℝ) (e : C(ℝ, ℂ)) (ν : Measure ℂ) : ℝ≥0∞ :=
  ⨅ C : Finset ((ℚ × ℚ) × ℚ), if MapsTo e J (ratCover C) then ν (ratCover C) else ∞

theorem measurable_coverMass {J : Set ℝ} (hJ : IsCompact J) :
    Measurable fun z : C(ℝ, ℂ) × Measure ℂ => coverMass J z.1 z.2 := by
  unfold coverMass
  refine Measurable.iInf fun C => Measurable.ite ?_
    ((Measure.measurable_coe (isOpen_ratCover C).measurableSet).comp measurable_snd) measurable_const
  exact measurable_fst ((ContinuousMap.isOpen_setOfPred_mapsTo hJ (isOpen_ratCover C)).measurableSet)

theorem coverMass_eq {J : Set ℝ} (hJ : IsCompact J) (e : C(ℝ, ℂ)) {ν : Measure ℂ}
    (hfin : ∃ R > 0, ν (cthickening R (e '' J)) ≠ ∞) : coverMass J e ν = ν (e '' J) := by
  classical
  have hK : IsCompact (e '' J) := hJ.image e.continuous
  apply le_antisymm
  · have hlim : Tendsto (fun r => ν (cthickening r (e '' J))) (𝓝[>] 0) (𝓝 (ν (e '' J))) :=
      (tendsto_measure_cthickening_of_isClosed hfin hK.isClosed).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    obtain ⟨s, hs0, hsr⟩ := exists_rat_btwn (show (0 : ℝ) < r / 4 by linarith)
    have hq : ∀ x : ℂ, ∃ c : ℚ × ℚ, dist (coneRatPoint c) x < s := fun x => exists_coneRatPoint_dist_lt x hs0
    choose c hc using hq
    obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover (fun x => ball (coneRatPoint (c x)) ((2 * s : ℚ) : ℝ))
      (fun x _ => isOpen_ball.mem_nhds (by
        rw [mem_ball, dist_comm]
        push_cast
        linarith [hc x]))
    have hcov : ratCover (t.image fun x => (c x, 2 * s)) =
        ⋃ x ∈ t, ball (coneRatPoint (c x)) ((2 * s : ℚ) : ℝ) := by
      rw [ratCover, Finset.set_biUnion_finset_image]
    have hmaps : MapsTo e J (ratCover (t.image fun x => (c x, 2 * s))) := by
      intro τ hτ
      rw [hcov]
      exact ht ⟨τ, hτ, rfl⟩
    have hsub : ratCover (t.image fun x => (c x, 2 * s)) ⊆ cthickening r (e '' J) := by
      rw [hcov]
      intro y hy
      simp only [mem_iUnion] at hy
      obtain ⟨x, hxt, hy⟩ := hy
      apply Metric.thickening_subset_cthickening r (e '' J)
      rw [mem_thickening_iff]
      refine ⟨x, htK x hxt, ?_⟩
      rw [mem_ball] at hy
      push_cast at hy
      have := dist_triangle y (coneRatPoint (c x)) x
      linarith [hc x]
    calc coverMass J e ν
        ≤ (if MapsTo e J (ratCover (t.image fun x => (c x, 2 * s)))
            then ν (ratCover (t.image fun x => (c x, 2 * s))) else ∞) := by
          unfold coverMass
          exact iInf_le (fun C => if MapsTo e J (ratCover C) then ν (ratCover C) else ∞) _
      _ = ν (ratCover (t.image fun x => (c x, 2 * s))) := ite_eq_left hmaps
      _ ≤ ν (cthickening r (e '' J)) := measure_mono hsub
  · unfold coverMass
    refine le_iInf fun C => ?_
    split_ifs with h
    · exact measure_mono h.image_subset
    · exact le_top

/-! ### Locally finite measures charging every rational disk -/

/-- A measure on `ℂ` finite on bounded sets and positive on every open rational disk. -/
def OffsetGoodMeasure (ν : Measure ℂ) : Prop :=
  (∀ n : ℕ, ν (closedBall 0 n) ≠ ∞) ∧
    ∀ q : (ℚ × ℚ) × ℚ, 0 < (q.2 : ℝ) → 0 < ν (ball (coneRatPoint q.1) q.2)

theorem measurableSet_offsetGoodMeasure : MeasurableSet {ν : Measure ℂ | OffsetGoodMeasure ν} := by
  have heq : {ν : Measure ℂ | OffsetGoodMeasure ν} =
      (⋂ n : ℕ, {ν : Measure ℂ | ν (closedBall 0 n) ≠ ∞}) ∩
        ⋂ q : (ℚ × ℚ) × ℚ, {ν : Measure ℂ | 0 < (q.2 : ℝ) → 0 < ν (ball (coneRatPoint q.1) q.2)} := by
    ext ν
    simp only [OffsetGoodMeasure, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [heq]
  refine (MeasurableSet.iInter fun n => ?_).inter (MeasurableSet.iInter fun q => ?_)
  · exact (Measure.measurable_coe measurableSet_closedBall) (measurableSet_singleton ∞).compl
  · by_cases hq : 0 < (q.2 : ℝ)
    · have h1 : {ν : Measure ℂ | 0 < (q.2 : ℝ) → 0 < ν (ball (coneRatPoint q.1) q.2)} =
          {ν : Measure ℂ | 0 < ν (ball (coneRatPoint q.1) q.2)} := by
        ext ν
        exact ⟨fun h => h hq, fun h _ => h⟩
      rw [h1]
      exact (Measure.measurable_coe measurableSet_ball) measurableSet_Ioi
    · have h1 : {ν : Measure ℂ | 0 < (q.2 : ℝ) → 0 < ν (ball (coneRatPoint q.1) q.2)} = univ := by
        ext ν
        exact ⟨fun _ => trivial, fun _ h => absurd h hq⟩
      rw [h1]
      exact MeasurableSet.univ

theorem OffsetGoodMeasure.measure_ne_top {ν : Measure ℂ} (hν : OffsetGoodMeasure ν) {K : Set ℂ}
    (hK : IsCompact K) : ν K ≠ ∞ := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_ge r
  exact ne_top_of_le_ne_top (hν.1 n) (measure_mono (hr.trans (closedBall_subset_closedBall hn)))

/-- The area measure of a curve parametrized by area, which is a reparametrization of a proper surjective
curve, is finite on bounded sets and positive on open disks. -/
theorem offsetGoodMeasure_of_areaParam {ηL η : C(ℝ, ℂ)} {μ : Measure ℂ} (hsurj : Function.Surjective ηL)
    (hprop : IsProperMap ηL) {φ : ℝ ≃o ℝ} (hφ : ∀ t, η t = ηL (φ t))
    (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) : OffsetGoodMeasure μ := by
  refine ⟨fun n => ?_, fun q hq => ?_⟩
  · have hc : IsCompact (ηL ⁻¹' closedBall (0 : ℂ) n) :=
      hprop.isCompact_preimage (isCompact_closedBall _ _)
    obtain ⟨T, hT⟩ := hc.isBounded.subset_closedBall 0
    have hsub : closedBall (0 : ℂ) n ⊆ η '' Icc (φ.symm (-|T|)) (φ.symm |T|) := by
      intro y hy
      obtain ⟨t, rfl⟩ := hsurj y
      have ht := hT hy
      rw [mem_closedBall, Real.dist_eq, sub_zero] at ht
      have ht' := abs_le.1 (ht.trans (le_abs_self T))
      refine ⟨φ.symm t, ⟨φ.symm.monotone ht'.1, φ.symm.monotone ht'.2⟩, ?_⟩
      rw [hφ, φ.apply_symm_apply]
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [harea _ _ (φ.symm.monotone (by linarith [abs_nonneg T]))]
    exact ENNReal.ofReal_ne_top
  · obtain ⟨t₀, ht₀⟩ := hsurj (coneRatPoint q.1)
    have hs₀ : η (φ.symm t₀) = coneRatPoint q.1 := by rw [hφ, φ.apply_symm_apply, ht₀]
    obtain ⟨ε, hε, hεη⟩ := Metric.continuousAt_iff.1 η.continuous.continuousAt (q.2 : ℝ) hq
    have hsub : η '' Icc (φ.symm t₀) (φ.symm t₀ + ε / 2) ⊆ ball (coneRatPoint q.1) q.2 := by
      rintro _ ⟨s, hs, rfl⟩
      rw [mem_ball, ← hs₀]
      refine hεη ?_
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [harea _ _ (by linarith)]
    exact ENNReal.ofReal_pos.2 (by linarith)

/-! ### Tilts by two bumps -/

/-- Pairs of rational disks admissible at scale `δ`: positive radii and disks inside `B_{min(1,δ)}(0) \ {0}`. -/
def IsOffsetDiskPair (δ : ℝ) (k : ((ℚ × ℚ) × ℚ) × ((ℚ × ℚ) × ℚ)) : Prop :=
  0 < (k.1.2 : ℝ) ∧ 0 < (k.2.2 : ℝ) ∧ coneRatDisk k.1 ⊆ ball 0 (min 1 δ) \ {0} ∧
    coneRatDisk k.2 ⊆ ball 0 (min 1 δ) \ {0}

/-- The smooth bump of a rational disk: equal to `1` on the concentric disk of half radius, positive exactly on
the open disk. -/
def diskBump (q : (ℚ × ℚ) × ℚ) (hq : 0 < (q.2 : ℝ)) : ContDiffBump (coneRatPoint q.1) :=
  ⟨(q.2 : ℝ) / 2, q.2, half_pos hq, half_lt_self hq⟩

theorem diskBump_eq_zero {q : (ℚ × ℚ) × ℚ} {hq : 0 < (q.2 : ℝ)} {w : ℂ} (hw : w ∉ coneRatDisk q) :
    diskBump q hq w = 0 := by
  by_contra h
  have hs : w ∈ Function.support (diskBump q hq) := Function.mem_support.2 h
  rw [ContDiffBump.support_eq] at hs
  exact hw (ball_subset_closedBall hs)

theorem diskBump_pos {q : (ℚ × ℚ) × ℚ} {hq : 0 < (q.2 : ℝ)} {w : ℂ} (hw : w ∈ ball (coneRatPoint q.1) q.2) :
    0 < diskBump q hq w := by
  have hs : w ∈ Function.support (diskBump q hq) := by
    rw [ContDiffBump.support_eq]
    exact hw
  exact lt_of_le_of_ne (diskBump q hq).nonneg (Ne.symm hs)

/-- The tilt exponent `x₀ f₋ + x₁ f₊`. -/
def tiltFun (δ : ℝ) (k : {k // IsOffsetDiskPair δ k}) (x : Fin 2 → ℝ) (z : ℂ) : ℝ :=
  x 0 * diskBump k.1.1 k.2.1 z + x 1 * diskBump k.1.2 k.2.2.1 z

/-- The area measure tilted by `exp(γ (x₀ f₋ + x₁ f₊))`. -/
def tiltMeasure (γ δ : ℝ) (k : {k // IsOffsetDiskPair δ k}) (x : Fin 2 → ℝ) (ν : Measure ℂ) : Measure ℂ :=
  ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z))

/-- The tilt on curve-measure pairs. -/
def offsetTilt (γ δ : ℝ) (k : {k // IsOffsetDiskPair δ k}) (x : Fin 2 → ℝ)
    (z : C(ℝ, ℂ) × Measure ℂ) : C(ℝ, ℂ) × Measure ℂ :=
  (z.1, tiltMeasure γ δ k x z.2)

section Tilt

variable {γ δ : ℝ} (k : {k // IsOffsetDiskPair δ k})

theorem tiltFun_eq_zero {x : Fin 2 → ℝ} {w : ℂ} (h1 : w ∉ coneRatDisk k.1.1) (h2 : w ∉ coneRatDisk k.1.2) :
    tiltFun δ k x w = 0 := by
  rw [tiltFun, diskBump_eq_zero h1, diskBump_eq_zero h2, mul_zero, mul_zero, add_zero]

theorem abs_tiltFun_le (x : Fin 2 → ℝ) (w : ℂ) : |tiltFun δ k x w| ≤ |x 0| + |x 1| := by
  rw [tiltFun]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (diskBump k.1.1 k.2.1).nonneg]
    exact mul_le_of_le_one_right (abs_nonneg _) (diskBump k.1.1 k.2.1).le_one
  · rw [abs_mul, abs_of_nonneg (diskBump k.1.2 k.2.2.1).nonneg]
    exact mul_le_of_le_one_right (abs_nonneg _) (diskBump k.1.2 k.2.2.1).le_one

theorem continuous_tiltFun (x : Fin 2 → ℝ) : Continuous (tiltFun δ k x) :=
  (continuous_const.mul (diskBump k.1.1 k.2.1).continuous).add
    (continuous_const.mul (diskBump k.1.2 k.2.2.1).continuous)

theorem contDiff_tiltFun (x : Fin 2 → ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tiltFun δ k x) :=
  (contDiff_const.mul (diskBump k.1.1 k.2.1).contDiff).add
    (contDiff_const.mul (diskBump k.1.2 k.2.2.1).contDiff)

theorem tsupport_tiltFun_subset (x : Fin 2 → ℝ) : tsupport (tiltFun δ k x) ⊆ ball (0 : ℂ) 1 \ {0} := by
  have hC : IsClosed (coneRatDisk k.1.1 ∪ coneRatDisk k.1.2) := isClosed_closedBall.union isClosed_closedBall
  refine (closure_minimal (fun w hw => ?_) hC).trans ?_
  · by_contra h
    rw [mem_union, not_or] at h
    exact hw (tiltFun_eq_zero k h.1 h.2)
  · rintro w (hw | hw)
    · obtain ⟨h1, h2⟩ := k.2.2.2.1 hw
      exact ⟨ball_subset_ball (min_le_left 1 δ) h1, h2⟩
    · obtain ⟨h1, h2⟩ := k.2.2.2.2 hw
      exact ⟨ball_subset_ball (min_le_left 1 δ) h1, h2⟩

theorem measurable_tiltDensity (x : Fin 2 → ℝ) :
    Measurable fun z => ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) :=
  (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (continuous_tiltFun k x)))).measurable

theorem tiltDensity_le (x : Fin 2 → ℝ) (w : ℂ) :
    ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) ≤
      ENNReal.ofReal (Real.exp (|γ| * (|x 0| + |x 1|))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ((le_abs_self _).trans ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_tiltFun_le k x w) (abs_nonneg γ)

theorem le_tiltDensity (x : Fin 2 → ℝ) (w : ℂ) :
    ENNReal.ofReal (Real.exp (-(|γ| * (|x 0| + |x 1|)))) ≤
      ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h := neg_abs_le (γ * tiltFun δ k x w)
  rw [abs_mul] at h
  have h' := mul_le_mul_of_nonneg_left (abs_tiltFun_le k x w) (abs_nonneg γ)
  linarith

/-- For every measure `ν` and measurable `U`, the tilted mass `∫_U exp(γ (x₀ f₋ + x₁ f₊)) dν` is continuous in
`x` (with values in `[0, ∞]`). -/
theorem continuous_lintegral_tilt (ν : Measure ℂ) {U : Set ℂ} (hU : MeasurableSet U) :
    Continuous fun x : Fin 2 → ℝ => ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν := by
  set K : Set ℂ := coneRatDisk k.1.1 ∪ coneRatDisk k.1.2 with hKdef
  have hKm : MeasurableSet K := (isClosed_closedBall.union isClosed_closedBall).measurableSet
  have hsplit : ∀ x : Fin 2 → ℝ, ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν =
      ∫⁻ z in U ∩ K, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν + ν (U \ K) := by
    intro x
    rw [← lintegral_inter_add_sdiff _ U hKm]
    congr 1
    rw [← setLIntegral_one]
    refine lintegral_congr_ae ((ae_restrict_iff' (hU.diff hKm)).2 (ae_of_all _ fun w hw => ?_))
    have hw2 : w ∉ K := hw.2
    rw [hKdef, mem_union, not_or] at hw2
    show ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) = 1
    rw [tiltFun_eq_zero k hw2.1 hw2.2]
    simp
  have heq : (fun x : Fin 2 → ℝ => ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν) =
      fun x => ∫⁻ z in U ∩ K, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν + ν (U \ K) :=
    funext hsplit
  rw [heq]
  refine Continuous.add ?_ continuous_const
  by_cases hfin : ν (U ∩ K) = ∞
  · have htop : ∀ x : Fin 2 → ℝ, ∫⁻ z in U ∩ K, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν = ∞ := by
      intro x
      refine eq_top_iff.2 ?_
      calc ∞ = ENNReal.ofReal (Real.exp (-(|γ| * (|x 0| + |x 1|)))) * ν (U ∩ K) := by
            rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne']
        _ = ∫⁻ _ in U ∩ K, ENNReal.ofReal (Real.exp (-(|γ| * (|x 0| + |x 1|)))) ∂ν :=
            (setLIntegral_const _ _).symm
        _ ≤ _ := lintegral_mono fun w => le_tiltDensity k x w
    have hc : (fun x : Fin 2 → ℝ => ∫⁻ z in U ∩ K, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν) =
        fun _ => ∞ := funext htop
    rw [hc]
    exact continuous_const
  · refine continuous_iff_continuousAt.2 fun x₀ => ?_
    have hbd : ∀ᶠ x in 𝓝 x₀, ∀ᵐ w ∂(ν.restrict (U ∩ K)),
        ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) ≤
          ENNReal.ofReal (Real.exp (|γ| * (2 * (‖x₀‖ + 1)))) := by
      filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
      refine ae_of_all _ fun w => (tiltDensity_le k x w).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (abs_nonneg γ))))
      have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have h1 := norm_sub_norm_le x x₀
        rw [mem_ball, dist_eq_norm] at hx
        linarith
      have h0 : |x 0| ≤ ‖x‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm x 0
      have h1 : |x 1| ≤ ‖x‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm x 1
      linarith
    exact tendsto_lintegral_filter_of_dominated_convergence
      (fun _ => ENNReal.ofReal (Real.exp (|γ| * (2 * (‖x₀‖ + 1)))))
      (Eventually.of_forall fun x => measurable_tiltDensity k x) hbd
      (by rw [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      (ae_of_all _ fun w => ((ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (((continuous_apply 0).mul continuous_const).add
          ((continuous_apply 1).mul continuous_const))))).tendsto x₀))

theorem measurable_tiltMeasure :
    Measurable fun p : (Fin 2 → ℝ) × Measure ℂ => tiltMeasure γ δ k p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun U hU => ?_
  have hu : Measurable (Function.uncurry fun (x : Fin 2 → ℝ) (ν : Measure ℂ) =>
      ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν) :=
    measurable_uncurry_of_continuous_of_measurable (fun ν => continuous_lintegral_tilt k ν hU)
      (fun x => (Measure.measurable_lintegral (measurable_tiltDensity k x)).comp
        (measurable_restrict_of_measurableSet hU))
  have heq : (fun p : (Fin 2 → ℝ) × Measure ℂ => tiltMeasure γ δ k p.1 p.2 U) =
      Function.uncurry fun (x : Fin 2 → ℝ) (ν : Measure ℂ) =>
        ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x z)) ∂ν := by
    funext p
    exact withDensity_apply _ hU
  rw [heq]
  exact hu

theorem measurable_offsetTilt :
    Measurable fun p : (Fin 2 → ℝ) × (C(ℝ, ℂ) × Measure ℂ) => offsetTilt γ δ k p.1 p.2 := by
  have hg : Measurable fun p : (Fin 2 → ℝ) × (C(ℝ, ℂ) × Measure ℂ) => (p.1, p.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have h2 := (measurable_tiltMeasure (γ := γ) k).comp hg
  simp only [Function.comp_def] at h2
  have h1 : Measurable fun p : (Fin 2 → ℝ) × (C(ℝ, ℂ) × Measure ℂ) => p.2.1 :=
    measurable_fst.comp measurable_snd
  exact h1.prodMk h2

theorem tiltMeasure_ne_top {ν : Measure ℂ} (hν : OffsetGoodMeasure ν) (x : Fin 2 → ℝ) {K : Set ℂ}
    (hK : IsCompact K) : tiltMeasure γ δ k x ν K ≠ ∞ := by
  rw [tiltMeasure, withDensity_apply _ hK.isClosed.measurableSet]
  have hle : ∫⁻ w in K, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) ∂ν ≤
      ENNReal.ofReal (Real.exp (|γ| * (|x 0| + |x 1|))) * ν K :=
    calc ∫⁻ w in K, ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) ∂ν
        ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp (|γ| * (|x 0| + |x 1|))) ∂ν :=
          lintegral_mono fun w => tiltDensity_le k x w
      _ = _ := setLIntegral_const K _
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hν.measure_ne_top hK)) hle

theorem tiltMeasure_apply_of_notMem_right {ν : Measure ℂ} (x : Fin 2 → ℝ) {K : Set ℂ}
    (hK : MeasurableSet K) (hdis : ∀ w ∈ K, w ∉ coneRatDisk k.1.2) :
    tiltMeasure γ δ k x ν K =
      ∫⁻ w, ENNReal.ofReal (Real.exp (γ * (x 0 * diskBump k.1.1 k.2.1 w))) ∂(ν.restrict K) := by
  rw [tiltMeasure, withDensity_apply _ hK]
  refine lintegral_congr_ae ((ae_restrict_iff' hK).2 (ae_of_all _ fun w hw => ?_))
  show ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) =
    ENNReal.ofReal (Real.exp (γ * (x 0 * diskBump k.1.1 k.2.1 w)))
  rw [tiltFun, diskBump_eq_zero (hdis w hw), mul_zero, add_zero]

theorem tiltMeasure_apply_of_notMem_left {ν : Measure ℂ} (x : Fin 2 → ℝ) {K : Set ℂ}
    (hK : MeasurableSet K) (hdis : ∀ w ∈ K, w ∉ coneRatDisk k.1.1) :
    tiltMeasure γ δ k x ν K =
      ∫⁻ w, ENNReal.ofReal (Real.exp (γ * (x 1 * diskBump k.1.2 k.2.2.1 w))) ∂(ν.restrict K) := by
  rw [tiltMeasure, withDensity_apply _ hK]
  refine lintegral_congr_ae ((ae_restrict_iff' hK).2 (ae_of_all _ fun w hw => ?_))
  show ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) =
    ENNReal.ofReal (Real.exp (γ * (x 1 * diskBump k.1.2 k.2.2.1 w)))
  rw [tiltFun, diskBump_eq_zero (hdis w hw), mul_zero, zero_add]

end Tilt

/-! ### The offsets as a measurable function of the curve and the area measure -/

/-- The outer data and the two offsets, with the masses of the two curve segments computed as cover masses. -/
def offsetData (a δ M : ℝ) (z : C(ℝ, ℂ) × Measure ℂ) : (C(ℝ, ℂ) × Measure ℂ) × (Fin 2 → ℝ) :=
  (annulusOuterData z.1 z.2 δ M,
    ![-(coverMass (Icc (-a) 0) z.1 z.2).toReal, (coverMass (Icc 0 a) z.1 z.2).toReal])

theorem measurable_offsetData (a δ M : ℝ) : Measurable (offsetData a δ M) := by
  refine (measurable_fst.prodMk ((measurable_restrict_of_measurableSet
    (measurableSet_offsetOuterAnnulus δ M)).comp measurable_snd)).prodMk ?_
  refine Measurable.of_eval fun i => ?_
  fin_cases i
  · exact (ENNReal.measurable_toReal.comp (measurable_coverMass isCompact_Icc)).neg
  · exact ENNReal.measurable_toReal.comp (measurable_coverMass isCompact_Icc)

theorem offsetData_fst_offsetTilt {γ δ a M : ℝ} (k : {k // IsOffsetDiskPair δ k}) (x : Fin 2 → ℝ)
    (z : C(ℝ, ℂ) × Measure ℂ) : (offsetData a δ M (offsetTilt γ δ k x z)).1 = (offsetData a δ M z).1 := by
  have hA := measurableSet_offsetOuterAnnulus δ M
  have h1 : (fun w => ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w))) =ᵐ[z.2.restrict (offsetOuterAnnulus δ M)]
      1 := by
    refine (ae_restrict_iff' hA).2 (ae_of_all _ fun w hw => ?_)
    have hnot : ∀ q : (ℚ × ℚ) × ℚ, coneRatDisk q ⊆ ball 0 (min 1 δ) \ {0} → w ∉ coneRatDisk q := by
      intro q hq hwq
      have h := (hq hwq).1
      rw [mem_ball] at h
      exact hw.2 (by rw [mem_closedBall]; linarith [min_le_right 1 δ])
    show ENNReal.ofReal (Real.exp (γ * tiltFun δ k x w)) = 1
    rw [tiltFun_eq_zero k (hnot _ k.2.2.2.1) (hnot _ k.2.2.2.2)]
    simp
  show annulusOuterData z.1 (tiltMeasure γ δ k x z.2) δ M = annulusOuterData z.1 z.2 δ M
  rw [annulusOuterData, annulusOuterData, tiltMeasure, restrict_withDensity hA, withDensity_congr_ae h1,
    withDensity_one]

/-- **The offsets move along strictly monotone `C¹` curves under the tilts.** For a measure `κ` finite, `f`
continuous with values in `[0, 1]`, `γ > 0` and `κ{f > 0} > 0`, the map `t ↦ σ ∫ exp(γ t f) dκ` (`σ ≠ 0`) is
measurable and pulls back Lebesgue-null sets to Lebesgue-null sets. -/
theorem tiltMass_null_preimage {κ : Measure ℂ} [IsFiniteMeasure κ] {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) {γ : ℝ} (hγ : 0 < γ) (hpos : 0 < κ {w | 0 < f w})
    {σ : ℝ} (hσ : σ ≠ 0) :
    Measurable (fun t : ℝ => σ * (∫⁻ w, ENNReal.ofReal (Real.exp (γ * (t * f w))) ∂κ).toReal) ∧
      ∀ N : Set ℝ, volume N = 0 →
        volume ((fun t : ℝ => σ * (∫⁻ w, ENNReal.ofReal (Real.exp (γ * (t * f w))) ∂κ).toReal) ⁻¹' N) = 0 := by
  have hFc : ∀ t : ℝ, Continuous fun w => Real.exp (γ * (t * f w)) := fun t =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul hf))
  have hbound : ∀ (t : ℝ) (w : ℂ), Real.exp (γ * (t * f w)) ≤ Real.exp (γ * |t|) := by
    intro t w
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hγ.le)
    calc t * f w ≤ |t| * f w := mul_le_mul_of_nonneg_right (le_abs_self t) (hf0 w)
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hf1 w) (abs_nonneg t)
      _ = |t| := mul_one _
  have hint : ∀ t : ℝ, Integrable (fun w => Real.exp (γ * (t * f w))) κ := fun t =>
    Integrable.mono' (integrable_const (Real.exp (γ * |t|))) (hFc t).aestronglyMeasurable
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound t w)
  have hderiv : ∀ t : ℝ, Integrable (fun w => Real.exp (γ * (t * f w)) * (γ * f w)) κ ∧
      HasDerivAt (fun s => ∫ w, Real.exp (γ * (s * f w)) ∂κ)
        (∫ w, Real.exp (γ * (t * f w)) * (γ * f w) ∂κ) t := by
    intro t
    have hb : ∀ᵐ w ∂κ, ∀ s ∈ ball t 1,
        ‖Real.exp (γ * (s * f w)) * (γ * f w)‖ ≤ Real.exp (γ * (|t| + 1)) * γ := by
      refine ae_of_all _ fun w s hs => ?_
      have hs' : |s| ≤ |t| + 1 := by
        rw [mem_ball, Real.dist_eq] at hs
        have := abs_sub_abs_le_abs_sub s t
        linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (mul_nonneg hγ.le (hf0 w))]
      refine mul_le_mul ((hbound s w).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs' hγ.le))) ?_
        (mul_nonneg hγ.le (hf0 w)) (Real.exp_pos _).le
      calc γ * f w ≤ γ * 1 := mul_le_mul_of_nonneg_left (hf1 w) hγ.le
        _ = γ := mul_one γ
    have hd : ∀ᵐ w ∂κ, ∀ s ∈ ball t 1, HasDerivAt (fun s => Real.exp (γ * (s * f w)))
        (Real.exp (γ * (s * f w)) * (γ * f w)) s :=
      ae_of_all _ fun w s _ => ((hasDerivAt_mul_const (f w)).const_mul γ).exp
    exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t zero_lt_one)
      (Eventually.of_forall fun s => (hFc s).aestronglyMeasurable) (hint t)
      ((hFc t).mul (continuous_const.mul hf)).aestronglyMeasurable hb (integrable_const _) hd
  have hpos' : ∀ t : ℝ, 0 < ∫ w, Real.exp (γ * (t * f w)) * (γ * f w) ∂κ := by
    intro t
    have hnn : 0 ≤ fun w => Real.exp (γ * (t * f w)) * (γ * f w) := fun w =>
      mul_nonneg (Real.exp_pos _).le (mul_nonneg hγ.le (hf0 w))
    rw [integral_pos_iff_support_of_nonneg hnn (hderiv t).1]
    refine lt_of_lt_of_le hpos (measure_mono fun w hw => ?_)
    exact mul_ne_zero (Real.exp_pos _).ne' (mul_ne_zero hγ.ne' (ne_of_gt hw))
  have hsm : StrictMono fun s => ∫ w, Real.exp (γ * (s * f w)) ∂κ :=
    strictMono_of_deriv_pos fun t => by rw [(hderiv t).2.deriv]; exact hpos' t
  have hmeq : (fun t : ℝ => σ * (∫⁻ w, ENNReal.ofReal (Real.exp (γ * (t * f w))) ∂κ).toReal) =
      fun t => σ * ∫ w, Real.exp (γ * (t * f w)) ∂κ := by
    funext t
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => (Real.exp_pos _).le)
      (hFc t).aestronglyMeasurable]
  rw [hmeq]
  have hd' : ∀ t : ℝ, HasDerivAt (fun t => σ * ∫ w, Real.exp (γ * (t * f w)) ∂κ)
      (σ * ∫ w, Real.exp (γ * (t * f w)) * (γ * f w) ∂κ) t := fun t => (hderiv t).2.const_mul σ
  refine ⟨(continuous_iff_continuousAt.2 fun t => (hd' t).continuousAt).measurable, fun N hN => ?_⟩
  exact volume_preimage_eq_zero_of_hasDerivAt hd' (fun t => mul_ne_zero hσ (hpos' t).ne')
    (fun t₁ t₂ h => hsm.injective (mul_left_cancel₀ hσ h)) hN

/-- **The offsets of the tilts pull back null sets to null sets**, on the curve event and for a measure finite on
bounded sets and charging every rational disk. -/
theorem volume_preimage_offsets_tilt {γ δ a : ℝ} (hγ : 0 < γ) (k : {k // IsOffsetDiskPair δ k})
    {z : C(ℝ, ℂ) × Measure ℂ} (hz : OffsetGoodMeasure z.2) (hE : z.1 ∈ offsetCurveEvent a k.1) (M : ℝ)
    {N : Set (Fin 2 → ℝ)} (hN : volume N = 0) :
    volume ((fun x => (offsetData a δ M (offsetTilt γ δ k x z)).2) ⁻¹' N) = 0 := by
  obtain ⟨e, ν⟩ := z
  obtain ⟨hmapsm, hmapsp, hinm, hinp⟩ := hE
  have hKm : IsCompact (e '' Icc (-a) 0) := isCompact_Icc.image e.continuous
  have hKp : IsCompact (e '' Icc 0 a) := isCompact_Icc.image e.continuous
  have hdism : ∀ w ∈ e '' Icc (-a) 0, w ∉ coneRatDisk k.1.2 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hmapsm ht
  have hdisp : ∀ w ∈ e '' Icc 0 a, w ∉ coneRatDisk k.1.1 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hmapsp ht
  have hfin : ∀ (x : Fin 2 → ℝ) (K : Set ℂ), IsCompact K →
      ∃ R > 0, tiltMeasure γ δ k x ν (cthickening R K) ≠ ∞ :=
    fun x K hK => ⟨1, one_pos, tiltMeasure_ne_top k hz x hK.cthickening⟩
  have hfun : (fun x => (offsetData a δ M (offsetTilt γ δ k x (e, ν))).2) = fun x =>
      ![(-1) * (∫⁻ w, ENNReal.ofReal (Real.exp (γ * (x 0 * diskBump k.1.1 k.2.1 w)))
          ∂(ν.restrict (e '' Icc (-a) 0))).toReal,
        1 * (∫⁻ w, ENNReal.ofReal (Real.exp (γ * (x 1 * diskBump k.1.2 k.2.2.1 w)))
          ∂(ν.restrict (e '' Icc 0 a))).toReal] := by
    funext x
    show ![-(coverMass (Icc (-a) 0) e (tiltMeasure γ δ k x ν)).toReal,
      (coverMass (Icc 0 a) e (tiltMeasure γ δ k x ν)).toReal] = _
    rw [coverMass_eq isCompact_Icc e (hfin x _ hKm), coverMass_eq isCompact_Icc e (hfin x _ hKp),
      tiltMeasure_apply_of_notMem_right k x hKm.isClosed.measurableSet hdism,
      tiltMeasure_apply_of_notMem_left k x hKp.isClosed.measurableSet hdisp, neg_one_mul, one_mul]
  rw [hfun]
  have : IsFiniteMeasure (ν.restrict (e '' Icc (-a) 0)) := isFiniteMeasure_restrict.2 (hz.measure_ne_top hKm)
  have : IsFiniteMeasure (ν.restrict (e '' Icc 0 a)) := isFiniteMeasure_restrict.2 (hz.measure_ne_top hKp)
  have hposm : 0 < (ν.restrict (e '' Icc (-a) 0)) {w | 0 < diskBump k.1.1 k.2.1 w} := by
    rw [Measure.restrict_apply' hKm.isClosed.measurableSet]
    exact lt_of_lt_of_le (hz.2 k.1.1 k.2.1)
      (measure_mono fun w hw => ⟨diskBump_pos hw, hinm (ball_subset_closedBall hw)⟩)
  have hposp : 0 < (ν.restrict (e '' Icc 0 a)) {w | 0 < diskBump k.1.2 k.2.2.1 w} := by
    rw [Measure.restrict_apply' hKp.isClosed.measurableSet]
    exact lt_of_lt_of_le (hz.2 k.1.2 k.2.2.1)
      (measure_mono fun w hw => ⟨diskBump_pos hw, hinp (ball_subset_closedBall hw)⟩)
  obtain ⟨hm₀, hn₀⟩ := tiltMass_null_preimage (κ := ν.restrict (e '' Icc (-a) 0))
    (diskBump k.1.1 k.2.1).continuous (fun _ => (diskBump k.1.1 k.2.1).nonneg)
    (fun _ => (diskBump k.1.1 k.2.1).le_one) hγ hposm (σ := -1) (by norm_num)
  obtain ⟨hm₁, hn₁⟩ := tiltMass_null_preimage (κ := ν.restrict (e '' Icc 0 a))
    (diskBump k.1.2 k.2.2.1).continuous (fun _ => (diskBump k.1.2 k.2.2.1).nonneg)
    (fun _ => (diskBump k.1.2 k.2.2.1).le_one) hγ hposp (σ := 1) one_ne_zero
  exact volume_preimage_eq_zero_of_fin_two hm₀ hm₁ hn₀ hn₁ hN

/-! ### The offset density -/

/-- **The offset density for one cone**, from the tilt input, the independence of the curve, the measurability
of the area measure, and the almost sure properties of the curve and the area measure. -/
theorem offsetDensity_of_bumpTilt {γ : ℝ} (hT : ConeAreaBumpTilt γ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ : β = 0 ∨ β = γ)
    {X : Ω → Field} {B B' : ℝ≥0 → Ω → ℝ} {e : Ω → C(ℝ, ℂ)}
    (hX : LQGMetric.IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    (he : Measurable e) (hie : IndepFun e (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P)
    (hμ : AEMeasurable (quantumConeArea γ β X B B') P)
    (hgood : ∀ᵐ ω ∂P, OffsetGoodMeasure (quantumConeArea γ β X B B' ω))
    (hcurve : ∀ᵐ ω ∂P, Function.Surjective (e ω) ∧ Tendsto (e ω) (cocompact ℝ) (cocompact ℂ) ∧
      e ω 0 = 0 ∧ ∀ s t : ℝ, s ≤ t → volume (e ω '' Icc s t) = ENNReal.ofReal (t - s))
    {a δ M : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    AEMeasurable (fun ω => quantumTimeOffsets (e ω) (quantumConeArea γ β X B B' ω) a) P ∧
      P.map (fun ω => (annulusOuterData (e ω) (quantumConeArea γ β X B B' ω) δ M,
          quantumTimeOffsets (e ω) (quantumConeArea γ β X B B' ω) a)) ≪
        (P.map fun ω => annulusOuterData (e ω) (quantumConeArea γ β X B B' ω) δ M).prod volume := by
  have hZ : AEMeasurable (fun ω => (e ω, quantumConeArea γ β X B B' ω)) P := he.aemeasurable.prodMk hμ
  have hG := measurable_offsetData a δ M
  have hae : ∀ᵐ ω ∂P, offsetData a δ M (e ω, quantumConeArea γ β X B B' ω) =
      (annulusOuterData (e ω) (quantumConeArea γ β X B B' ω) δ M,
        quantumTimeOffsets (e ω) (quantumConeArea γ β X B B' ω) a) := by
    filter_upwards [hgood] with ω hω
    have h1 := coverMass_eq isCompact_Icc (e ω) (J := Icc (-a) 0)
      ⟨1, one_pos, hω.measure_ne_top (isCompact_Icc.image (e ω).continuous).cthickening⟩
    have h2 := coverMass_eq isCompact_Icc (e ω) (J := Icc 0 a)
      ⟨1, one_pos, hω.measure_ne_top (isCompact_Icc.image (e ω).continuous).cthickening⟩
    simp only [offsetData, quantumTimeOffsets, h1, h2]
  refine ⟨((measurable_snd.comp hG).comp_aemeasurable hZ).congr ?_, ?_⟩
  · filter_upwards [hae] with ω hω
    show (offsetData a δ M (e ω, quantumConeArea γ β X B B' ω)).2 = _
    rw [hω]
  have hmapG : P.map (fun ω => (annulusOuterData (e ω) (quantumConeArea γ β X B B' ω) δ M,
      quantumTimeOffsets (e ω) (quantumConeArea γ β X B B' ω) a)) =
      (P.map fun ω => (e ω, quantumConeArea γ β X B B' ω)).map (offsetData a δ M) := by
    rw [AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hZ]
    exact Measure.map_congr (by filter_upwards [hae] with ω hω using hω.symm)
  have hmapO : P.map (fun ω => annulusOuterData (e ω) (quantumConeArea γ β X B B' ω) δ M) =
      (P.map fun ω => (e ω, quantumConeArea γ β X B B' ω)).map fun z => (offsetData a δ M z).1 := by
    rw [AEMeasurable.map_map_of_aemeasurable hG.fst.aemeasurable hZ]
    rfl
  rw [hmapG, hmapO]
  have hcovm : MeasurableSet {z : C(ℝ, ℂ) × Measure ℂ |
      ∃ k : {k // IsOffsetDiskPair δ k}, z ∈ Prod.fst ⁻¹' offsetCurveEvent a k.1} := by
    have h1 : {z : C(ℝ, ℂ) × Measure ℂ |
        ∃ k : {k // IsOffsetDiskPair δ k}, z ∈ Prod.fst ⁻¹' offsetCurveEvent a k.1} =
        ⋃ k : {k // IsOffsetDiskPair δ k}, Prod.fst ⁻¹' offsetCurveEvent a k.1 := by
      ext z
      exact mem_iUnion.symm
    rw [h1]
    exact MeasurableSet.iUnion fun k => measurable_fst (measurableSet_offsetCurveEvent a k.1 k.2.1 k.2.2.1)
  refine absolutelyContinuous_map_prod_volume_of_tilts hG
    (fun k : {k // IsOffsetDiskPair δ k} => Prod.fst ⁻¹' offsetCurveEvent a k.1)
    (fun k => measurable_fst (measurableSet_offsetCurveEvent a k.1 k.2.1 k.2.2.1)) ?_
    (fun k x => offsetTilt γ δ k x) (fun k => measurable_offsetTilt k) (fun _ _ _ => Iff.rfl) ?_
    (fun k x z _ => offsetData_fst_offsetTilt k x z) ?_
  · refine (ae_map_iff hZ hcovm).2 ?_
    filter_upwards [hcurve] with ω hω
    obtain ⟨hsurj, hprop, h0, hvol⟩ := hω
    obtain ⟨k, hk1, hk2, hk3, hk4, hev⟩ := exists_offsetDisks hsurj
      (isProperMap_iff_tendsto_cocompact.2 ⟨(e ω).continuous, hprop⟩) h0 hvol ha (lt_min one_pos hδ)
    exact ⟨⟨k, hk1, hk2, hk3, hk4⟩, hev⟩
  · intro k x
    have hTx : Measurable (offsetTilt γ δ k x) :=
      (measurable_offsetTilt k).comp (measurable_const.prodMk measurable_id)
    rw [AEMeasurable.map_map_of_aemeasurable hTx.aemeasurable hZ]
    exact hT P β X B B' e hγ hβ hX hB hB' hind he hie (tiltFun δ k x) (contDiff_tiltFun k x)
      (tsupport_tiltFun_subset k x)
  · intro k
    have hgood' : ∀ᵐ z ∂(P.map fun ω => (e ω, quantumConeArea γ β X B B' ω)), OffsetGoodMeasure z.2 :=
      (ae_map_iff hZ (measurable_snd measurableSet_offsetGoodMeasure)).2 hgood
    filter_upwards [hgood'] with z hz hE N hN
    exact volume_preimage_offsets_tilt hγ.1 k hz hE M hN

/-- **`ConeOffsetDensity` from the tilt input** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Lemma 3.3): for every mating-of-trees coupling, given the outer data
`(ηL, μ|{δ < |z| < M})`, the two offsets `(-μ(ηL([-a, 0])), μ(ηL([0, a])))` of the `γ`-quantum cone and of the
`0`-quantum cone have a joint Lebesgue density. -/
theorem coneOffsetDensity_of_bumpTilt (γ : ℝ) (hT : ConeAreaBumpTilt γ) : ConeOffsetDensity γ := by
  intro Ω _ P X X₀ _ B B' B₀ B₀' _ ηL _ _ _ D hγ a δ M ha hδ _
  have hP := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hind := Sec1.indepFun_igCurve_cone D
  have hψ : Measurable fun p : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
      (p.1, p.2.1, p.2.2.1) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hψ₀ : Measurable fun p : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
      (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        measurable_snd)))).prodMk (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))))
  have hie : IndepFun ηL (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P := by
    have h := hind.comp measurable_id hψ
    exact h
  have hie₀ : IndepFun ηL (fun ω => (X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))) P := by
    have h := hind.comp measurable_id hψ₀
    exact h
  have hAγ : AEMeasurable (quantumConeArea γ γ X B B') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMSCase.aemeasurable_coneField D hγ)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ)
  have hA0 : AEMeasurable (quantumConeArea γ 0 X₀ B₀ B₀') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMS4.aemeasurable_prop48ZeroConeField D)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ)
  have hgoodγ : ∀ᵐ ω ∂P, OffsetGoodMeasure (quantumConeArea γ γ X B B' ω) := by
    filter_upwards [D.spaceFilling, D.areaParam,
      MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ] with ω hsf hap hex
    obtain ⟨⟨φ, -, hφ⟩, harea⟩ := hap
    exact offsetGoodMeasure_of_areaParam hsf.1
      (isProperMap_iff_tendsto_cocompact.2 ⟨(ηL ω).continuous, hsf.2.1⟩) hφ
      (harea _ (MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex))
  have hgood0 : ∀ᵐ ω ∂P, OffsetGoodMeasure (quantumConeArea γ 0 X₀ B₀ B₀' ω) := by
    filter_upwards [D.spaceFilling, D.areaParam₀,
      MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ] with ω hsf hap hex
    obtain ⟨⟨φ, -, hφ⟩, harea⟩ := hap
    exact offsetGoodMeasure_of_areaParam hsf.1
      (isProperMap_iff_tendsto_cocompact.2 ⟨(ηL ω).continuous, hsf.2.1⟩) hφ
      (harea _ (MatedCRTHarmonic.CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex))
  exact ⟨offsetDensity_of_bumpTilt hT hγ (Or.inr rfl) D.gff D.bm_B D.bm_B' D.indep_cone hηL hie hAγ
      hgoodγ D.spaceFilling ha hδ,
    offsetDensity_of_bumpTilt hT hγ (Or.inl rfl) D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀ hηL hie₀ hA0
      hgood0 D.spaceFilling ha hδ⟩

end MatedCRT
