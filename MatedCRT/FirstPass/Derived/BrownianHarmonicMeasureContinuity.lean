import MatedCRT.FirstPass.Derived.BrownianExitPointRestart
import MatedCRT.FirstPass.Derived.BrownianDiscPoissonExit

/-!
# Continuity of Euclidean harmonic measure in the base point

Let `U` be a bounded open set containing the closed disc `closedBall c ρ`. For base points `y`,
`y'` in the open disc `B_ρ(c)`, the harmonic measures of `U` seen from `y` and from `y'` (the
exit distributions of planar Brownian motion) differ in total variation by at most the circle
average of `|P(c, y, ·) - P(c, y', ·)|`, where `P` is the Poisson kernel of the disc:
for every Borel set `A`,
`|P_y(B_{τ_U} ∈ A) - P_{y'}(B_{τ_U} ∈ A)| ≤ M(|P(c, y, ·) - P(c, y', ·)|; c, ρ)`.

The proof restarts Brownian motion at its exit from the disc (strong Markov property) and uses
that the exit point of the disc from `y` has the Poisson-kernel harmonic measure of the disc.
This is the continuity of harmonic measure in the base point used in the proof of Lemma 3.14 of
the Gwynne-Miller-Sheffield invariance principle.

On a compact set `K ⊆ U` the modulus is uniform in the base point
(`exists_forall_abs_planarBrownian_exitPoint_sub_le`), also for the Lévy–Prokhorov distance of the
exit laws (`exists_forall_levyProkhorovDist_planarBrownian_exitLaw_le`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6

namespace MatedCRT

/-- A path started in the disc `B_ρ(c)`, whose exit point from the disc lies on the circle
`∂B_ρ(c)`, leaves the disc strictly before it leaves any open set `U ⊇ closedBall c ρ`. -/
theorem exitTime_ball_lt_exitTime {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {ρ : ℝ}
    (hsub : closedBall c ρ ⊆ U) (ω : ContinuousPath ℂ) (h0 : ω 0 ∈ ball c ρ)
    (hfin : ContinuousPath.exitTime (ball c ρ) ω ≠ ⊤)
    (hsph : ω ((ContinuousPath.exitTime (ball c ρ) ω).toNNReal) ∈ sphere c ρ) :
    ContinuousPath.exitTime (ball c ρ) ω < ContinuousPath.exitTime U ω := by
  refine lt_of_not_ge fun hle => ?_
  have hUfin : ContinuousPath.exitTime U ω ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU ω
    (hsub (ball_subset_closedBall h0)) hUfin
  rw [hU.frontier_eq] at hfr
  apply hfr.2
  rcases hle.lt_or_eq with hlt | heq
  · apply hsub
    apply ball_subset_closedBall
    apply ContinuousPath.mem_of_lt_exitTime
    rwa [ENNReal.coe_toNNReal hUfin]
  · rw [heq]
    exact hsub (sphere_subset_closedBall hsph)

/-- **Harmonic measure of `U` through the disc.** For a bounded open `U ⊇ closedBall c ρ` and
`y ∈ B_ρ(c)`, the probability that Brownian motion from `y` leaves `U` in `A` is the average,
against the harmonic measure of the disc seen from `y`, of the same probability from the start
point `z ∈ ∂B_ρ(c)`. -/
theorem planarBrownian_exitPoint_eq_lintegral_discHarmonicMeasure {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c y : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hy : y ∈ ball c ρ) {A : Set ℂ} (hA : MeasurableSet A) :
    planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} =
      ∫⁻ z, planarBrownianMotion z {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}
        ∂(discHarmonicMeasure c ρ y) := by
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hmV : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime (ball c ρ) p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime (ball c ρ))
      (ContinuousPath.isStoppingTime_exitTime (ball c ρ) isOpen_ball)
  have hE : MeasurableSet {p : ContinuousPath ℂ |
      p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} := hmU hA
  obtain ⟨R, hR⟩ := hUb.subset_ball y
  have hae := ae_planarBrownian_disc_exitPoint_mem_sphere hy
  rw [planarBrownian_exitPoint_restart hU isOpen_ball
    (by filter_upwards [hae] with ω hω; exact lt_top_iff_ne_top.2 hω.1)
    (by
      filter_upwards [hae, ae_planarBrownianMotion_eval_zero y] with ω hω h0
      exact exitTime_ball_lt_exitTime hU hsub ω (by rw [h0]; exact hy) hω.1 hω.2)
    (by
      filter_upwards [ae_planarBrownianMotion_exitTime_ball_lt_top y R] with ω hω
      exact ((ContinuousPath.exitTime_mono hR ω).trans_lt hω).ne)
    hA,
    ← planarBrownian_disc_exit_distribution_of_mem hy,
    lintegral_map (Kernel.measurable_coe _ hE) hmV]

/-- The probability of leaving `U` in `A`, as a function of the base point in the disc, is the
Poisson integral of its values on the circle. -/
theorem planarBrownian_exitPoint_toReal_eq_discPoissonIntegral {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c x : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hx : x ∈ ball c ρ) {A : Set ℂ} (hA : MeasurableSet A) :
    (planarBrownianMotion x {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal =
      discPoissonIntegral (fun z => (planarBrownianMotion z
        {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal) c ρ x := by
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hE : MeasurableSet {p : ContinuousPath ℂ |
      p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} := hmU hA
  have hk := Kernel.measurable_coe planarBrownianMotion hE
  rw [planarBrownian_exitPoint_eq_lintegral_discHarmonicMeasure hU hUb hsub hx hA,
    ← integral_discHarmonicMeasure hx hk.ennreal_toReal]
  have := isFiniteMeasure_discHarmonicMeasure hx
  exact (integral_toReal hk.aemeasurable
    (Eventually.of_forall fun z => measure_lt_top _ _)).symm

/-- **Total-variation continuity of harmonic measure in the base point.** For a bounded open
`U ⊇ closedBall c ρ`, base points `y, y' ∈ B_ρ(c)` and every Borel set `A`, the exit
probabilities of `U` through `A` differ by at most the circle average of the difference of
Poisson kernels `|P(c, y, ·) - P(c, y', ·)|` (a bound uniform in `A`). -/
theorem abs_planarBrownian_exitPoint_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c y y' : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hy : y ∈ ball c ρ) (hy' : y' ∈ ball c ρ) {A : Set ℂ} (hA : MeasurableSet A) :
    |(planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal -
      (planarBrownianMotion y' {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal| ≤
      Real.circleAverage (fun ζ => |poissonKernel c y ζ - poissonKernel c y' ζ|) c ρ := by
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hE : MeasurableSet {p : ContinuousPath ℂ |
      p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} := hmU hA
  have hgm := (Kernel.measurable_coe planarBrownianMotion hE).ennreal_toReal
  rw [planarBrownian_exitPoint_toReal_eq_discPoissonIntegral hU hUb hsub hy hA,
    planarBrownian_exitPoint_toReal_eq_discPoissonIntegral hU hUb hsub hy' hA]
  have hg0 : ∀ z, 0 ≤ (planarBrownianMotion z
      {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal :=
    fun z => ENNReal.toReal_nonneg
  have hg1 : ∀ z, (planarBrownianMotion z
      {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal ≤ 1 := by
    intro z
    calc _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = 1 := ENNReal.toReal_one
  have hgci : CircleIntegrable (fun z => (planarBrownianMotion z
      {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal) c ρ := by
    refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
      (hgm.comp (continuous_circleMap c ρ).measurable).aestronglyMeasurable
      (Eventually.of_forall fun θ => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
    exact hg1 _
  have h1 := HarmonicBalls.CircleIntegrable.poissonKernel_smul hgci hy
  have h2 := HarmonicBalls.CircleIntegrable.poissonKernel_smul hgci hy'
  unfold discPoissonIntegral
  rw [← Real.circleAverage_sub h1 h2]
  refine Real.abs_circleAverage_le_circleAverage_abs.trans ?_
  apply Real.circleAverage_mono (h1.sub h2).abs
    ((continuousOn_poissonKernel hy).sub (continuousOn_poissonKernel hy')).abs.circleIntegrable'
  intro ζ _
  simp only [Pi.abs_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_nonneg (hg0 ζ)]; exact hg1 ζ)

/-- **Continuity of the Poisson kernel in the base point, in circle-average norm.** As `y' → y`
inside `B_ρ(c)`, the circle average over `∂B_ρ(c)` of `|P(c, y, ·) - P(c, y', ·)|` tends to `0`.
Proof: `(w, θ) ↦ P(c, w, c + ρ e^{iθ})` is jointly continuous on `B_ρ(c) × ℝ` (its denominator
`|ρ e^{iθ} - (w - c)|²` does not vanish), so the parametric integral over `[0, 2π]` is continuous. -/
theorem tendsto_circleAverage_abs_poissonKernel_sub {c y : ℂ} {ρ : ℝ} (hy : y ∈ ball c ρ) :
    Tendsto (fun y' => Real.circleAverage
      (fun ζ => |poissonKernel c y ζ - poissonKernel c y' ζ|) c ρ) (𝓝 y) (𝓝 0) := by
  have hρ : 0 < ρ := pos_of_mem_ball hy
  set g : ℂ → ℝ := fun y' => Real.circleAverage
    (fun ζ => |poissonKernel c y ζ - poissonKernel c y' ζ|) c ρ with hg_def
  have hz : Continuous fun p : ball c ρ × ℝ => circleMap c ρ p.2 :=
    (continuous_circleMap c ρ).comp continuous_snd
  have hw : Continuous fun p : ball c ρ × ℝ => (p.1 : ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hP : Continuous fun p : ball c ρ × ℝ =>
      poissonKernel c (p.1 : ℂ) (circleMap c ρ p.2) := by
    simp only [poissonKernel_def]
    refine Continuous.div (((hz.sub continuous_const).norm.pow 2).sub
      ((hw.sub continuous_const).norm.pow 2))
      (((hz.sub continuous_const).sub (hw.sub continuous_const)).norm.pow 2) ?_
    rintro ⟨⟨w, hwb⟩, θ⟩
    have hw' : ‖w - c‖ < ρ := by simpa [dist_eq_norm] using hwb
    have hzc : ‖circleMap c ρ θ - c‖ = ρ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
    have hne : (circleMap c ρ θ - c) - (w - c) ≠ 0 := by
      intro h
      have h' : ‖circleMap c ρ θ - c‖ = ‖w - c‖ := by rw [sub_eq_zero.mp h]
      linarith
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hF : Continuous (Function.uncurry fun (w : ball c ρ) (θ : ℝ) =>
      |poissonKernel c y (circleMap c ρ θ) - poissonKernel c (w : ℂ) (circleMap c ρ θ)|) :=
    (((continuous_poissonKernel_comp_circleMap hy).comp continuous_snd).sub hP).abs
  have hcont : Continuous ((ball c ρ).domRestrict g) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0
      (2 * Real.pi)).const_smul ((2 * Real.pi)⁻¹)
  have hgc : ContinuousAt g y :=
    (continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt (isOpen_ball.mem_nhds hy)
  have h0 : g y = 0 := by simp [hg_def, Real.circleAverage_def]
  simpa [h0] using hgc.tendsto

/-- **Uniform continuity of harmonic measure in the base point.** For a bounded open
`U ⊇ closedBall c ρ`, `y ∈ B_ρ(c)` and `ε > 0`, for all `y'` near `y` the exit distributions of
planar Brownian motion from `U` started at `y` and at `y'` are within `ε` in total variation:
`|P_y(B_{τ_U} ∈ A) - P_{y'}(B_{τ_U} ∈ A)| ≤ ε` for every Borel `A` simultaneously. -/
theorem eventually_abs_planarBrownian_exitPoint_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c y : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hy : y ∈ ball c ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y' in 𝓝 y, ∀ A : Set ℂ, MeasurableSet A →
      |(planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal -
        (planarBrownianMotion y' {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal|
          ≤ ε := by
  filter_upwards [(tendsto_circleAverage_abs_poissonKernel_sub hy).eventually (gt_mem_nhds hε),
    isOpen_ball.mem_nhds hy] with y' hy'ε hy'b A hA
  exact (abs_planarBrownian_exitPoint_sub_le hU hUb hsub hy hy'b hA).trans hy'ε.le

/-- **Uniform modulus of harmonic measure in the base point on compact sets.** For a bounded
open `U`, a compact `K ⊆ U` and `ε > 0` there is `δ > 0` such that for every `y ∈ K` and every
`y'` with `dist y y' < δ`, the harmonic measures of `U` seen from `y` and from `y'` are within `ε`
in total variation: `|P_y(B_{τ_U} ∈ A) - P_{y'}(B_{τ_U} ∈ A)| ≤ ε` for every Borel `A`.
Proof: the pointwise statement `eventually_abs_planarBrownian_exitPoint_sub_le` at each point of
`K` and the Lebesgue number lemma. This is the base-point modulus of harmonic measure, uniform on
the inner square, in the proof of Lemma 3.14 of Gwynne-Miller-Sheffield (arXiv 1807.07515). -/
theorem exists_forall_abs_planarBrownian_exitPoint_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ K, ∀ y' : ℂ, dist y y' < δ → ∀ A : Set ℂ, MeasurableSet A →
      |(planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal -
        (planarBrownianMotion y' {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal|
          ≤ ε := by
  set p : ℂ → Set ℂ → ℝ := fun y A =>
    (planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal
  have hloc : ∀ y ∈ K, ∀ᶠ y' in 𝓝 y, ∀ A : Set ℂ, MeasurableSet A →
      |p y A - p y' A| ≤ ε / 2 := by
    intro y hy
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU y (hKU hy)
    exact eventually_abs_planarBrownian_exitPoint_sub_le hU hUb
      ((closedBall_subset_ball (half_lt_self hρ)).trans hρU) (mem_ball_self (half_pos hρ))
      (half_pos hε)
  obtain ⟨δ, hδ, hδc⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun y : K => interior {y' | ∀ A : Set ℂ, MeasurableSet A → |p y A - p y' A| ≤ ε / 2})
    (fun _ => isOpen_interior)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, mem_interior_iff_mem_nhds.2 (hloc y hy)⟩)
  refine ⟨δ, hδ, fun y hy y' hyy' A hA => ?_⟩
  obtain ⟨i, hi⟩ := hδc y hy
  have h1 : |p i A - p y A| ≤ ε / 2 := interior_subset (hi (mem_ball_self hδ)) A hA
  have h2 : |p i A - p y' A| ≤ ε / 2 := interior_subset (hi (mem_ball'.2 hyy')) A hA
  show |p y A - p y' A| ≤ ε
  calc |p y A - p y' A| ≤ |p y A - p i A| + |p i A - p y' A| := abs_sub_le _ _ _
    _ = |p i A - p y A| + |p i A - p y' A| := by rw [abs_sub_comm (p y A)]
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε

/-- **Lévy–Prokhorov form of the uniform modulus.** For a bounded open `U`, a compact `K ⊆ U`
and `ε > 0` there is `δ > 0` such that for `y ∈ K` and `dist y y' < δ` the exit laws of planar
Brownian motion from `U` started at `y` and at `y'` (the harmonic measures of `U`) are within `ε`
in the Lévy–Prokhorov distance. -/
theorem exists_forall_levyProkhorovDist_planarBrownian_exitLaw_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ K, ∀ y' : ℂ, dist y y' < δ →
      levyProkhorovDist
        ((planarBrownianMotion y).map fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal))
        ((planarBrownianMotion y').map fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal))
          ≤ ε := by
  set f : ContinuousPath ℂ → ℂ := fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal)
  have hf : Measurable f := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  obtain ⟨δ, hδ, h⟩ := exists_forall_abs_planarBrownian_exitPoint_sub_le hU hUb hK hKU hε
  refine ⟨δ, hδ, fun y hy y' hyy' => ?_⟩
  have : IsProbabilityMeasure ((planarBrownianMotion y).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure ((planarBrownianMotion y').map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  refine levyProkhorovDist_le_of_forall_le _ _ hε.le fun r B hr hB => ?_
  have hr0 : 0 < r := hε.trans hr
  rw [Measure.map_apply hf hB, Measure.map_apply hf isOpen_thickening.measurableSet]
  have hB' : |(planarBrownianMotion y (f ⁻¹' B)).toReal -
      (planarBrownianMotion y' (f ⁻¹' B)).toReal| ≤ ε := h y hy y' hyy' B hB
  have hle : (planarBrownianMotion y (f ⁻¹' B)).toReal ≤
      (planarBrownianMotion y' (f ⁻¹' B)).toReal + ε := by
    linarith [(abs_le.1 hB').2]
  calc planarBrownianMotion y (f ⁻¹' B)
      = ENNReal.ofReal (planarBrownianMotion y (f ⁻¹' B)).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((planarBrownianMotion y' (f ⁻¹' B)).toReal + ε) :=
        ENNReal.ofReal_le_ofReal hle
    _ = planarBrownianMotion y' (f ⁻¹' B) + ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ planarBrownianMotion y' (f ⁻¹' thickening r B) + ENNReal.ofReal r :=
        add_le_add (measure_mono (preimage_mono (self_subset_thickening hr0 B)))
          (ENNReal.ofReal_le_ofReal hr.le)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.exitTime_ball_lt_exitTime
#print axioms MatedCRT.planarBrownian_exitPoint_eq_lintegral_discHarmonicMeasure
#print axioms MatedCRT.planarBrownian_exitPoint_toReal_eq_discPoissonIntegral
#print axioms MatedCRT.abs_planarBrownian_exitPoint_sub_le
#print axioms MatedCRT.tendsto_circleAverage_abs_poissonKernel_sub
#print axioms MatedCRT.eventually_abs_planarBrownian_exitPoint_sub_le
#print axioms MatedCRT.exists_forall_abs_planarBrownian_exitPoint_sub_le
#print axioms MatedCRT.exists_forall_levyProkhorovDist_planarBrownian_exitLaw_le
