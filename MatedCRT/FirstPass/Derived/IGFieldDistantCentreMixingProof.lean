import MatedCRT.FirstPass.Derived.ZeroConeCircleAverageInputsProof
import MatedCRT.FirstPass.Derived.ZeroConeJointStepsProof

/-!
# Mixing of the whole-plane GFF modulo `2πχ` under similarities with distant centres

`IGFieldDistantCentreMixing` (`ZeroConeJointStepsProof.lean`) states that for a whole-plane GFF `h` normalized by
`h_1(0) = 0` and an independent uniform phase `u` on `[0, 2πχ)`, the normalized similarity steps
`T_n = igSimilarityStep γ z_n s_n` (the array of `h(z_n + s_n ·) − h_{s_n}(z_n)` with the phase
`(u + h_{s_n}(z_n)) mod 2πχ`) satisfy `μ(S₁ ∩ T_n⁻¹ S₂) → μ(S₁) μ(S₂)` whenever `|z_n| → ∞`, for arbitrary scales
`s_n > 0` (Duplantier–Sheffield, arXiv:0808.1560, §3.1, for the logarithmic covariance of circle averages).

The proof (`igFieldDistantCentreMixing`) follows that of `igFieldDilationMixing`
(`ZeroConeCircleAverageInputsProof.lean`), with a sequence of maps in place of the iterates of one map.
* Each step preserves the law of the array (`measurePreserving_igSimilarityStep`): the normalized field
  `h(z + s ·) − h_s(z)` has the law of `h`, and `(u + h_s(z)) mod 2πχ` is uniform and independent of `h`.
* Mixing on all measurable sets follows from mixing on the measurable cylinders
  (`tendsto_measure_inter_preimage_seq_of_isSetRing`).
* The covariance of a fixed increment `h_r(c) − h_1(0)` with the far increments `h_{sρ'}(z + s w) − h_s(z)`
  tends to `0` uniformly in the scale `s` (`tendsto_of_incCov_far`): for `s (|w| + ρ' + 1) ≤ |z|/2` the potential
  of the near pair decays on the far circles (`abs_incCov_far_le_of_dist`), and for larger `s` the potential of the
  far pair is `(1/(sρ') + 1/s)`-Lipschitz (`abs_incCov_far_le_of_scale`).
* For a nonzero phase frequency, `Var(h_s(z) − h_1(0)) ≥ log(|z| − 1)` for every `s > 0`
  (`le_variance_cInc_far`) makes the Gaussian characteristic function tend to `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal symmDiff

namespace MatedCRT

/-! ### Mixing along a sequence of measure-preserving maps -/

section SeqMixing

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

theorem abs_measureReal_inter_preimage_sub_le_of_measurePreserving [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) {S₁ S₂ A B : Set α} (hS₁ : MeasurableSet S₁)
    (hS₂ : MeasurableSet S₂) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real (S₁ ∩ T ⁻¹' S₂) - μ.real (A ∩ T ⁻¹' B)| ≤ μ.real (A ∆ S₁) + μ.real (B ∆ S₂) := by
  have hpre : μ.real (T ⁻¹' (B ∆ S₂)) = μ.real (B ∆ S₂) := by
    simp only [measureReal_def]
    rw [hT.measure_preimage (hB.symmDiff hS₂).nullMeasurableSet]
  calc |μ.real (S₁ ∩ T ⁻¹' S₂) - μ.real (A ∩ T ⁻¹' B)|
      ≤ μ.real ((S₁ ∩ T ⁻¹' S₂) ∆ (A ∩ T ⁻¹' B)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hS₁.inter (hT.measurable hS₂)).nullMeasurableSet
          (hA.inter (hT.measurable hB)).nullMeasurableSet
    _ ≤ μ.real ((A ∆ S₁) ∪ T ⁻¹' (B ∆ S₂)) := by
        refine measureReal_mono ?_
        intro x hx
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at hx ⊢
        tauto
    _ ≤ μ.real (A ∆ S₁) + μ.real (T ⁻¹' (B ∆ S₂)) := measureReal_union_le _ _
    _ = μ.real (A ∆ S₁) + μ.real (B ∆ S₂) := by rw [hpre]

/-- **Mixing on a generating ring of sets implies mixing, along a sequence of measure-preserving maps**
(Walters, *An introduction to ergodic theory*, Theorem 1.17, for the maps `T_n` in place of `T^n`). -/
theorem tendsto_measure_inter_preimage_seq_of_isSetRing [IsProbabilityMeasure μ] {C : Set (Set α)}
    (hC : IsSetRing C) (hcov : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mα = MeasurableSpace.generateFrom C) {T : ℕ → α → α}
    (hT : ∀ n, MeasurePreserving (T n) μ μ)
    (hmix : ∀ A ∈ C, ∀ B ∈ C,
      Tendsto (fun n : ℕ => μ.real (A ∩ T n ⁻¹' B)) atTop (𝓝 (μ.real A * μ.real B)))
    {S₁ S₂ : Set α} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) :
    Tendsto (fun n : ℕ => μ (S₁ ∩ T n ⁻¹' S₂)) atTop (𝓝 (μ S₁ * μ S₂)) := by
  have hmeasC : ∀ B ∈ C, MeasurableSet B := fun B hB => by
    have : MeasurableSet[MeasurableSpace.generateFrom C] B :=
      MeasurableSpace.measurableSet_generateFrom hB
    rwa [← hgen] at this
  have hreal : Tendsto (fun n : ℕ => μ.real (S₁ ∩ T n ⁻¹' S₂)) atTop
      (𝓝 (μ.real S₁ * μ.real S₂)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / 8 := by positivity
    obtain ⟨A, hAC, hA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hcov hgen hS₁
      (ENNReal.ofReal_pos.2 hδ)
    obtain ⟨B, hBC, hB⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hcov hgen hS₂
      (ENNReal.ofReal_pos.2 hδ)
    have hAm := hmeasC A hAC
    have hBm := hmeasC B hBC
    have hdA : μ.real (A ∆ S₁) < ε / 8 := ENNReal.toReal_lt_of_lt_ofReal hA
    have hdB : μ.real (B ∆ S₂) < ε / 8 := ENNReal.toReal_lt_of_lt_ofReal hB
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hmix A hAC B hBC) (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := abs_measureReal_inter_preimage_sub_le_of_measurePreserving (hT n) hS₁ hS₂ hAm hBm
    have h2A : |μ.real A - μ.real S₁| ≤ μ.real (A ∆ S₁) :=
      abs_measureReal_sub_le_measureReal_symmDiff hAm.nullMeasurableSet hS₁.nullMeasurableSet
    have h2B : |μ.real B - μ.real S₂| ≤ μ.real (B ∆ S₂) :=
      abs_measureReal_sub_le_measureReal_symmDiff hBm.nullMeasurableSet hS₂.nullMeasurableSet
    have h4 : |μ.real A * μ.real B - μ.real S₁ * μ.real S₂| ≤ μ.real (A ∆ S₁) + μ.real (B ∆ S₂) := by
      have e : μ.real A * μ.real B - μ.real S₁ * μ.real S₂ =
          (μ.real A - μ.real S₁) * μ.real B + μ.real S₁ * (μ.real B - μ.real S₂) := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg measureReal_nonneg]
        calc |μ.real A - μ.real S₁| * μ.real B ≤ |μ.real A - μ.real S₁| * 1 :=
              mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg _)
          _ ≤ μ.real (A ∆ S₁) := by rw [mul_one]; exact h2A
      · rw [abs_mul, abs_of_nonneg measureReal_nonneg]
        calc μ.real S₁ * |μ.real B - μ.real S₂| ≤ 1 * |μ.real B - μ.real S₂| :=
              mul_le_mul_of_nonneg_right measureReal_le_one (abs_nonneg _)
          _ ≤ μ.real (B ∆ S₂) := by rw [one_mul]; exact h2B
    have hNn := hN n hn
    rw [Real.dist_eq] at hNn ⊢
    have t1 := abs_sub_le (μ.real (S₁ ∩ T n ⁻¹' S₂)) (μ.real (A ∩ T n ⁻¹' B))
      (μ.real S₁ * μ.real S₂)
    have t2 := abs_sub_le (μ.real (A ∩ T n ⁻¹' B)) (μ.real A * μ.real B) (μ.real S₁ * μ.real S₂)
    linarith
  have hfin : ∀ n : ℕ, μ (S₁ ∩ T n ⁻¹' S₂) ≠ ∞ := fun n => measure_ne_top _ _
  rw [← ENNReal.tendsto_toReal_iff hfin
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simpa only [measureReal_def, ENNReal.toReal_mul] using hreal

end SeqMixing

/-! ### The normalized similarity step preserves the law of the array -/

section Similarity

theorem igSimilarityStep_of_nonpos (γ : ℝ) (z : ℂ) (s : ℝ) (f : ℝ × ℂ → ℝ) {x : ℝ × ℂ}
    (hx : ¬ 0 < x.1) : igSimilarityStep γ z s f x = 0 := by
  simp only [igSimilarityStep, hx, ↓reduceIte]

theorem igSimilarityStep_igPosCircleProcess_of_pos (γ : ℝ) (z : ℂ) {s : ℝ} (hs : 0 < s) (g : Field)
    (v : ℝ) {x : ℝ × ℂ} (hx : 0 < x.1) :
    igSimilarityStep γ z s (igPosCircleProcess g v) x =
      v + LQGMetric.circleAvg g (s * x.1) (z + (s : ℂ) * x.2) -
        ((⌊(v + LQGMetric.circleAvg g s z) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) *
          (2 * Real.pi * igChi γ) := by
  have hsx : 0 < s * x.1 := mul_pos hs hx
  simp only [igSimilarityStep, igPosCircleProcess, hx, hsx, hs, ↓reduceIte]

/-- The normalized field `h(z + s ·) − h_s(z)`. -/
def igNormalizedSimilarity (z : ℂ) (s : ℝ) (h : Field) : Field :=
  LQGMetric.addConst (LQGMetric.affineComp s z h) (-LQGMetric.circleAvg h s z)

theorem measurable_igNormalizedSimilarity (z : ℂ) (s : ℝ) :
    Measurable (igNormalizedSimilarity z s) := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  simp only [igNormalizedSimilarity, LQGMetric.GFFInv.addConst_apply]
  exact ((LQGMetric.measurable_distOn_apply φ).comp (LQGMetric.measurable_affineComp s z)).add
    ((LQGMetric.measurable_circleAvg_left s z).neg.const_mul _)

/-- **The similarity step of the array is a modification of the array of the normalized pair.** At each fixed
`x`, almost surely, the normalized similarity step of the array of `(h, u)` agrees at `x` with the array of
`(h(z + s ·) − h_s(z), (u + h_s(z)) mod 2πχ)`. -/
theorem ae_igSimilarityStep_igPosCircleProcess {γ s : ℝ} (hs : 0 < s) (z : ℂ)
    (hp : 0 < 2 * Real.pi * igChi γ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h : Ω' → Field} (hh : LQGMetric.IsWholePlaneGFF h P') (u : Ω' → ℝ) (x : ℝ × ℂ) :
    ∀ᵐ ω ∂P', igSimilarityStep γ z s (igPosCircleProcess (h ω) (u ω)) x =
      igPosCircleProcess (igNormalizedSimilarity z s (h ω))
        (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z)) x := by
  by_cases hx : 0 < x.1
  · have hA := LQGMetric.CircleAvg.ae_circleAvg_addConst (hh.affineComp hs z) x.2 hx
    have hB := LQGMetric.CircleAvg.ae_circleAvg_affineComp (hh.affineComp hs z) hx x.2
    have hC := LQGMetric.CircleAvg.ae_circleAvg_affineComp hh (mul_pos hs hx) (z + (s : ℂ) * x.2)
    filter_upwards [hA, hB, hC] with ω hAω hBω hCω
    rw [igSimilarityStep_igPosCircleProcess_of_pos γ z hs _ _ hx, igPosCircleProcess_of_pos _ _ hx,
      igNormalizedSimilarity, hAω, ← hBω, LQGMetric.GM.affineComp_comp hx.ne' hs.ne',
      add_comm ((s : ℂ) * x.2) z, hCω]
    simp only [toIcoMod, toIcoDiv_eq_floor, sub_zero, zsmul_eq_mul]
    ring
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [igSimilarityStep_of_nonpos γ z s _ hx, igPosCircleProcess_of_nonpos _ _ hx]

/-- **The normalized pair has the law of the pair** (translation and scale invariance of the normalized
whole-plane GFF and uniformity of `(u + h_s(z)) mod 2πχ` given the field). -/
theorem map_igNormalizedSimilarity_pair {γ s : ℝ} (hs : 0 < s) (z : ℂ) (hp : 0 < 2 * Real.pi * igChi γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → Field} {u : Ω' → ℝ}
    (hh : LQGMetric.IsNormalizedWPGFF h P') (hum : Measurable u)
    (hulaw : P'.map u = LatticeProb.uniformIco (2 * Real.pi * igChi γ)) (hind : IndepFun u h P') :
    P'.map (fun ω => (igNormalizedSimilarity z s (h ω),
        toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z))) =
      P'.map (fun ω => (h ω, u ω)) := by
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have hhm : Measurable h := hh.1.measurable
  have ham : Measurable fun g : Field => LQGMetric.circleAvg g s z :=
    LQGMetric.measurable_circleAvg_left s z
  have hGm := measurable_igNormalizedSimilarity z s
  have hGI : Measurable fun ω => igNormalizedSimilarity z s (h ω) := by
    simpa only [Function.comp_def] using hGm.comp hhm
  have hVm : Measurable fun ω => toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z) := by
    simpa only [Function.comp_def, Pi.add_apply] using
      (LatticeProb.measurable_toIcoMod_zero hp).comp (hum.add (ham.comp hhm))
  have hVI := LatticeProb.indepFun_toIcoMod_add_uniformIco hp hum hhm hulaw hind ham
  have hVG := LatticeProb.indepFun_toIcoMod_add_uniformIco_comp hp hum hhm hulaw hind ham hGm
  rw [(indepFun_iff_map_prod_eq_prod_map_map hGI.aemeasurable hVm.aemeasurable).1 hVG.symm,
    (indepFun_iff_map_prod_eq_prod_map_map hhm.aemeasurable hum.aemeasurable).1 hind.symm]
  congr 1
  · exact LQGMetric.CircleAvg.map_affine_sub_circleAvg hh hs z
  · rw [hVI.1, hulaw]

theorem measurePreserving_igSimilarityStep_of_measurable {γ s : ℝ} (hs : 0 < s) (z : ℂ)
    (hp : 0 < 2 * Real.pi * igChi γ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h : Ω' → Field} {u : Ω' → ℝ} (hh : LQGMetric.IsNormalizedWPGFF h P') (hum : Measurable u)
    (hulaw : P'.map u = LatticeProb.uniformIco (2 * Real.pi * igChi γ)) (hind : IndepFun u h P') :
    MeasurePreserving (igSimilarityStep γ z s) (P'.map fun ω => igPosCircleProcess (h ω) (u ω))
      (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) := by
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have hhm : Measurable h := hh.1.measurable
  have ham : Measurable fun g : Field => LQGMetric.circleAvg g s z :=
    LQGMetric.measurable_circleAvg_left s z
  have hTm := measurable_igSimilarityStep γ z s
  have hKm : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hhm hum
  have hTK : Measurable fun ω => igSimilarityStep γ z s (igPosCircleProcess (h ω) (u ω)) := by
    simpa only [Function.comp_def] using hTm.comp hKm
  have hGI : Measurable fun ω => igNormalizedSimilarity z s (h ω) := by
    simpa only [Function.comp_def] using (measurable_igNormalizedSimilarity z s).comp hhm
  have hVm : Measurable fun ω => toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z) := by
    simpa only [Function.comp_def, Pi.add_apply] using
      (LatticeProb.measurable_toIcoMod_zero hp).comp (hum.add (ham.comp hhm))
  have hYm : Measurable fun ω => igPosCircleProcess (igNormalizedSimilarity z s (h ω))
      (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z)) :=
    measurable_igPosCircleProcess_comp hGI hVm
  have hlaw1 : P'.map (fun ω => igSimilarityStep γ z s (igPosCircleProcess (h ω) (u ω))) =
      P'.map (fun ω => igPosCircleProcess (igNormalizedSimilarity z s (h ω))
        (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z))) :=
    map_eq_of_forall_ae_eq (X := fun x ω => igSimilarityStep γ z s (igPosCircleProcess (h ω) (u ω)) x)
      (Y := fun x ω => igPosCircleProcess (igNormalizedSimilarity z s (h ω))
        (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z)) x)
      hTK.aemeasurable hYm.aemeasurable fun x => ae_igSimilarityStep_igPosCircleProcess hs z hp hh.1 u x
  have hlaw2 : P'.map (fun ω => igPosCircleProcess (igNormalizedSimilarity z s (h ω))
      (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s z))) =
      P'.map fun ω => igPosCircleProcess (h ω) (u ω) := by
    have e1 := Measure.map_map measurable_igPosCircleProcess (hGI.prodMk hVm) (μ := P')
    have e2 := Measure.map_map measurable_igPosCircleProcess (hhm.prodMk hum) (μ := P')
    simp only [Function.comp_def] at e1 e2
    rw [← e1, ← e2, map_igNormalizedSimilarity_pair hs z hp hh hum hulaw hind]
  refine ⟨hTm, ?_⟩
  rw [Measure.map_map hTm hKm, Function.comp_def, hlaw1, hlaw2]

/-- **The normalized similarity step preserves the law of the circle-average array of the whole-plane GFF modulo
`2πχ`.** For every `z ∈ ℂ` and `s > 0`, the array of `(h, u)` and its normalized similarity step have the same law:
the field `h(z + s ·) − h_s(z)` has the law of `h` (translation and scale invariance), `(u + h_s(z)) mod 2πχ` is
uniform and independent of `h`, and at each fixed positive radius and centre the circle average of
`h(z + s ·) − h_s(z)` is almost surely `h_{sρ}(z + sw) − h_s(z)`. -/
theorem measurePreserving_igSimilarityStep {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) {s : ℝ} (hs : 0 < s) (z : ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → Field} {u : Ω' → ℝ}
    (hh : LQGMetric.IsNormalizedWPGFF h P')
    (hulaw : P'.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h u P') :
    MeasurePreserving (igSimilarityStep γ z s) (P'.map fun ω => igPosCircleProcess (h ω) (u ω))
      (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) := by
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have hp : 0 < 2 * Real.pi * igChi γ := by
    have := Sec1.igChi_pos hγ.1 hγ.2
    positivity
  have huae : AEMeasurable u P' := aemeasurable_of_map_eq_igUniform hulaw
  have hu'law : P'.map (huae.mk u) = LatticeProb.uniformIco (2 * Real.pi * igChi γ) := by
    rw [← Measure.map_congr huae.ae_eq_mk]
    exact hulaw
  have hind' : IndepFun (huae.mk u) h P' := (hind.congr (ae_eq_refl _) huae.ae_eq_mk).symm
  have hμ : (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) =
      P'.map fun ω => igPosCircleProcess (h ω) (huae.mk u ω) := by
    refine Measure.map_congr ?_
    filter_upwards [huae.ae_eq_mk] with ω hω
    simp only [hω]
  rw [hμ]
  exact measurePreserving_igSimilarityStep_of_measurable hs z hp hh huae.measurable_mk hu'law hind'

end Similarity

/-! ### Coordinates of the similarity step -/

section Coord

theorem exists_igMixCoord_igSimilarityStep (γ : ℝ) (K : Finset (ℝ × ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s)
    (g : Field) (v : ℝ) :
    ∃ k : ℤ, igMixCoord K (igSimilarityStep γ z s (igPosCircleProcess g v)) =
      (v + LQGMetric.circleAvg g s z - k * (2 * Real.pi * igChi γ),
        fun x : K => if 0 < (x : ℝ × ℂ).1 then
          LQGMetric.circleAvg g (s * (x : ℝ × ℂ).1) (z + (s : ℂ) * (x : ℝ × ℂ).2) -
            LQGMetric.circleAvg g s z else 0) := by
  refine ⟨⌊(v + LQGMetric.circleAvg g s z) / (2 * Real.pi * igChi γ)⌋, ?_⟩
  have ho : igSimilarityStep γ z s (igPosCircleProcess g v) (1, 0) =
      v + LQGMetric.circleAvg g s z -
        ((⌊(v + LQGMetric.circleAvg g s z) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) *
          (2 * Real.pi * igChi γ) := by
    rw [igSimilarityStep_igPosCircleProcess_of_pos γ z hs g v (x := ((1 : ℝ), (0 : ℂ))) one_pos]
    simp only [mul_one, mul_zero, add_zero]
  refine Prod.ext ho (funext fun x => ?_)
  simp only [igMixCoord]
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · rw [ite_eq_left hx, ite_eq_left hx, ho, igSimilarityStep_igPosCircleProcess_of_pos γ z hs g v hx]
    ring
  · rw [ite_eq_right hx, ite_eq_right hx, igSimilarityStep_of_nonpos γ z s _ hx]

end Coord

/-! ### Logarithmic potentials of circle pairs -/

section Potential

open LQGMetric LQGMetric.CircleAvg

theorem norm_sub_abs_le_norm_of_mem_sphere {Z x : ℂ} {R : ℝ} (hx : x ∈ Metric.sphere Z |R|) :
    ‖Z‖ - |R| ≤ ‖x‖ := by
  have h1 : ‖x - Z‖ = |R| := by rw [← dist_eq_norm]; exact hx
  have h2 := norm_sub_norm_le Z x
  rw [norm_sub_rev, h1] at h2
  linarith

theorem abs_circleAverage_sub_le_of_forall {f : ℂ → ℝ} {c : ℂ} {R a M : ℝ}
    (hf : CircleIntegrable f c R) (h : ∀ x ∈ Metric.sphere c |R|, |f x - a| ≤ M) :
    |Real.circleAverage f c R - a| ≤ M := by
  rw [abs_le]
  constructor
  · have hc : CircleIntegrable (fun _ : ℂ => a - M) c R := circleIntegrable_const _ _ _
    have := Real.circleAverage_mono_on_of_le_circle (hc.sub hf) (a := 0) fun y hy => by
      have := (abs_le.1 (h y hy)).1
      simp only [Pi.sub_apply]
      linarith
    rw [Real.circleAverage_sub hc hf, Real.circleAverage_const] at this
    linarith
  · have := Real.circleAverage_mono_on_of_le_circle hf (a := a + M) fun y hy => by
      have := (abs_le.1 (h y hy)).2
      linarith
    linarith

/-- The potential of the near pair `σ_{c,r} − σ_{0,1}` decays at infinity. -/
theorem abs_circLog_sub_circLog_far_le {c : ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : ‖c‖ < ‖x‖) :
    |circLog c r x - circLog 0 1 x| ≤ (|r - 1| + ‖c‖) / (‖x‖ - ‖c‖) := by
  have hm : 0 < ‖x‖ - ‖c‖ := by linarith
  rw [circLog_eq_log_max hr, circLog_eq_log_max one_pos]
  refine (LQGMetric.CircleAvg.abs_log_sub_log_le hm ?_ ?_).trans ?_
  · calc ‖x‖ - ‖c‖ ≤ ‖c - x‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le x c
      _ ≤ max r ‖c - x‖ := le_max_right _ _
  · calc ‖x‖ - ‖c‖ ≤ ‖0 - x‖ := by rw [zero_sub, norm_neg]; linarith [norm_nonneg c]
      _ ≤ max 1 ‖0 - x‖ := le_max_right _ _
  · refine (div_le_div_iff_of_pos_right hm).2 ?_
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · linarith [norm_nonneg c]
    · refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [sub_sub_sub_cancel_right, sub_zero]
      linarith [abs_nonneg (r - 1)]

/-- **Covariance of a near and a far increment, large far scale.** The covariance of `h_r(c) − h_1(0)` and
`h_{R₁}(Z₁) − h_S(Z)` is the difference of the circle averages over `∂B_r(c)` and `∂B_1(0)` of the potential of
`σ_{Z₁,R₁} − σ_{Z,S}`, which is `(1/R₁ + 1/S)`-Lipschitz. -/
theorem abs_incCov_far_le_of_scale {c : ℂ} {r : ℝ} (hr : 0 < r) {Z₁ Z : ℂ} {R₁ S : ℝ} (hR₁ : 0 < R₁)
    (hS : 0 < S) : |incCov c r 0 1 Z₁ R₁ Z S| ≤ (1 / R₁ + 1 / S) * (‖c‖ + r + 1) := by
  have hci : ∀ (a : ℂ) (t : ℝ) (b : ℂ) (q : ℝ), 0 < t → CircleIntegrable (circLog a t) b q :=
    fun a t b q ht => ((continuous_circLog ht.ne' a).continuousOn).circleIntegrable'
  set f : ℂ → ℝ := fun x => circLog Z₁ R₁ x - circLog Z S x with hf_def
  have hfc : Continuous f := (continuous_circLog hR₁.ne' Z₁).sub (continuous_circLog hS.ne' Z)
  have hL : ∀ x y, |f x - f y| ≤ ‖x - y‖ / R₁ + ‖x - y‖ / S := by
    intro x y
    have e1 := abs_circLog_sub_le hR₁ Z₁ x y
    have e2 := abs_circLog_sub_le hS Z x y
    have e : f x - f y = (circLog Z₁ R₁ x - circLog Z₁ R₁ y) - (circLog Z S x - circLog Z S y) := by
      simp only [hf_def]
      ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  have hcirc : ∀ (b : ℂ) (q : ℝ), 0 < q →
      |Real.circleAverage f b q - f 0| ≤ (‖b‖ + q) / R₁ + (‖b‖ + q) / S := by
    intro b q hq
    refine abs_circleAverage_sub_le_of_forall hfc.continuousOn.circleIntegrable' fun x hx => ?_
    have hxb : ‖x - b‖ = q := by rw [← dist_eq_norm, ← abs_of_pos hq]; exact hx
    have hxn : ‖x‖ ≤ ‖b‖ + q := by
      calc ‖x‖ = ‖b + (x - b)‖ := by rw [add_sub_cancel]
        _ ≤ ‖b‖ + ‖x - b‖ := norm_add_le _ _
        _ = ‖b‖ + q := by rw [hxb]
    refine (hL x 0).trans ?_
    rw [sub_zero]
    gcongr
  have hexp : incCov c r 0 1 Z₁ R₁ Z S =
      -((Real.circleAverage f c r - f 0) - (Real.circleAverage f 0 1 - f 0)) := by
    have e1 : Real.circleAverage f c r =
        Real.circleAverage (circLog Z₁ R₁) c r - Real.circleAverage (circLog Z S) c r :=
      Real.circleAverage_fun_sub (hci Z₁ R₁ c r hR₁) (hci Z S c r hS)
    have e2 : Real.circleAverage f 0 1 =
        Real.circleAverage (circLog Z₁ R₁) 0 1 - Real.circleAverage (circLog Z S) 0 1 :=
      Real.circleAverage_fun_sub (hci Z₁ R₁ 0 1 hR₁) (hci Z S 0 1 hS)
    rw [e1, e2]
    simp only [incCov, circCov]
    ring
  rw [hexp, abs_neg]
  have h1 := hcirc c r hr
  have h2 := hcirc 0 1 one_pos
  rw [norm_zero, zero_add] at h2
  calc |(Real.circleAverage f c r - f 0) - (Real.circleAverage f 0 1 - f 0)|
      ≤ |Real.circleAverage f c r - f 0| + |Real.circleAverage f 0 1 - f 0| := abs_sub _ _
    _ ≤ ((‖c‖ + r) / R₁ + (‖c‖ + r) / S) + (1 / R₁ + 1 / S) := add_le_add h1 h2
    _ = (1 / R₁ + 1 / S) * (‖c‖ + r + 1) := by ring

/-- **Covariance of a far and a near increment, far circles.** The covariance of `h_{R₁}(Z₁) − h_S(Z)` and
`h_r(c) − h_1(0)` is the difference of the circle averages over `∂B_{R₁}(Z₁)` and `∂B_S(Z)` of the potential of
`σ_{c,r} − σ_{0,1}`, which is at most `(|r − 1| + |c|)/(|x| − |c|)` at `x`. -/
theorem abs_incCov_far_le_of_dist {c : ℂ} {r : ℝ} (hr : 0 < r) {Z₁ Z : ℂ} {R₁ S m : ℝ} (hm : ‖c‖ < m)
    (h1 : ∀ x ∈ Metric.sphere Z₁ |R₁|, m ≤ ‖x‖) (h2 : ∀ x ∈ Metric.sphere Z |S|, m ≤ ‖x‖) :
    |incCov Z₁ R₁ Z S c r 0 1| ≤ 2 * ((|r - 1| + ‖c‖) / (m - ‖c‖)) := by
  have hci : ∀ (a : ℂ) (t : ℝ) (b : ℂ) (q : ℝ), 0 < t → CircleIntegrable (circLog a t) b q :=
    fun a t b q ht => ((continuous_circLog ht.ne' a).continuousOn).circleIntegrable'
  set g : ℂ → ℝ := fun x => circLog c r x - circLog 0 1 x with hg_def
  have hgc : Continuous g := (continuous_circLog hr.ne' c).sub (continuous_circLog one_ne_zero 0)
  have hpt : ∀ x, m ≤ ‖x‖ → |g x - 0| ≤ (|r - 1| + ‖c‖) / (m - ‖c‖) := by
    intro x hx
    rw [sub_zero]
    refine (abs_circLog_sub_circLog_far_le hr (hm.trans_le hx)).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hA1 := abs_circleAverage_sub_le_of_forall (c := Z₁) (R := R₁) hgc.continuousOn.circleIntegrable'
    fun x hx => hpt x (h1 x hx)
  have hA2 := abs_circleAverage_sub_le_of_forall (c := Z) (R := S) hgc.continuousOn.circleIntegrable'
    fun x hx => hpt x (h2 x hx)
  rw [sub_zero] at hA1 hA2
  have hexp : incCov Z₁ R₁ Z S c r 0 1 = -(Real.circleAverage g Z₁ R₁ - Real.circleAverage g Z S) := by
    have e1 : Real.circleAverage g Z₁ R₁ =
        Real.circleAverage (circLog c r) Z₁ R₁ - Real.circleAverage (circLog 0 1) Z₁ R₁ :=
      Real.circleAverage_fun_sub (hci c r Z₁ R₁ hr) (hci 0 1 Z₁ R₁ one_pos)
    have e2 : Real.circleAverage g Z S =
        Real.circleAverage (circLog c r) Z S - Real.circleAverage (circLog 0 1) Z S :=
      Real.circleAverage_fun_sub (hci c r Z S hr) (hci 0 1 Z S one_pos)
    rw [e1, e2]
    simp only [incCov, circCov]
    ring
  rw [hexp, abs_neg]
  calc |Real.circleAverage g Z₁ R₁ - Real.circleAverage g Z S|
      ≤ |Real.circleAverage g Z₁ R₁| + |Real.circleAverage g Z S| := abs_sub _ _
    _ ≤ (|r - 1| + ‖c‖) / (m - ‖c‖) + (|r - 1| + ‖c‖) / (m - ‖c‖) := add_le_add hA1 hA2
    _ = 2 * ((|r - 1| + ‖c‖) / (m - ‖c‖)) := by ring

/-- **Decorrelation at distant centres, uniformly in the scale**.
A sequence `C_n` equal to both expressions of the covariance of `h_r(c) − h_1(0)` and
`h_{ρ_n ρ'}(z_n + ρ_n w) − h_{ρ_n}(z_n)` tends to `0` when `|z_n| → ∞`, for arbitrary `ρ_n > 0`. -/
theorem tendsto_of_incCov_far {c : ℂ} {r : ℝ} (hr : 0 < r) (w : ℂ) {ρ' : ℝ} (hρ' : 0 < ρ')
    {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n) (hz : Tendsto (fun n => ‖z n‖) atTop atTop)
    {C : ℕ → ℝ} (h1 : ∀ n, C n = incCov c r 0 1 (z n + (ρ n : ℂ) * w) (ρ n * ρ') (z n) (ρ n))
    (h2 : ∀ n, C n = incCov (z n + (ρ n : ℂ) * w) (ρ n * ρ') (z n) (ρ n) c r 0 1) :
    Tendsto C atTop (𝓝 0) := by
  set K : ℝ := ‖w‖ + ρ' + 1 with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  have hb1 : Tendsto (fun n => 2 * ((|r - 1| + ‖c‖) / (‖z n‖ / 2 - ‖c‖))) atTop (𝓝 0) := by
    have hd : Tendsto (fun n => ‖z n‖ / 2 - ‖c‖) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-‖c‖) (hz.atTop_div_const two_pos)).congr fun n => by ring
    have := ((tendsto_const_nhds (x := |r - 1| + ‖c‖)).div_atTop hd).const_mul 2
    rw [mul_zero] at this
    exact this
  have hb2 : Tendsto (fun n => (1 / ρ' + 1) * (‖c‖ + r + 1) * (2 * K / ‖z n‖)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := 2 * K)).div_atTop hz).const_mul ((1 / ρ' + 1) * (‖c‖ + r + 1))
    rw [mul_zero] at this
    exact this
  have hb := hb1.add hb2
  rw [add_zero] at hb
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [hz.eventually_gt_atTop (2 * ‖c‖ + 1)] with n hn
  have hcn := norm_nonneg c
  have ht : 0 < ‖z n‖ := by linarith
  have hρn := hρ n
  have hb1n : 0 ≤ 2 * ((|r - 1| + ‖c‖) / (‖z n‖ / 2 - ‖c‖)) := by
    have : 0 < ‖z n‖ / 2 - ‖c‖ := by linarith
    positivity
  have hb2n : 0 ≤ (1 / ρ' + 1) * (‖c‖ + r + 1) * (2 * K / ‖z n‖) := by positivity
  have hexpK : ρ n * K = ρ n * ‖w‖ + ρ n * ρ' + ρ n := by rw [hK_def]; ring
  have hw0 : 0 ≤ ρ n * ‖w‖ := mul_nonneg hρn.le (norm_nonneg w)
  have hρρ : 0 < ρ n * ρ' := mul_pos hρn hρ'
  rw [Real.norm_eq_abs]
  rcases le_or_gt (ρ n * K) (‖z n‖ / 2) with hcase | hcase
  · rw [h2 n]
    have hZ1 : ∀ y ∈ Metric.sphere (z n + (ρ n : ℂ) * w) |ρ n * ρ'|, ‖z n‖ / 2 ≤ ‖y‖ := by
      intro y hy
      have e1 := norm_sub_abs_le_norm_of_mem_sphere hy
      have e2 := norm_sub_le (z n + (ρ n : ℂ) * w) ((ρ n : ℂ) * w)
      rw [add_sub_cancel_right] at e2
      have e3 : ‖(ρ n : ℂ) * w‖ = ρ n * ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρn]
      rw [e3] at e2
      rw [abs_of_pos hρρ] at e1
      linarith
    have hZ0 : ∀ y ∈ Metric.sphere (z n) |ρ n|, ‖z n‖ / 2 ≤ ‖y‖ := by
      intro y hy
      have e1 := norm_sub_abs_le_norm_of_mem_sphere hy
      rw [abs_of_pos hρn] at e1
      linarith
    have hII := abs_incCov_far_le_of_dist (c := c) hr (m := ‖z n‖ / 2) (by linarith) hZ1 hZ0
    linarith
  · rw [h1 n]
    have hI := abs_incCov_far_le_of_scale (c := c) hr (Z₁ := z n + (ρ n : ℂ) * w) (Z := z n) hρρ hρn
    have hinv : 1 / ρ n ≤ 2 * K / ‖z n‖ := by
      rw [div_le_div_iff₀ hρn ht]
      linarith
    have hC0 : 0 ≤ (1 / ρ' + 1) * (‖c‖ + r + 1) := by positivity
    calc |incCov c r 0 1 (z n + (ρ n : ℂ) * w) (ρ n * ρ') (z n) (ρ n)|
        ≤ (1 / (ρ n * ρ') + 1 / ρ n) * (‖c‖ + r + 1) := hI
      _ = (1 / ρ' + 1) * (‖c‖ + r + 1) * (1 / ρ n) := by ring
      _ ≤ (1 / ρ' + 1) * (‖c‖ + r + 1) * (2 * K / ‖z n‖) := mul_le_mul_of_nonneg_left hinv hC0
      _ ≤ _ := by linarith

end Potential

/-! ### The far increments -/

section GaussSim

open LQGMetric LQGMetric.CircleAvg LQGDimension.SegLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field}

/-- The far increments `h_{sρ'}(z + s w) − h_s(z)` at the indices `(ρ', w)` of positive radius, `0` at the
others. -/
def igSimGauss (h : Ω → Field) (K : Finset (ℝ × ℂ)) (z : ℂ) (s : ℝ) (ω : Ω) (x : K) : ℝ :=
  if 0 < (x : ℝ × ℂ).1 then cInc h (s * (x : ℝ × ℂ).1) (z + (s : ℂ) * (x : ℝ × ℂ).2) s z ω else 0

omit [MeasurableSpace Ω] in
theorem inGSpan_igSimGauss (K : Finset (ℝ × ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s) (x : K) :
    InGSpan (incProc h) (fun ω => igSimGauss h K z s ω x) := by
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · simp only [igSimGauss, hx, ↓reduceIte]
    exact inGSpan_cInc (mul_pos hs hx) hs _ _
  · simp only [igSimGauss, hx, ↓reduceIte]
    exact InGSpan.zero

omit [MeasurableSpace Ω] in
theorem inGSpan_sum_igSimGauss (K : Finset (ℝ × ℂ)) (z : ℂ) {s : ℝ} (hs : 0 < s) (t : K → ℝ) :
    InGSpan (incProc h) (fun ω => ∑ x, t x * igSimGauss h K z s ω x) :=
  InGSpan.finset_sum _ fun x _ => (inGSpan_igSimGauss K z hs x).const_mul (t x)

/-- **`Var(h_s(z) − h_1(0)) ≥ log(|z| − 1)` for every scale `s > 0`**: the variance is `−log s + ⨍_{∂B_s(z)} log max(1, |x|) + ⨍_{∂B_1(0)} log max(s, |z − x|)`, the first
average is at least `⨍_{∂B_s(z)} log |x| = log max(s, |z|) ≥ log s`, and the second at least
`log max(s, |z| − 1)`. -/
theorem le_variance_cInc_far (hh : IsWholePlaneGFF h P) {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : 1 < ‖z‖) :
    Real.log (‖z‖ - 1) ≤ Var[cInc h ρ z 1 0; P] := by
  rw [(map_cInc hh hρ one_pos z 0).2]
  have h1 : circCov z ρ z ρ = Real.log ρ := by
    rw [circCov_center z hρ ρ hρ, inv_mul_cancel₀ hρ.ne']
    simp
  have h2 : circCov 0 1 0 1 = 0 := by
    rw [circCov_center 0 one_pos 1 one_pos]
    simp
  have h3 : Real.log (max ρ ‖z‖) ≤ circCov z ρ 0 1 := by
    have hci1 : CircleIntegrable (fun a => Real.log ‖a - 0‖) z ρ :=
      circleIntegrable_log_norm_sub_const (a := 0) (c := z) ρ
    have hci2 : CircleIntegrable (circLog 0 1) z ρ :=
      ((continuous_circLog one_ne_zero 0).continuousOn).circleIntegrable'
    have e : Real.circleAverage (fun a => Real.log ‖a - 0‖) z ρ = Real.log (max ρ ‖z‖) := by
      have := circLog_eq_log_max hρ z 0
      rw [sub_zero] at this
      exact this
    rw [← e]
    refine Real.circleAverage_mono hci1 hci2 fun x _ => ?_
    show Real.log ‖x - 0‖ ≤ circLog 0 1 x
    rw [circLog_eq_log_max one_pos, zero_sub, norm_neg, sub_zero]
    rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
    · rw [← hx, Real.log_zero]
      exact Real.log_nonneg (le_max_left _ _)
    · exact Real.log_le_log hx (le_max_right _ _)
  have h4 : Real.log (max ρ (‖z‖ - 1)) ≤ circCov 0 1 z ρ := by
    have hci : CircleIntegrable (circLog z ρ) 0 1 :=
      ((continuous_circLog hρ.ne' z).continuousOn).circleIntegrable'
    have hc : CircleIntegrable (fun _ : ℂ => Real.log (max ρ (‖z‖ - 1))) 0 1 := circleIntegrable_const _ _ _
    calc Real.log (max ρ (‖z‖ - 1)) = Real.circleAverage (fun _ => Real.log (max ρ (‖z‖ - 1))) 0 1 :=
          (Real.circleAverage_const _ _ _).symm
      _ ≤ circCov 0 1 z ρ := Real.circleAverage_mono hc hci fun x hx => by
          have hx1 : ‖x‖ = 1 := by simpa using hx
          show Real.log (max ρ (‖z‖ - 1)) ≤ circLog z ρ x
          rw [circLog_eq_log_max hρ]
          refine Real.log_le_log (lt_max_of_lt_left hρ) (max_le (le_max_left _ _) ?_)
          calc ‖z‖ - 1 = ‖z‖ - ‖x‖ := by rw [hx1]
            _ ≤ ‖z - x‖ := norm_sub_norm_le z x
            _ ≤ max ρ ‖z - x‖ := le_max_right _ _
  have h5 : Real.log ρ ≤ Real.log (max ρ ‖z‖) := Real.log_le_log hρ (le_max_left _ _)
  have h6 : Real.log (‖z‖ - 1) ≤ Real.log (max ρ (‖z‖ - 1)) :=
    Real.log_le_log (by linarith) (le_max_right _ _)
  simp only [incCov]
  linarith

theorem tendsto_variance_cInc_far (hh : IsWholePlaneGFF h P) {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    {z : ℕ → ℂ} (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    Tendsto (fun n => Var[cInc h (ρ n) (z n) 1 0; P]) atTop atTop := by
  have hsub : Tendsto (fun n => ‖z n‖ - 1) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-1) hz).congr fun n => by ring
  have hlog : Tendsto (fun n => Real.log (‖z n‖ - 1)) atTop atTop := Real.tendsto_log_atTop.comp hsub
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [hz.eventually_gt_atTop 1] with n hn
  exact le_variance_cInc_far hh (hρ n) hn

theorem tendsto_cov_igSimGauss (hh : IsWholePlaneGFF h P) {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) (J K : Finset (ℝ × ℂ)) (x : J) (k : K) :
    Tendsto (fun n : ℕ =>
      cov[fun ω => igMixGauss h J 0 ω x, fun ω => igSimGauss h K (z n) (ρ n) ω k; P]) atTop (𝓝 0) := by
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · by_cases hk : 0 < (k : ℝ × ℂ).1
    · have hcov1 : ∀ n : ℕ,
          cov[fun ω => igMixGauss h J 0 ω x, fun ω => igSimGauss h K (z n) (ρ n) ω k; P] =
            incCov ((((2 : ℝ) ^ 0 : ℝ) : ℂ) * (x : ℝ × ℂ).2) ((2 : ℝ) ^ 0 * (x : ℝ × ℂ).1) 0 ((2 : ℝ) ^ 0)
              (z n + ((ρ n : ℝ) : ℂ) * (k : ℝ × ℂ).2) (ρ n * (k : ℝ × ℂ).1) (z n) (ρ n) := by
        intro n
        simp only [igMixGauss, igSimGauss, hx, hk, ↓reduceIte]
        exact covariance_cInc hh (by positivity) (by positivity) (mul_pos (hρ n) hk) (hρ n) _ _ _ _
      have hcov2 : ∀ n : ℕ,
          cov[fun ω => igMixGauss h J 0 ω x, fun ω => igSimGauss h K (z n) (ρ n) ω k; P] =
            incCov (z n + ((ρ n : ℝ) : ℂ) * (k : ℝ × ℂ).2) (ρ n * (k : ℝ × ℂ).1) (z n) (ρ n)
              ((((2 : ℝ) ^ 0 : ℝ) : ℂ) * (x : ℝ × ℂ).2) ((2 : ℝ) ^ 0 * (x : ℝ × ℂ).1) 0 ((2 : ℝ) ^ 0) := by
        intro n
        rw [covariance_comm]
        simp only [igMixGauss, igSimGauss, hx, hk, ↓reduceIte]
        exact covariance_cInc hh (mul_pos (hρ n) hk) (hρ n) (by positivity) (by positivity) _ _ _ _
      simp only [pow_zero, one_mul, Complex.ofReal_one] at hcov1 hcov2
      exact tendsto_of_incCov_far hx (k : ℝ × ℂ).2 hk hρ hz hcov1 hcov2
    · simp [igSimGauss, hk, covariance]
  · simp [igMixGauss, hx, covariance]

end GaussSim

/-! ### Characters of the array and of its distant similarity steps -/

section Char

open LQGMetric LQGMetric.CircleAvg LQGDimension.SegLaw

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field} {u : Ω → ℝ} {γ : ℝ}

/-- **Asymptotically uncorrelated characters at distant centres.** The characters `exp(i(σ a + ⟨s, b⟩))` of the
coordinates of the array of `(h, u)` and `exp(i(2πm a'/(2πχ) + ⟨t, b'⟩))` of the coordinates of its normalized
similarity step `T_n = igSimilarityStep γ z_n ρ_n` are asymptotically uncorrelated when `|z_n| → ∞`. -/
theorem tendsto_igSim_char (hγ : γ ∈ Ioo (0 : ℝ) 2) (hh : IsNormalizedWPGFF h P) (hum : Measurable u)
    (hulaw : P.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h u P)
    {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n) (hz : Tendsto (fun n => ‖z n‖) atTop atTop)
    (J K : Finset (ℝ × ℂ)) (σ : ℝ) (s : J → ℝ) (m : ℤ) (t : K → ℝ) :
    Tendsto (igMixCorr P (fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω)))
      (fun n ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω))))
      (igMixChar σ s) (igMixChar (2 * Real.pi * m / (2 * Real.pi * igChi γ)) t)) atTop (𝓝 0) := by
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hd : 0 < 2 * Real.pi * igChi γ := by
    have := Sec1.igChi_pos hγ.1 hγ.2
    positivity
  set d := 2 * Real.pi * igChi γ with hd_def
  set c : ℝ := 2 * Real.pi * m / d with hc_def
  set A : Ω → ℝ := fun ω => ∑ x, s x * igMixGauss h J 0 ω x with hA_def
  set B : ℕ → Ω → ℝ := fun n ω => ∑ k, t k * igSimGauss h K (z n) (ρ n) ω k with hB_def
  set G : ℕ → Ω → ℝ := fun n => cInc h (ρ n) (z n) 1 0 with hG_def
  have hAs : InGSpan (incProc h) A := inGSpan_sum_igMixGauss J 0 s
  have hBs : ∀ n, InGSpan (incProc h) (B n) := fun n => inGSpan_sum_igSimGauss K (z n) (hρ n) t
  have hGs : ∀ n, InGSpan (incProc h) (G n) := fun n => inGSpan_cInc (hρ n) one_pos (z n) 0
  have hAL : MemLp A 2 P := memLp_of_inGSpan hh.1 hAs
  have hBL : ∀ n, MemLp (B n) 2 P := fun n => memLp_of_inGSpan hh.1 (hBs n)
  have hGL : ∀ n, MemLp (G n) 2 P := fun n => memLp_of_inGSpan hh.1 (hGs n)
  set φ : ℝ → ℂ := fun α => ∫ ω, Complex.exp (((α * u ω : ℝ) : ℂ) * Complex.I) ∂P with hφ_def
  have hφ1 : ∀ α, ‖φ α‖ ≤ 1 := fun α => norm_integral_cexp_le (P := P) fun ω => α * u ω
  -- pointwise forms of the characters
  have hX : ∀ ω, igMixChar σ s (igMixCoord J (igPosCircleProcess (h ω) (u ω))) =
      Complex.exp (((σ * (u ω + circleAvg (h ω) 1 0) + A ω : ℝ) : ℂ) * Complex.I) := by
    intro ω
    rw [igMixCoord_igPosCircleProcess]
    simp only [igMixChar, hA_def, igMixGauss, cInc, pow_zero, one_mul, Complex.ofReal_one]
  have hY : ∀ n ω,
      igMixChar c t (igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) =
        Complex.exp (((c * (u ω + circleAvg (h ω) 1 0) + (B n ω + c * G n ω) : ℝ) : ℂ) *
          Complex.I) := by
    intro n ω
    obtain ⟨k, hk⟩ := exists_igMixCoord_igSimilarityStep γ K (z n) (hρ n) (h ω) (u ω)
    rw [hk]
    simp only [igMixChar]
    have hcd : c * d = 2 * Real.pi * m := by rw [hc_def]; field_simp
    have hsum : (∑ x : K, t x * (if 0 < (x : ℝ × ℂ).1 then
        circleAvg (h ω) (ρ n * (x : ℝ × ℂ).1) (z n + ((ρ n : ℝ) : ℂ) * (x : ℝ × ℂ).2) -
          circleAvg (h ω) (ρ n) (z n) else 0)) = B n ω := rfl
    rw [hsum]
    have hlin : c * (u ω + circleAvg (h ω) (ρ n) (z n) - k * d) + B n ω =
        (c * (u ω + circleAvg (h ω) 1 0) + (B n ω + c * G n ω)) +
          2 * Real.pi * ((-(m * k) : ℤ) : ℝ) := by
      simp only [hG_def, cInc]
      push_cast
      linear_combination (-(k : ℝ)) * hcd
    rw [hlin, cexp_ofReal_add_two_pi_mul_int]
  -- the three integrals
  have I1 : ∫ ω, igMixChar σ s (igMixCoord J (igPosCircleProcess (h ω) (u ω))) ∂P =
      φ σ * ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) :=
    (integral_congr_ae (Eventually.of_forall hX)).trans
      (integral_cexp_phase_add_inGSpan hh hum hind hAs σ)
  have I2 : ∀ n,
      ∫ ω, igMixChar c t (igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) ∂P =
        φ c * ((Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2)) : ℝ) : ℂ) := fun n =>
    (integral_congr_ae (Eventually.of_forall (hY n))).trans
      (integral_cexp_phase_add_inGSpan hh hum hind ((hBs n).add ((hGs n).const_mul c)) c)
  have I12 : ∀ n,
      ∫ ω, igMixChar σ s (igMixCoord J (igPosCircleProcess (h ω) (u ω))) *
        igMixChar c t (igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) ∂P =
        φ (σ + c) * ((Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2)) : ℝ) : ℂ) := by
    intro n
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans
      (integral_cexp_phase_add_inGSpan hh hum hind (hAs.add ((hBs n).add ((hGs n).const_mul c)))
        (σ + c))
    rw [hX, hY n, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hE : ∀ᶠ n in atTop,
      φ (σ + c) * ((Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2)) : ℝ) : ℂ) -
        (φ σ * ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ)) *
          (φ c * ((Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2)) : ℝ) : ℂ)) =
      igMixCorr P (fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω)))
        (fun n ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω))))
        (igMixChar σ s) (igMixChar c t) n := by
    refine Eventually.of_forall fun n => ?_
    simp only [igMixCorr]
    rw [I12 n, I1, I2 n]
  refine Tendsto.congr' hE ?_
  -- the variances of the far increments are constant (law preservation)
  have hΦ : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hh.1.measurable hum
  have hT : ∀ n, MeasurePreserving (igSimilarityStep γ (z n) (ρ n))
      (P.map fun ω => igPosCircleProcess (h ω) (u ω)) (P.map fun ω => igPosCircleProcess (h ω) (u ω)) :=
    fun n => measurePreserving_igSimilarityStep hγ (hρ n) (z n) hh hulaw hind
  set gB : ℝ × (K → ℝ) → ℝ := fun q => ∑ k, t k * q.2 k with hgB_def
  have hgB : Measurable gB :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp measurable_snd)
  set VB : ℝ := Var[gB; (P.map fun ω => igPosCircleProcess (h ω) (u ω)).map (igMixCoord K)]
  have hVB : ∀ n, Var[B n; P] = VB := by
    intro n
    have hYm : Measurable fun ω =>
        igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω))) :=
      (measurable_igMixCoord K).comp ((measurable_igSimilarityStep γ (z n) (ρ n)).comp hΦ)
    have hBY : B n = gB ∘ fun ω =>
        igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω))) := by
      funext ω
      obtain ⟨k, hk⟩ := exists_igMixCoord_igSimilarityStep γ K (z n) (hρ n) (h ω) (u ω)
      simp only [Function.comp_apply, hgB_def]
      rw [hk]
      rfl
    have hlaw : P.map (fun ω =>
        igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) =
        (P.map fun ω => igPosCircleProcess (h ω) (u ω)).map (igMixCoord K) := by
      rw [show (fun ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) =
          (igMixCoord K ∘ igSimilarityStep γ (z n) (ρ n)) ∘ fun ω => igPosCircleProcess (h ω) (u ω) from rfl,
        ← Measure.map_map ((measurable_igMixCoord K).comp (measurable_igSimilarityStep γ (z n) (ρ n))) hΦ,
        ← Measure.map_map (measurable_igMixCoord K) (measurable_igSimilarityStep γ (z n) (ρ n)),
        (hT n).map_eq]
    rw [hBY, ← variance_map hgB.aemeasurable hYm.aemeasurable, hlaw]
  have hVA0 : 0 ≤ Var[A; P] := variance_nonneg _ _
  rcases eq_or_ne m 0 with hm | hm
  · -- the phase frequency vanishes
    have hc0 : c = 0 := by rw [hc_def, hm]; simp
    have hφ0 : φ 0 = 1 := by simp [hφ_def]
    simp only [hc0, zero_mul, add_zero, hφ0, one_mul]
    -- covariance of the near and far increments
    have hC : Tendsto (fun n => cov[A, B n; P]) atTop (𝓝 0) := by
      have hsum : ∀ n, cov[A, B n; P] = ∑ x : J, ∑ k : K,
          s x * t k * cov[fun ω => igMixGauss h J 0 ω x, fun ω => igSimGauss h K (z n) (ρ n) ω k; P] := by
        intro n
        rw [hA_def, hB_def]
        simp only
        rw [covariance_fun_sum_fun_sum
          (fun x => (memLp_of_inGSpan hh.1 (inGSpan_igMixGauss J 0 x)).const_mul (s x))
          (fun k => (memLp_of_inGSpan hh.1 (inGSpan_igSimGauss K (z n) (hρ n) k)).const_mul (t k))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
        rw [covariance_const_mul_left, covariance_const_mul_right]
        ring
      simp only [hsum]
      rw [show (0 : ℝ) = ∑ x : J, ∑ k : K, s x * t k * 0 by simp]
      exact tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun k _ =>
        (tendsto_cov_igSimGauss hh.1 hρ hz J K x k).const_mul _
    have hCn : Tendsto (fun n => -cov[A, B n; P]) atTop (𝓝 0) := by simpa using hC.neg
    have hexpC : Tendsto (fun n => Real.exp (-cov[A, B n; P]) - 1) atTop (𝓝 0) := by
      have := ((Real.continuous_exp.tendsto 0).comp hCn).sub_const 1
      simpa [Function.comp_def] using this
    have hexpA : Tendsto (fun n => |Real.exp (-cov[A, B n; P]) - 1|) atTop (𝓝 0) := by
      simpa using hexpC.abs
    refine squeeze_zero_norm' ?_ hexpA
    refine Eventually.of_forall fun n => ?_
    have hv := variance_add hAL (hBL n)
    have hv' : Var[fun ω => A ω + B n ω; P] = Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P] := hv
    rw [hv']
    have hVB0 : 0 ≤ Var[B n; P] := variance_nonneg _ _
    have hfac : ((Real.exp (-((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2)) : ℝ) : ℂ) -
        ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) * ((Real.exp (-(Var[B n; P] / 2)) : ℝ) : ℂ) =
        ((Real.exp (-(Var[A; P] / 2)) * Real.exp (-(Var[B n; P] / 2)) *
          (Real.exp (-cov[A, B n; P]) - 1) : ℝ) : ℂ) := by
      push_cast
      rw [show -((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2 : ℂ) =
        -(Var[A; P] / 2 : ℂ) + -(Var[B n; P] / 2 : ℂ) + -(cov[A, B n; P] : ℂ) by ring,
        Complex.exp_add, Complex.exp_add]
      ring
    rw [show φ σ * ((Real.exp (-((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2)) : ℝ) : ℂ) -
        φ σ * ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) * ((Real.exp (-(Var[B n; P] / 2)) : ℝ) : ℂ) =
        φ σ * (((Real.exp (-((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2)) : ℝ) : ℂ) -
        ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) * ((Real.exp (-(Var[B n; P] / 2)) : ℝ) : ℂ)) by ring,
      hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have e1 : Real.exp (-(Var[A; P] / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have e2 : Real.exp (-(Var[B n; P] / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hab : 0 ≤ |Real.exp (-cov[A, B n; P]) - 1| := abs_nonneg _
    calc ‖φ σ‖ * (Real.exp (-(Var[A; P] / 2)) * Real.exp (-(Var[B n; P] / 2)) *
          |Real.exp (-cov[A, B n; P]) - 1|)
        ≤ 1 * (1 * 1 * |Real.exp (-cov[A, B n; P]) - 1|) := by
          gcongr
          · exact hφ1 σ
    _ = |Real.exp (-cov[A, B n; P]) - 1| := by ring
  · -- the phase frequency does not vanish: the variance of `h_{ρ_n}(z_n)` diverges
    have hc : c ≠ 0 := by
      rw [hc_def]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.2 hm))
        hd.ne'
    have hW : Tendsto (fun n => Var[G n; P]) atTop atTop := tendsto_variance_cInc_far hh.1 hρ hz
    have hVG : ∀ n : ℕ, Var[fun ω => c * G n ω; P] = c ^ 2 * Var[G n; P] := fun n => by
      rw [variance_const_mul]
    have hlin : ∀ M : ℝ, Tendsto (fun n : ℕ => c ^ 2 * Var[G n; P] / 2 - M) atTop atTop := by
      intro M
      have hpos : 0 < c ^ 2 / 2 := by positivity
      have := (hW.const_mul_atTop hpos).atTop_add (tendsto_const_nhds (x := -M))
      refine this.congr fun n => ?_
      ring
    have hdiv : ∀ V : ℕ → ℝ, (∀ᶠ n in atTop, c ^ 2 * Var[G n; P] / 2 - (2 * Var[A; P] + 2 * VB) ≤ V n) →
        Tendsto (fun n => Real.exp (-(V n / 2))) atTop (𝓝 0) := by
      intro V hV
      have hVt : Tendsto V atTop atTop := tendsto_atTop_mono' atTop hV (hlin _)
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hVt.atTop_div_const two_pos))
    have hlow12 : ∀ᶠ n in atTop, c ^ 2 * Var[G n; P] / 2 - (2 * Var[A; P] + 2 * VB) ≤
        Var[fun ω => A ω + (B n ω + c * G n ω); P] := by
      refine Eventually.of_forall fun n => ?_
      have e : (fun ω => A ω + (B n ω + c * G n ω)) = fun ω => (A ω + B n ω) + c * G n ω := by
        funext ω; ring
      rw [e]
      have h1 : Var[fun ω => c * G n ω; P] / 2 - Var[fun ω => A ω + B n ω; P] ≤
          Var[fun ω => (A ω + B n ω) + c * G n ω; P] :=
        variance_add_ge (P := P) (X := fun ω => A ω + B n ω) (hAL.add (hBL n)) ((hGL n).const_mul c)
      have h2 := variance_add_le (P := P) hAL (hBL n)
      rw [hVG n] at h1
      rw [hVB n] at h2
      linarith
    have hlow2 : ∀ᶠ n in atTop, c ^ 2 * Var[G n; P] / 2 - (2 * Var[A; P] + 2 * VB) ≤
        Var[fun ω => B n ω + c * G n ω; P] := by
      refine Eventually.of_forall fun n => ?_
      have h1 := variance_add_ge (P := P) (hBL n) ((hGL n).const_mul c)
      rw [hVG n, hVB n] at h1
      have hVB0 : 0 ≤ VB := by rw [← hVB n]; exact variance_nonneg _ _
      linarith
    have t12 := hdiv _ hlow12
    have t2 := hdiv _ hlow2
    refine squeeze_zero_norm' ?_ (by simpa using t12.add t2)
    refine Eventually.of_forall fun n => ?_
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc ‖φ (σ + c)‖ * Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2))
          ≤ 1 * Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2)) := by
            gcongr; exact hφ1 _
        _ = _ := one_mul _
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have e1 : Real.exp (-(Var[A; P] / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc ‖φ σ‖ * Real.exp (-(Var[A; P] / 2)) *
            (‖φ c‖ * Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2)))
          ≤ 1 * 1 * (1 * Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2))) := by
            gcongr
            · exact hφ1 _
            · exact hφ1 _
        _ = _ := by ring

end Char

/-! ### Assembly -/

section Assembly

open LQGMetric

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field} {u : Ω → ℝ} {γ : ℝ}

/-- **Asymptotic independence of the cylinder events of the array and of its distant similarity steps.** -/
theorem tendsto_igSim_cyl (hγ : γ ∈ Ioo (0 : ℝ) 2) (hh : IsNormalizedWPGFF h P) (hum : Measurable u)
    (hulaw : P.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h u P)
    {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n) (hz : Tendsto (fun n => ‖z n‖) atTop atTop)
    (J K : Finset (ℝ × ℂ)) {A' : Set (ℝ × (J → ℝ))} {B' : Set (ℝ × (K → ℝ))}
    (hA' : MeasurableSet A') (hB' : MeasurableSet B') :
    Tendsto (fun n : ℕ =>
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' A' ∩
        (fun ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) ⁻¹' B') -
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' A') *
        P.real ((fun ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) ⁻¹'
          B')) atTop (𝓝 0) := by
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hd : 0 < 2 * Real.pi * igChi γ := by
    have := Sec1.igChi_pos hγ.1 hγ.2
    positivity
  set d := 2 * Real.pi * igChi γ with hd_def
  have hΦ : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hh.1.measurable hum
  set μ := P.map fun ω => igPosCircleProcess (h ω) (u ω) with hμ_def
  have hμP : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).mpr inferInstance
  have hT : ∀ n, MeasurePreserving (igSimilarityStep γ (z n) (ρ n)) μ μ := fun n =>
    measurePreserving_igSimilarityStep hγ (hρ n) (z n) hh hulaw hind
  set X : Ω → ℝ × (J → ℝ) := fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω)) with hX_def
  set Y : ℕ → Ω → ℝ × (K → ℝ) :=
    fun n ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω))) with hY_def
  have hXm : Measurable X := (measurable_igMixCoord J).comp hΦ
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (measurable_igMixCoord K).comp ((measurable_igSimilarityStep γ (z n) (ρ n)).comp hΦ)
  have hlawX : P.map X = μ.map (igMixCoord J) := (Measure.map_map (measurable_igMixCoord J) hΦ).symm
  have hlawY : ∀ n, P.map (Y n) = μ.map (igMixCoord K) := fun n => by
    rw [show Y n = (igMixCoord K ∘ igSimilarityStep γ (z n) (ρ n)) ∘ fun ω => igPosCircleProcess (h ω) (u ω)
        from rfl,
      ← Measure.map_map ((measurable_igMixCoord K).comp (measurable_igSimilarityStep γ (z n) (ρ n))) hΦ,
      ← Measure.map_map (measurable_igMixCoord K) (measurable_igSimilarityStep γ (z n) (ρ n)),
      (hT n).map_eq]
  have hphase : ∀ I : Finset (ℝ × ℂ), (μ.map (igMixCoord I)) {p | p.1 ∈ Ico 0 d} = 1 := by
    intro I
    have hfm : MeasurableSet {p : ℝ × (I → ℝ) | p.1 ∈ Ico 0 d} := measurableSet_Ico.preimage measurable_fst
    rw [Measure.map_map (measurable_igMixCoord I) hΦ,
      Measure.map_apply ((measurable_igMixCoord I).comp hΦ) hfm]
    have hset : (igMixCoord I ∘ fun ω => igPosCircleProcess (h ω) (u ω)) ⁻¹' {p | p.1 ∈ Ico 0 d} =
        (fun ω => u ω + circleAvg (h ω) 1 0) ⁻¹' Ico 0 d := by
      ext ω
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_ofPred_eq,
        igMixCoord_igPosCircleProcess]
    have hsm : Measurable fun ω => u ω + circleAvg (h ω) 1 0 :=
      hum.add ((measurable_circleAvg_left 1 0).comp hh.1.measurable)
    rw [hset, ← Measure.map_apply hsm measurableSet_Ico]
    have hae : (fun ω => u ω + circleAvg (h ω) 1 0) =ᵐ[P] u :=
      hh.2.mono fun ω hω => by simp [hω]
    rw [Measure.map_congr hae, hulaw, ProbabilityTheory.cond_apply measurableSet_Ico, Set.inter_self,
      ENNReal.inv_mul_cancel]
    · simp [Real.volume_Ico, hd]
    · simp [Real.volume_Ico]
  have : IsProbabilityMeasure (μ.map (igMixCoord J)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_igMixCoord J).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map (igMixCoord K)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_igMixCoord K).aemeasurable).mpr inferInstance
  have hbJ := tendsto_measureReal_compl_igMixBox (μ.map (igMixCoord J)) (hphase J)
  have hbK := tendsto_measureReal_compl_igMixBox (μ.map (igMixCoord K)) (hphase K)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hLJ, hLK, hL1⟩ : ∃ L₀ : ℕ, (μ.map (igMixCoord J)).real (igMixBox d L₀ J)ᶜ < ε / 8 ∧
      (μ.map (igMixCoord K)).real (igMixBox d L₀ K)ᶜ < ε / 8 ∧ 1 ≤ L₀ :=
    ((hbJ.eventually (gt_mem_nhds (by positivity))).and
      ((hbK.eventually (gt_mem_nhds (by positivity))).and (eventually_ge_atTop 1))).exists
  have hL : (0 : ℝ) < (L₀ : ℝ) := by exact_mod_cast hL1
  set L : ℝ := (L₀ : ℝ) with hL_def
  set Ξ : Ω → UnitAddTorus (Option J) := fun ω => igMixTorus d L J (X ω) with hΞ_def
  set Υ : ℕ → Ω → UnitAddTorus (Option K) := fun n ω => igMixTorus d L K (Y (n + 1) ω) with hΥ_def
  have hΞ : Measurable Ξ := (measurable_igMixTorus d L J).comp hXm
  have hΥ : ∀ n, Measurable (Υ n) := fun n => (measurable_igMixTorus d L K).comp (hYm (n + 1))
  have hlawΥ : ∀ n, P.map (Υ n) = P.map (Υ 0) := fun n => by
    rw [show Υ n = igMixTorus d L K ∘ Y (n + 1) from rfl, show Υ 0 = igMixTorus d L K ∘ Y (0 + 1) from rfl,
      ← Measure.map_map (measurable_igMixTorus d L K) (hYm (n + 1)),
      ← Measure.map_map (measurable_igMixTorus d L K) (hYm (0 + 1)), hlawY, hlawY]
  have hcorr : ∀ f ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Option J))),
      ∀ g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Option K))),
      Tendsto (igMixCorr P Ξ Υ f g) atTop (𝓝 0) := by
    refine tendsto_igMixCorr_span _ _ hΞ hΥ fun a b => ?_
    have h5 := tendsto_igSim_char hγ hh hum hulaw hind hρ hz J K (2 * Real.pi * a none / d)
      (fun x => 2 * Real.pi * a (some x) / (2 * L)) (b none) (fun k => 2 * Real.pi * b (some k) / (2 * L))
    refine (h5.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
    simp only [Function.comp_apply, igMixCorr, hΞ_def, hΥ_def, mFourier_igMixTorus]
    rfl
  have hmain := tendsto_igMixCorr_indicator_of_dense UnitAddTorus.span_mFourier_closure_eq_top
    UnitAddTorus.span_mFourier_closure_eq_top hΞ hΥ hlawΥ hcorr
    ((measurable_igMixSection d L J) hA') ((measurable_igMixSection d L K) hB')
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hmain (ε / 4) (by positivity)
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hNk := hN k (by omega)
  rw [dist_zero_right, igMixCorr_indicator hΞ hΥ ((measurable_igMixSection d L J) hA')
    ((measurable_igMixSection d L K) hB'), Complex.norm_real, Real.norm_eq_abs] at hNk
  rw [Real.dist_eq, sub_zero]
  have hEG : (X ⁻¹' A') ∆ (Ξ ⁻¹' (igMixSection d L J ⁻¹' A')) ⊆ X ⁻¹' (igMixBox d L J)ᶜ := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    intro hbox
    have hsec := igMixSection_igMixTorus hd hL hbox
    simp only [Set.mem_symmDiff, Set.mem_preimage, hΞ_def, hsec] at hω
    tauto
  have hFH : (Y (k + 1) ⁻¹' B') ∆ (Υ k ⁻¹' (igMixSection d L K ⁻¹' B')) ⊆
      Y (k + 1) ⁻¹' (igMixBox d L K)ᶜ := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    intro hbox
    have hsec := igMixSection_igMixTorus hd hL hbox
    simp only [Set.mem_symmDiff, Set.mem_preimage, hΥ_def, hsec] at hω
    tauto
  have hcmp := abs_measureReal_inter_sub_le (P := P) (hXm hA') (hΞ ((measurable_igMixSection d L J) hA'))
    (hYm (k + 1) hB') (hΥ k ((measurable_igMixSection d L K) hB')) hEG hFH
  have hG : P.real (X ⁻¹' (igMixBox d L J)ᶜ) < ε / 8 := by
    rw [measureReal_preimage_eq_map hXm (measurableSet_igMixBox d L J).compl, hlawX]; exact hLJ
  have hH : P.real (Y (k + 1) ⁻¹' (igMixBox d L K)ᶜ) < ε / 8 := by
    rw [measureReal_preimage_eq_map (hYm (k + 1)) (measurableSet_igMixBox d L K).compl, hlawY]; exact hLK
  have habs := abs_sub_abs_le_abs_sub
    (P.real (X ⁻¹' A' ∩ Y (k + 1) ⁻¹' B') - P.real (X ⁻¹' A') * P.real (Y (k + 1) ⁻¹' B'))
    (P.real (Ξ ⁻¹' (igMixSection d L J ⁻¹' A') ∩ Υ k ⁻¹' (igMixSection d L K ⁻¹' B')) -
      P.real (Ξ ⁻¹' (igMixSection d L J ⁻¹' A')) * P.real (Υ k ⁻¹' (igMixSection d L K ⁻¹' B')))
  linarith

/-- **Mixing at distant centres for a measurable phase.** -/
theorem igFieldDistantCentreMixing_of_measurable (hγ : γ ∈ Ioo (0 : ℝ) 2) (hh : IsNormalizedWPGFF h P)
    (hum : Measurable u) (hulaw : P.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)])
    (hind : IndepFun h u P) {z : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) {S₁ S₂ : Set (ℝ × ℂ → ℝ)} (hS₁ : MeasurableSet S₁)
    (hS₂ : MeasurableSet S₂) :
    Tendsto (fun n : ℕ => (P.map fun ω => igPosCircleProcess (h ω) (u ω))
        (S₁ ∩ igSimilarityStep γ (z n) (ρ n) ⁻¹' S₂)) atTop
      (𝓝 ((P.map fun ω => igPosCircleProcess (h ω) (u ω)) S₁ *
        (P.map fun ω => igPosCircleProcess (h ω) (u ω)) S₂)) := by
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hΦ : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hh.1.measurable hum
  set μ := P.map fun ω => igPosCircleProcess (h ω) (u ω) with hμ_def
  have hμP : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).mpr inferInstance
  have hT : ∀ n, MeasurePreserving (igSimilarityStep γ (z n) (ρ n)) μ μ := fun n =>
    measurePreserving_igSimilarityStep hγ (hρ n) (z n) hh hulaw hind
  refine tendsto_measure_inter_preimage_seq_of_isSetRing isSetRing_measurableCylinders
    ⟨{univ}, Set.countable_singleton _, Set.singleton_subset_iff.2 (univ_mem_measurableCylinders _),
      by simp⟩ generateFrom_measurableCylinders.symm hT ?_ hS₁ hS₂
  intro A hA B hB
  obtain ⟨J, SA, hSA, rfl⟩ := (mem_measurableCylinders A).1 hA
  obtain ⟨K, SB, hSB, rfl⟩ := (mem_measurableCylinders B).1 hB
  have hA' : MeasurableSet (igMixRecover J ⁻¹' SA) := measurable_igMixRecover J hSA
  have hB' : MeasurableSet (igMixRecover K ⁻¹' SB) := measurable_igMixRecover K hSB
  have hcylA : cylinder J SA = igMixCoord J ⁻¹' (igMixRecover J ⁻¹' SA) := by
    ext f
    rw [mem_cylinder, Set.mem_preimage, Set.mem_preimage, igMixRecover_igMixCoord]
  have hcylB : cylinder K SB = igMixCoord K ⁻¹' (igMixRecover K ⁻¹' SB) := by
    ext f
    rw [mem_cylinder, Set.mem_preimage, Set.mem_preimage, igMixRecover_igMixCoord]
  have hcAm : MeasurableSet (cylinder J SA : Set (ℝ × ℂ → ℝ)) := by
    rw [hcylA]; exact measurable_igMixCoord J hA'
  have hcBm : MeasurableSet (cylinder K SB : Set (ℝ × ℂ → ℝ)) := by
    rw [hcylB]; exact measurable_igMixCoord K hB'
  have hcore := tendsto_igSim_cyl hγ hh hum hulaw hind hρ hz J K hA' hB'
  have e1 : ∀ n : ℕ, μ.real (cylinder J SA ∩ igSimilarityStep γ (z n) (ρ n) ⁻¹' cylinder K SB) =
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' (igMixRecover J ⁻¹' SA) ∩
        (fun ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) ⁻¹'
          (igMixRecover K ⁻¹' SB)) := fun n => by
    rw [hμ_def, ← measureReal_preimage_eq_map hΦ
      (hcAm.inter ((measurable_igSimilarityStep γ (z n) (ρ n)) hcBm)), hcylA, hcylB]
    rfl
  have e2 : μ.real (cylinder J SA) =
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' (igMixRecover J ⁻¹' SA)) := by
    rw [hμ_def, ← measureReal_preimage_eq_map hΦ hcAm, hcylA]
    rfl
  have e3 : ∀ n : ℕ, μ.real (cylinder K SB) =
      P.real ((fun ω => igMixCoord K (igSimilarityStep γ (z n) (ρ n) (igPosCircleProcess (h ω) (u ω)))) ⁻¹'
        (igMixRecover K ⁻¹' SB)) := fun n => by
    have hpre : μ.real (igSimilarityStep γ (z n) (ρ n) ⁻¹' cylinder K SB) = μ.real (cylinder K SB) := by
      simp only [measureReal_def]
      rw [(hT n).measure_preimage hcBm.nullMeasurableSet]
    rw [← hpre, hμ_def, ← measureReal_preimage_eq_map hΦ ((measurable_igSimilarityStep γ (z n) (ρ n)) hcBm),
      hcylB]
    rfl
  have := hcore.add_const (μ.real (cylinder J SA) * μ.real (cylinder K SB))
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [e1 n, e2, e3 n]
  ring

end Assembly

/-- **Mixing of the whole-plane GFF modulo `2πχ` under similarities with distant centres**
(`IGFieldDistantCentreMixing`: law preservation of each
normalized step, character density, cross covariance uniform in the scale, and `Var h_s(z) ≥ log |z|`-type
divergence of the phase variance). -/
theorem igFieldDistantCentreMixing (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) : IGFieldDistantCentreMixing γ hγ := by
  intro Ω' _ P' h u hh hulaw hind z ρ hρ hz S₁ S₂ hS₁ hS₂
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have huae : AEMeasurable u P' := aemeasurable_of_map_eq_igUniform hulaw
  have hμ : (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) =
      P'.map fun ω => igPosCircleProcess (h ω) (huae.mk u ω) := by
    refine Measure.map_congr ?_
    filter_upwards [huae.ae_eq_mk] with ω hω
    simp only [hω]
  have hulaw' : P'.map (huae.mk u) = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] := by
    rw [← Measure.map_congr huae.ae_eq_mk]
    exact hulaw
  have hind' : IndepFun h (huae.mk u) P' := hind.congr (ae_eq_refl _) huae.ae_eq_mk
  rw [hμ]
  exact igFieldDistantCentreMixing_of_measurable hγ hh huae.measurable_mk hulaw' hind' hρ hz hS₁ hS₂

end MatedCRT
