import MatedCRT.FirstPass.Derived.BindIntegral
import MatedCRT.FirstPass.Derived.AnnealedPathLaw
import MatedCRT.FirstPass.Derived.VertexLawInterpClose
import LatticeProb.Prob.ProbabilityMeasureBorel

/-!
# Weak convergence of the annealed walk laws from the vertex of the origin

Along `ε_n → 0` suppose that the pairs (datum, interpolated quenched walk law) converge weakly to `ν` (the joint
convergence of the identification of subsequential limits) and that the vertex-indexed modulus of the quenched walk
laws is small in probability.  Then the annealed laws `annealedPathLaw S η' ε_n a_n` of the rescaled walks from the
vertex `a^{ε_n}_0` of the origin converge, against every bounded Lipschitz test function `F` of the paths, to the
mixture `originPathLaw ν = ∫ p.2 0 dν(p)` of the laws at the origin of the limit random path law.

* `originPathLaw`, `integral_originPathLaw`.
* `tendsto_integral_annealedPathLaw`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]
variable {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [PolishSpace Data] [BorelSpace Data]

/-- The mixture over a random path law `p.2 : ℂ → Prob(ContinuousPath ℂ)` of its value at the origin. -/
noncomputable def originPathLaw
    (ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))) : Measure (ContinuousPath ℂ) :=
  ν.bind fun p => ((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))

omit [PolishSpace Data] in
theorem measurable_originPathLawKernel :
    Measurable fun p : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
      ((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) := by
  have h1 : Measurable fun p : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
      (p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) :=
    ((continuous_eval_const (0 : ℂ)).comp continuous_snd).measurable
  exact measurable_subtype_coe.comp h1

omit [PolishSpace Data] in
/-- A bounded measurable path functional integrates against `originPathLaw ν` as the mixture of the integrals at
the origin. -/
theorem integral_originPathLaw
    (ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))) [IsProbabilityMeasure ν]
    {F : ContinuousPath ℂ → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    ∫ q, F q ∂(originPathLaw ν) =
      ∫ p, ∫ q, F q ∂((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) ∂ν :=
  integral_bind_of_bounded measurable_originPathLawKernel.aemeasurable
    (ae_of_all _ fun _ => inferInstance) hF hM

/-- For a bounded continuous path functional `F`, `p ↦ ∫ F d(p.2 0)` is a bounded continuous function. -/
noncomputable def originIntegral (F : ContinuousPath ℂ →ᵇ ℝ) :
    (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun p => ∫ q, F q ∂((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)),
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp
        ((continuous_eval_const (0 : ℂ)).comp continuous_snd)⟩ (2 * ‖F‖) (fun p p' => by
    have h : ∀ μ : ProbabilityMeasure (ContinuousPath ℂ),
        |∫ q, F q ∂(μ : Measure (ContinuousPath ℂ))| ≤ ‖F‖ := fun μ => by
      have := norm_integral_le_of_norm_le_const (μ := (μ : Measure (ContinuousPath ℂ))) (f := F)
        (C := ‖F‖) (ae_of_all _ fun q => F.norm_coe_le_norm q)
      simpa [Real.norm_eq_abs] using this
    show dist (∫ q, F q ∂((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)))
      (∫ q, F q ∂((p'.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))) ≤
        2 * ‖F‖
    rw [Real.dist_eq]
    refine le_trans (abs_sub _ _) ?_
    linarith [h (p.2 0), h (p'.2 0)])

omit [MeasurableSpace Data] [PolishSpace Data] [BorelSpace Data] in
theorem originIntegral_apply (F : ContinuousPath ℂ →ᵇ ℝ)
    (p : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) :
    originIntegral F p =
      ∫ q, F q ∂((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) := rfl

omit [PolishSpace Data] in
/-- **The annealed walk laws from the vertex of the origin converge, against bounded Lipschitz test
functionals, to the origin mixture of the limit random path law.** -/
theorem tendsto_integral_annealedPathLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    {a : ℕ → Ω → ℤ} (ha : ∀ n, Measurable (a n))
    (hav : ∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} [IsProbabilityMeasure ν]
    (hconv : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, interpWalkLaw S η' (e n) ω) ∂S.P) atTop (𝓝 (∫ p, f p ∂ν)))
    (F : ContinuousPath ℂ →ᵇ ℝ) {L : ℝ≥0} (hL : LipschitzWith L F) :
    Tendsto (fun n => ∫ q, F q ∂(annealedPathLaw S η' (e n) (a n))) atTop
      (𝓝 (∫ q, F q ∂(originPathLaw ν))) := by
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  set M : ℝ := ‖F‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hM : ∀ x, |F x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm x
  have hF : Measurable F := F.continuous.measurable
  have hFint : ∀ μ : ProbabilityMeasure (ContinuousPath ℂ),
      |∫ q, F q ∂(μ : Measure (ContinuousPath ℂ))| ≤ M := fun μ => by
    have := norm_integral_le_of_norm_le_const (μ := (μ : Measure (ContinuousPath ℂ))) (f := F)
      (C := M) (ae_of_all _ fun q => F.norm_coe_le_norm q)
    simpa [Real.norm_eq_abs] using this
  have hker : ∀ n, Measurable fun ω =>
      walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) (a n ω) ω := by
    intro n
    have hv : Measurable (fun ω => vertexPoint (e n) (⇑(η' ω))) := measurable_vertexPoint_curve hη' (e n)
    have hg : Measurable (fun p : Ω × ℤ =>
        walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) p.2 p.1) :=
      measurable_from_prod_countable_left fun k =>
        measurable_walkPathLaw hS hv (S.mε_nonneg (e n)) (e n) k
    exact hg.comp (measurable_id.prodMk (ha n))
  let u : ℕ → Ω → ℝ := fun n ω => ∫ q, F q ∂(walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω)))
    (S.mε_nonneg (e n)) (e n) (a n ω) ω : Measure (ContinuousPath ℂ))
  let w : ℕ → Ω → ℝ := fun n ω => originIntegral F (D ω, interpWalkLaw S η' (e n) ω)
  have hu : ∀ n, Measurable (u n) := fun n =>
    (measurable_integral_probabilityMeasure_of_boundedContinuous F).comp (hker n)
  have hw : ∀ n, AEMeasurable (w n) S.P := fun n =>
    (originIntegral F).continuous.measurable.comp_aemeasurable
      (hD.aemeasurable.prodMk (aemeasurable_interpWalkLaw hS hη' hae (he0 n)))
  have hubd : ∀ n ω, |u n ω| ≤ M := fun n ω => hFint _
  have hwbd : ∀ n ω, |w n ω| ≤ M := fun n ω => hFint _
  have hui : ∀ n, Integrable (u n) S.P := fun n =>
    Integrable.of_bound (hu n).aestronglyMeasurable M
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hubd n ω)
  have hwi : ∀ n, Integrable (w n) S.P := fun n =>
    Integrable.of_bound (hw n).aestronglyMeasurable M
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hwbd n ω)
  have hA : ∀ n, ∫ q, F q ∂(annealedPathLaw S η' (e n) (a n)) = ∫ ω, u n ω ∂S.P := fun n =>
    integral_bind_of_bounded (measurable_subtype_coe.comp (hker n)).aemeasurable
      (ae_of_all _ fun ω => (walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω)))
        (S.mε_nonneg (e n)) (e n) (a n ω) ω).2) hF hM
  have hR : ∫ q, F q ∂(originPathLaw ν) = ∫ p, originIntegral F p ∂ν := integral_originPathLaw ν hF hM
  have hlim : Tendsto (fun n => ∫ ω, w n ω ∂S.P) atTop (𝓝 (∫ p, originIntegral F p ∂ν)) :=
    hconv (originIntegral F)
  have hdiff : Tendsto (fun n => ∫ ω, u n ω ∂S.P - ∫ ω, w n ω ∂S.P) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set K : ℝ := L + 2 * M with hKdef
    have hK : 0 ≤ K := by positivity
    set b : ℝ := ε / (3 * (K + 1)) with hbdef
    have hb : 0 < b := by positivity
    set τ : ℝ := ε / (3 * (2 * M + 1)) with hτdef
    have hτ : 0 < τ := by positivity
    have hprob := tendsto_prob_pathLP_vertex_interpWalkLaw hS hae he0 he hmod a hav (b := b / 2)
      (by positivity)
    have hev := (ENNReal.tendsto_nhds_zero.1 hprob) (ENNReal.ofReal τ) (ENNReal.ofReal_pos.2 hτ)
    filter_upwards [hev] with n hn
    set Bad : Set Ω := {ω | ENNReal.ofReal (b / 2) < pathLevyProkhorovEDist
      (walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) (a n ω) ω)
      (interpWalkLaw S η' (e n) ω 0)} with hBad
    set B' : Set Ω := toMeasurable S.P Bad with hB'
    have hB'meas : MeasurableSet B' := measurableSet_toMeasurable _ _
    have hB'P : S.P B' = S.P Bad := measure_toMeasurable Bad
    have hpt : ∀ ω, ‖u n ω - w n ω‖ ≤ K * b + 2 * M * B'.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      rw [Real.norm_eq_abs]
      have hKb : 0 ≤ K * b := mul_nonneg hK hb.le
      by_cases hω : ω ∈ B'
      · rw [Set.indicator_of_mem hω]
        have := abs_sub (u n ω) (w n ω)
        have := hubd n ω
        have := hwbd n ω
        linarith [abs_sub (u n ω) (w n ω)]
      · rw [Set.indicator_of_notMem hω]
        have hnb : ω ∉ Bad := fun h => hω (subset_toMeasurable _ _ h)
        have hle : pathLevyProkhorovEDist
            (walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) (a n ω) ω)
            (interpWalkLaw S η' (e n) ω 0) ≤ ENNReal.ofReal (b / 2) := by
          simpa [hBad] using hnb
        have hlt := lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff hb).2 (half_lt_self hb))
        have := abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_lipschitz
          (walkPathLaw S (fun ω => vertexPoint (e n) (⇑(η' ω))) (S.mε_nonneg (e n)) (e n) (a n ω) ω :
            Measure (ContinuousPath ℂ))
          (interpWalkLaw S η' (e n) ω 0 : Measure (ContinuousPath ℂ)) hb hlt F hL
        simpa [hKdef, hMdef, u, w, originIntegral_apply] using this
    have hphi : Integrable (fun ω => K * b + 2 * M * B'.indicator (fun _ => (1 : ℝ)) ω) S.P :=
      (integrable_const _).add
        (((integrable_indicator_iff hB'meas).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _)
    have hint : ∫ ω, (K * b + 2 * M * B'.indicator (fun _ => (1 : ℝ)) ω) ∂S.P =
        K * b + 2 * M * (S.P B').toReal := by
      rw [integral_add (integrable_const _)
        (((integrable_indicator_iff hB'meas).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _),
        integral_const, integral_const_mul, integral_indicator_const _ hB'meas]
      simp [measureReal_def]
    have hbound := norm_integral_le_of_norm_le hphi (ae_of_all _ hpt)
    rw [integral_sub (hui n) (hwi n)] at *
    have hτle : (S.P B').toReal ≤ τ := by
      rw [hB'P]; exact ENNReal.toReal_le_of_le_ofReal hτ.le hn
    have hKb : K * b ≤ ε / 3 := by
      have : K * b = ε / 3 * (K / (K + 1)) := by simp only [hbdef]; field_simp
      rw [this]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    have h2Mτ : 2 * M * τ ≤ ε / 3 := by
      have : 2 * M * τ = ε / 3 * ((2 * M) / (2 * M + 1)) := by simp only [hτdef]; field_simp
      rw [this]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    rw [Real.dist_eq, sub_zero]
    rw [hint] at hbound
    have := mul_le_mul_of_nonneg_left hτle (by positivity : (0 : ℝ) ≤ 2 * M)
    rw [Real.norm_eq_abs] at hbound
    linarith
  have h2 := hdiff.add hlim
  rw [zero_add, ← hR] at h2
  refine h2.congr fun n => ?_
  rw [hA n]
  ring

end MatedCRT.FirstPass.Derived
