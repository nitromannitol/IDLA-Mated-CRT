import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Root
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import Mathlib.Probability.Martingale.Convergence

/-!
# Approximation of an invariant functional by a local observation (Lemma A.1 of Gwynne–Miller–Sheffield)

Section 2 of the written proof of Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161, Appendix A), fourth
paragraph: a bounded measurable functional `F` of the circle-average embedding `h` of the `0`-quantum cone, almost
surely invariant under the coordinate changes `h ↦ h(C · + z) + Q log C`, is approximated in `L¹` by the local
observation `J(h, 0) = f(H_0|_{B_a(0)}) 1{0 < a r_1(0) < r_b(0)}` of `ZeroConeLemmaA1Root`.

The area measure of the cone has no atom at `0`, infinite total mass and finite mass on compacts (the first two from
the existence of the capped squares of Lemma A.4, `ZeroConeUniformRootLemmaA4`). Hence `0 < r_1(0)` and
`r_b(0) → ∞`, so that `F(h) = F(H_0)` almost surely. The disc restrictions of `H_0` generate the field σ-algebra, so
Lévy's upward theorem approximates `F(H_0)` by a function of `H_0|_{B_a(0)}`; the radius test is then removed by
taking `b` large.

## Main statements

* `exists_rootObs_approx`: the approximation of `F` by `rootObs γ f b₀ · 0` in `L¹` of the law of the cone.
* `exists_measurable_approx_of_comp`: Lévy's upward theorem for the disc restrictions of a measurable field.
* `ae_originFacts`: almost surely `0 < r_1(0)` and `r_b(0) → ∞` as `b → ∞`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-! ### The mass radius of a locally finite measure of infinite mass -/

section MassRadius

open ZeroConeRoot

/-- Some ball around `z` has mass larger than any finite bound, if the total mass is infinite. -/
theorem exists_ball_gt {ν : Measure ℂ} (htop : ν univ = ⊤) {c : ℝ≥0∞} (hc : c ≠ ⊤) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ c < ν (Metric.ball z r) := by
  have hmono : Monotone fun n : ℕ => Metric.ball z (n : ℝ) := fun m n hmn =>
    Metric.ball_subset_ball (by exact_mod_cast hmn)
  have h := hmono.measure_iUnion (μ := ν)
  rw [Metric.iUnion_ball_nat, htop] at h
  have hlt : c < ⨆ n : ℕ, ν (Metric.ball z n) := by
    rw [← h]
    exact lt_top_iff_ne_top.2 hc
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlt
  exact ⟨(k : ℝ) + 1, by positivity,
    hk.trans_le (measure_mono (Metric.ball_subset_ball (by linarith)))⟩

/-- The mass radius is at least `R` when the ball of radius `R` has mass at most `s` and some ball has mass
larger than `s`. -/
theorem le_massRadius {ν : Measure ℂ} {s R : ℝ} {z : ℂ}
    (hne : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal s < ν (Metric.ball z r))
    (hR : ν (Metric.ball z R) ≤ ENNReal.ofReal s) : R ≤ massRadius ν s z := by
  refine le_csInf hne fun r hr => ?_
  by_contra hlt
  exact absurd (hr.2.trans_le (measure_mono (Metric.ball_subset_ball (not_le.1 hlt).le))) (not_lt.2 hR)

/-- **The mass radii tend to infinity** with the mass, for a measure which is finite on compacts and has infinite
total mass. -/
theorem tendsto_massRadius_natCast {ν : Measure ℂ} (hloc : ∀ K : Set ℂ, IsCompact K → ν K < ⊤)
    (htop : ν univ = ⊤) (z : ℂ) :
    Tendsto (fun n : ℕ => massRadius ν ((n : ℝ) + 1) z) atTop atTop := by
  refine tendsto_atTop.2 fun R => ?_
  have hR'pos : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : ν (Metric.ball z (max R 1)) < ⊤ :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt (hloc _ (isCompact_closedBall z _))
  obtain ⟨n₀, hn₀⟩ := ENNReal.exists_nat_gt hfin.ne
  refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  have hs : ENNReal.ofReal ((n : ℝ) + 1) = (n : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hne := exists_ball_gt htop (c := ENNReal.ofReal ((n : ℝ) + 1)) ENNReal.ofReal_ne_top z
  have hle : ν (Metric.ball z (max R 1)) ≤ ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [hs]
    calc ν (Metric.ball z (max R 1)) ≤ n₀ := hn₀.le
      _ ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
      _ ≤ (n : ℝ≥0∞) + 1 := le_self_add
  exact (le_max_left R 1).trans (le_massRadius hne hle)

/-- **The mass radius is positive** for a measure which is finite on compacts, has no atom at `z` and has infinite
total mass. -/
theorem massRadius_pos {ν : Measure ℂ} (hloc : ∀ K : Set ℂ, IsCompact K → ν K < ⊤) {z : ℂ}
    (h0 : ν {z} = 0) (htop : ν univ = ⊤) {s : ℝ} (hs : 0 < s) : 0 < massRadius ν s z := by
  have hanti : Antitone fun n : ℕ => Metric.ball z (1 / ((n : ℝ) + 1)) := fun m n hmn =>
    Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1))
  have hinter : ⋂ n : ℕ, Metric.ball z (1 / ((n : ℝ) + 1)) = {z} := by
    ext x
    simp only [mem_iInter, Metric.mem_ball, mem_singleton_iff]
    constructor
    · intro h
      by_contra hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.2 hx)
      exact absurd (h n) (not_lt.2 hn.le)
    · rintro rfl n
      rw [dist_self]
      positivity
  have hfin : ∃ n : ℕ, ν (Metric.ball z (1 / ((n : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (hloc _ (isCompact_closedBall z _))).ne⟩
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => measurableSet_ball.nullMeasurableSet) hanti hfin
  rw [hinter, h0] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hs))).exists
  have hne := exists_ball_gt htop (c := ENNReal.ofReal s) ENNReal.ofReal_ne_top z
  exact lt_of_lt_of_le (by positivity) (le_massRadius hne hn.le)

end MassRadius

/-! ### The capped squares give an atomless measure of infinite mass -/

section CappedSquares

open ZeroConeRoot
open LatticeProb.DyadicOffset (dyadicSquares IsOffGrid)
open LatticeProb.CappedSquare (IsCappedSquare)

/-- The existence of the capped squares of all positive masses forces `ν {0} = 0`. -/
theorem measure_singleton_zero_of_capped {ν : Measure ℂ} {q : DyCoord}
    (hcap : ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ S, IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) m 0 S) : ν {0} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  obtain ⟨S, hS⟩ := hcap ε (ENNReal.coe_ne_zero.2 hε.ne') ENNReal.coe_ne_top
  calc ν {0} ≤ ν S := measure_mono (singleton_subset_iff.2 hS.mem)
    _ ≤ ε := hS.mass_le
    _ = 0 + ε := (zero_add _).symm

/-- The existence of the capped squares of all positive masses, at an off-grid origin, forces `ν univ = ∞`: a finite
total mass would make every square of the chain at the origin admissible for the mass `ν univ + 1`. -/
theorem measure_univ_eq_top_of_capped {ν : Measure ℂ} (hν : ∀ K : Set ℂ, IsCompact K → ν K < ⊤)
    {q : DyCoord} (hw : IsOffGrid q.1 q.2.1 q.2.2 0)
    (hcap : ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ S, IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (⇑ν) m 0 S) : ν univ = ⊤ := by
  by_contra hne
  have hm0 : ν univ + 1 ≠ 0 := by simp
  have hmt : ν univ + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hne, ENNReal.one_ne_top⟩
  obtain ⟨S, hS⟩ := hcap _ hm0 hmt
  have hspec := (rootGen_spec hν hw hS).1
  have hmem : rootGen ν q (ν univ + 1) + 1 ∈ {j : ℤ | chainMass ν q j ≤ ν univ + 1} := by
    show chainMass ν q _ ≤ _
    rw [chainMass, sqMass_eq hν]
    exact (measure_mono (subset_univ _)).trans le_self_add
  have := hspec.2 hmem
  omega

/-- **The area measure is atomless at `0` and has infinite mass**, almost surely: the (A.2) clause of Lemma A.4. -/
theorem ae_mass_facts {μ : Measure Field} [IsProbabilityMeasure μ] {M : Field → Measure ℂ}
    (hloc : ∀ᵐ h ∂μ, ∀ K : Set ℂ, IsCompact K → M h K < ⊤)
    (hA2 : ∀ᵐ p ∂μ.prod uniformDyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ S, IsCappedSquare (dyadicSquares p.2.1 p.2.2.1 p.2.2.2) (⇑(M p.1)) m 0 S) :
    ∀ᵐ h ∂μ, M h {0} = 0 ∧ M h univ = ⊤ := by
  have hgood := ae_goodPair hloc hA2
  filter_upwards [Measure.ae_ae_of_ae_prod hgood] with h hh
  obtain ⟨q, hq⟩ := hh.exists
  exact ⟨measure_singleton_zero_of_capped hq.2.2, measure_univ_eq_top_of_capped hq.1 hq.2.1 hq.2.2⟩

end CappedSquares

/-! ### The normalization at the origin -/

/-- The mass radius `r_s(0)` of the area measure of a field. -/
def originRadius (γ s : ℝ) (h : Field) : ℝ :=
  ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) s 0

/-- The field `H_0 = h(r_1(0) · ) + Q log r_1(0)` normalized at the mass radius `r_1(0)`, extended by the identity
when `r_1(0) ≤ 0`. -/
def originField (γ : ℝ) (h : Field) : Field :=
  lqgSimilarityAction γ (originRadius γ 1 h, 0) h

theorem measurable_originRadius (γ s : ℝ) : Measurable (originRadius γ s) := by
  have hg : Measurable fun h : Field => (h, (0 : ℂ)) := measurable_id.prodMk measurable_const
  have h3 := (measurable_massRadius_areaMap γ s).comp hg
  simp only [Function.comp_def] at h3
  exact h3

theorem measurable_originField (γ : ℝ) : Measurable (originField γ) := by
  have hg : Measurable fun h : Field => ((originRadius γ 1 h, (0 : ℂ)), h) :=
    ((measurable_originRadius γ 1).prodMk measurable_const).prodMk measurable_id
  have h3 := (measurable_lqgSimilarityAction γ).comp hg
  simp only [Function.comp_def] at h3
  exact h3

theorem rootField_zero_eq_originField (γ : ℝ) {h : Field} (hpos : 0 < originRadius γ 1 h) :
    rootField γ h 0 = originField γ h :=
  (lqgSimilarityAction_of_pos γ (t := (originRadius γ 1 h, 0)) hpos h).symm

/-- **Almost surely `0 < r_1(0)` and `r_b(0) → ∞`**, for the circle-average embedding of the `0`-quantum cone. -/
theorem ae_originFacts (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ)
    (hP : IsProbabilityMeasure P') (hX : LQGMetric.IsWholePlaneGFF X₀' P') (hb : IsBrownianReal b P')
    (hb' : IsBrownianReal b' P')
    (hXbb : IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P')
    (hbb' : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P')
    (hA4 : ZeroConeUniformRootLemmaA4 γ hγ) :
    ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')), 0 < originRadius γ 1 h ∧
      Tendsto (fun n : ℕ => originRadius γ ((n : ℝ) + 1) h) atTop atTop := by
  have hHm : AEMeasurable (zeroConeFieldOf γ X₀' b b') P' :=
    ZeroConeRoot.aemeasurable_zeroConeFieldOf γ hX hb hb' hbb'
  have : IsProbabilityMeasure (P'.map (zeroConeFieldOf γ X₀' b b')) :=
    (Measure.isProbabilityMeasure_map_iff hHm).2 hP
  have hQ : (0 : ℝ) < MatedCRTHarmonic.CellScaling.lqgQ γ := MatedCRTHarmonic.LQGCoord.lqgQ_pos hγ.1
  have hgoodω : ∀ᵐ ω ∂P', zeroConeFieldOf γ X₀' b b' ω ∈ ConeAreaCovariance.goodSet γ :=
    ConeAreaCovariance.ae_coneField_mem_goodSet hγ.1 hγ.2 hQ hX hb hb'
  have hgoodμ : ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), h ∈ ConeAreaCovariance.goodSet γ :=
    (ae_map_iff hHm (ConeAreaCovariance.measurableSet_goodSet γ)).2 hgoodω
  have hMv := hgoodμ.mono fun h hh => (ConeAreaCovariance.areaMap_spec hγ.1.ne' hh).1
  obtain ⟨hA2, -⟩ := hA4 P' X₀' b b' hP hX hb hb' hXbb hbb' (ConeAreaCovariance.areaMap γ)
    (ConeAreaCovariance.measurable_areaMap γ) hMv
  have hloc := hMv.mono fun _ hh => hh.1
  filter_upwards [ae_mass_facts hloc hA2, hloc] with h h1 h2
  exact ⟨massRadius_pos h2 h1.1 h1.2 one_pos, tendsto_massRadius_natCast h2 h1.2 0⟩

/-! ### Lévy's upward theorem for the disc restrictions -/

/-- **The disc restrictions generate the field σ-algebra**: a map into the fields is measurable for the supremum of
the σ-algebras of its restrictions to the discs `B_n(0)`, since every test function has compact support. -/
theorem measurable_iSup_fieldSigma {Ω : Type} (H : Ω → Field) :
    Measurable[⨆ n : ℕ, LQGMetric.Blueprint.fieldSigma H (a1Ball n)] H := by
  let _ : MeasurableSpace Ω := ⨆ n : ℕ, LQGMetric.Blueprint.fieldSigma H (a1Ball n)
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  obtain ⟨r, hr⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℂ)
  have hsub : tsupport (φ : ℂ → ℝ) ⊆ (a1Ball ⌈r⌉₊ : Set ℂ) :=
    hr.trans (Metric.ball_subset_ball (Nat.le_ceil r))
  exact (LQGMetric.GM.measurable_pair_fieldSigma H φ hsub).mono
    (le_iSup (fun n : ℕ => LQGMetric.Blueprint.fieldSigma H (a1Ball n)) ⌈r⌉₊) le_rfl

theorem a1Ball_mono {m n : ℕ} (hmn : m ≤ n) : a1Ball m ≤ a1Ball n :=
  Metric.ball_subset_ball (by exact_mod_cast hmn)

/-- Clamping to `[0, K]` does not increase the distance to a point of `[0, K]`. -/
theorem abs_sub_clamp_le {g K : ℝ} (hg0 : 0 ≤ g) (hgK : g ≤ K) (c : ℝ) :
    |g - max 0 (min K c)| ≤ |g - c| := by
  rcases le_total c 0 with hc | hc
  · have h1 : min K c ≤ 0 := (min_le_right _ _).trans hc
    rw [max_eq_left h1, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total c K with hcK | hcK
    · rw [min_eq_right hcK, max_eq_right hc]
    · rw [min_eq_left hcK, max_eq_right (hg0.trans hgK), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith

/-- **Lévy's upward theorem for the disc restrictions of a measurable field**: a measurable function `G` of
the field `H` is approximated in `L¹` by a function `f` of the restriction of `H` to a disc `B_a(0)`, with
`0 ≤ f ≤ K`. -/
theorem exists_measurable_approx_of_comp {μ : Measure Field} [IsProbabilityMeasure μ] {H : Field → Field}
    (hH : Measurable H) {G : Field → ℝ} (hG : Measurable G) {K : ℝ} (hG0 : ∀ h, 0 ≤ G h)
    (hGK : ∀ h, G h ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℕ) (f : LQGMetric.DistOn (a1Ball a) → ℝ), Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ K) ∧
      ∫ h, |G (H h) - f (LQGMetric.restrictTo (a1Ball a) (H h))| ∂μ ≤ δ := by
  have hK : 0 ≤ K := (hG0 0).trans (hGK 0)
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Field) :=
    { seq := fun n => LQGMetric.Blueprint.fieldSigma H (a1Ball n)
      mono' := fun _ _ hmn => LQGMetric.GM.fieldSigma_mono H (a1Ball_mono hmn)
      le' := fun n => ((LQGMetric.measurable_restrictTo (a1Ball n)).comp hH).comap_le }
  have hg : Integrable (fun h => G (H h)) μ :=
    integrable_of_abs_le (hG.comp hH) (K := K) fun h => by
      rw [abs_of_nonneg (hG0 _)]
      exact hGK _
  have hsup : StronglyMeasurable[⨆ n, ℱ n] fun h => G (H h) :=
    (hG.comp (measurable_iSup_fieldSigma H)).stronglyMeasurable
  have hconv := Integrable.tendsto_eLpNorm_condExp (ℱ := ℱ) hg hsup
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hconv).2 _ (ENNReal.ofReal_pos.2 hδ)).exists
  have hcm : Measurable[MeasurableSpace.comap
      (fun h => LQGMetric.restrictTo (a1Ball N) (H h)) inferInstance]
      (μ[fun h => G (H h) | ℱ N]) := stronglyMeasurable_condExp.measurable
  obtain ⟨f₀, hf₀m, hf₀⟩ := Measurable.exists_eq_measurable_comp hcm
  refine ⟨N, fun x => max 0 (min K (f₀ x)), measurable_const.max (measurable_const.min hf₀m),
    fun x => le_max_left _ _, fun x => max_le hK (min_le_left _ _), ?_⟩
  have hc : Integrable (μ[fun h => G (H h) | ℱ N]) μ := integrable_condExp
  have hdiff : Integrable (fun h => ‖(μ[fun h => G (H h) | ℱ N]) h - G (H h)‖) μ :=
    (hc.sub hg).norm
  have hlt : ∫ h, ‖(μ[fun h => G (H h) | ℱ N]) h - G (H h)‖ ∂μ < δ := by
    have h1 := ofReal_integral_norm_eq_lintegral_enorm (hc.sub hg)
    rw [← eLpNorm_one_eq_lintegral_enorm (hc.sub hg).aestronglyMeasurable] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 (lt_of_eq_of_lt h1 hN)
  have hfm : Measurable fun h => |G (H h) - max 0 (min K (f₀ (LQGMetric.restrictTo (a1Ball N) (H h))))| :=
    (((hG.comp hH).sub ((measurable_const.max (measurable_const.min hf₀m)).comp
      ((LQGMetric.measurable_restrictTo (a1Ball N)).comp hH)))).abs
  refine le_trans (integral_mono (integrable_of_abs_le hfm (K := K) fun h => ?_) hdiff fun h => ?_) hlt.le
  · rw [abs_abs, abs_le]
    have h0 := hG0 (H h)
    have h1 := hGK (H h)
    have h2 : 0 ≤ max 0 (min K (f₀ (LQGMetric.restrictTo (a1Ball N) (H h)))) := le_max_left _ _
    have h3 : max 0 (min K (f₀ (LQGMetric.restrictTo (a1Ball N) (H h)))) ≤ K :=
      max_le hK (min_le_left _ _)
    constructor <;> linarith
  · have hch : (μ[fun h => G (H h) | ℱ N]) h = f₀ (LQGMetric.restrictTo (a1Ball N) (H h)) :=
      congrFun hf₀ h
    show |G (H h) - max 0 (min K (f₀ (LQGMetric.restrictTo (a1Ball N) (H h))))| ≤
      ‖(μ[fun h => G (H h) | ℱ N]) h - G (H h)‖
    rw [hch, Real.norm_eq_abs,
      abs_sub_comm (f₀ (LQGMetric.restrictTo (a1Ball N) (H h))) (G (H h))]
    exact abs_sub_clamp_le (hG0 _) (hGK _) _

/-! ### The approximation by the local observation -/

/-- The approximation by the local observation, from the almost sure facts about the normalization at the
origin. -/
theorem exists_rootObs_approx_aux (γ : ℝ) {μ : Measure Field} [IsProbabilityMeasure μ] {F : Field → ℝ}
    (hFm : Measurable F) {K : ℝ} (hF0 : ∀ h, 0 ≤ F h) (hFK : ∀ h, F h ≤ K)
    (hfacts : ∀ᵐ h ∂μ, 0 < originRadius γ 1 h ∧
      Tendsto (fun n : ℕ => originRadius γ ((n : ℝ) + 1) h) atTop atTop)
    (hFH : ∀ᵐ h ∂μ, F (originField γ h) = F h ∨ ¬ 0 < originRadius γ 1 h) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : ℕ) (f : LQGMetric.DistOn (a1Ball a) → ℝ) (b₀ : ℝ), 1 ≤ b₀ ∧ Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, f x ≤ K) ∧ ∫ h, |F h - rootObs γ f b₀ h 0| ∂μ ≤ ε := by
  classical
  have hK : 0 ≤ K := (hF0 0).trans (hFK 0)
  -- the approximation by a function of the restriction to a disc
  obtain ⟨a, f, hfm, hf0, hfK, hlevy⟩ := exists_measurable_approx_of_comp
    (μ := μ) (measurable_originField γ) hFm hF0 hFK (half_pos hε)
  -- removing the radius test
  let As : ℕ → Set Field := fun n =>
    {h | originRadius γ ((n : ℝ) + 1) h ≤ (a : ℝ) * originRadius γ 1 h}
  have hAs : ∀ n, MeasurableSet (As n) := fun n =>
    measurableSet_le (measurable_originRadius γ _) ((measurable_originRadius γ 1).const_mul _)
  have hlim : ∀ᵐ h ∂μ, ∀ᶠ n : ℕ in atTop, h ∈ As n ↔ h ∈ (∅ : Set Field) := by
    filter_upwards [hfacts] with h hh
    filter_upwards [hh.2.eventually_gt_atTop ((a : ℝ) * originRadius γ 1 h)] with n hn
    simp only [As, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hn
  have hmeas := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := μ) atTop
    MeasurableSet.empty hAs hlim
  rw [measure_empty] at hmeas
  have hδ : 0 < ε / (2 * (K + 1)) := by positivity
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hmeas).2 _ (ENNReal.ofReal_pos.2 hδ)).exists
  have hAn : K * (μ (As n)).toReal ≤ ε / 2 := by
    have h1 : (μ (As n)).toReal ≤ ε / (2 * (K + 1)) := ENNReal.toReal_le_of_le_ofReal hδ.le hn.le
    calc K * (μ (As n)).toReal ≤ K * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK
      _ ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  refine ⟨a, f, (n : ℝ) + 1, by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], hfm, hf0, hfK, ?_⟩
  -- the pointwise comparison
  have hobs_m : Measurable fun h : Field => rootObs γ f ((n : ℝ) + 1) h 0 := by
    have hg : Measurable fun h : Field => (h, (0 : ℂ)) := measurable_id.prodMk measurable_const
    have h3 := (measurable_rootObs γ hfm ((n : ℝ) + 1)).comp hg
    simp only [Function.comp_def] at h3
    exact h3
  have hLm : Measurable fun h : Field => |F h - rootObs γ f ((n : ℝ) + 1) h 0| :=
    (hFm.sub hobs_m).abs
  have hLint : Integrable (fun h : Field => |F h - rootObs γ f ((n : ℝ) + 1) h 0|) μ := by
    refine integrable_of_abs_le hLm (K := K) fun h => ?_
    have h0 := rootObs_nonneg γ hf0 ((n : ℝ) + 1) h 0
    have h1 := rootObs_le γ hfK hK ((n : ℝ) + 1) h 0
    have h2 := hF0 h
    have h3 := hFK h
    rw [abs_abs, abs_le]
    constructor <;> linarith
  have hfm' : Measurable fun h : Field => |F (originField γ h) -
      f (LQGMetric.restrictTo (a1Ball a) (originField γ h))| :=
    ((hFm.comp (measurable_originField γ)).sub
      (hfm.comp ((LQGMetric.measurable_restrictTo (a1Ball a)).comp (measurable_originField γ)))).abs
  have hRint : Integrable (fun h : Field => |F (originField γ h) -
      f (LQGMetric.restrictTo (a1Ball a) (originField γ h))|) μ := by
    refine integrable_of_abs_le hfm' (K := K) fun h => ?_
    have h0 := hf0 (LQGMetric.restrictTo (a1Ball a) (originField γ h))
    have h1 := hfK (LQGMetric.restrictTo (a1Ball a) (originField γ h))
    have h2 := hF0 (originField γ h)
    have h3 := hFK (originField γ h)
    rw [abs_abs, abs_le]
    constructor <;> linarith
  have hIint : Integrable ((As n).indicator fun _ : Field => K) μ := (integrable_const K).indicator (hAs n)
  have hpt : ∀ᵐ h ∂μ, |F h - rootObs γ f ((n : ℝ) + 1) h 0| ≤
      |F (originField γ h) - f (LQGMetric.restrictTo (a1Ball a) (originField γ h))| +
        (As n).indicator (fun _ : Field => K) h := by
    filter_upwards [hfacts, hFH] with h hh hinvh
    have hpos := hh.1
    have hinvh' : F (originField γ h) = F h := hinvh.resolve_right (not_not.2 hpos)
    by_cases ht : RootTest γ a ((n : ℝ) + 1) h 0
    · have hob : rootObs γ f ((n : ℝ) + 1) h 0 =
          f (LQGMetric.restrictTo (a1Ball a) (originField γ h)) := by
        simp only [rootObs, ht, ↓reduceIte, rootField_zero_eq_originField γ hpos]
      rw [hob, hinvh']
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => hK) _)
    · have hob : rootObs γ f ((n : ℝ) + 1) h 0 = 0 := by
        simp only [rootObs, ht, ↓reduceIte]
      have hmem : h ∈ As n := by
        have : ¬ (a : ℝ) * originRadius γ 1 h < originRadius γ ((n : ℝ) + 1) h :=
          fun hlt => ht ⟨hpos, hlt⟩
        exact not_lt.1 this
      rw [hob, indicator_of_mem hmem, sub_zero, abs_of_nonneg (hF0 h)]
      exact (hFK h).trans (le_add_of_nonneg_left (abs_nonneg _))
  have hsum : Integrable (fun h : Field =>
      |F (originField γ h) - f (LQGMetric.restrictTo (a1Ball a) (originField γ h))| +
        (As n).indicator (fun _ : Field => K) h) μ := hRint.add hIint
  have h1 : ∫ h, |F h - rootObs γ f ((n : ℝ) + 1) h 0| ∂μ ≤
      ∫ h, (|F (originField γ h) - f (LQGMetric.restrictTo (a1Ball a) (originField γ h))| +
        (As n).indicator (fun _ : Field => K) h) ∂μ := integral_mono_ae hLint hsum hpt
  have h2 : ∫ h, (|F (originField γ h) - f (LQGMetric.restrictTo (a1Ball a) (originField γ h))| +
        (As n).indicator (fun _ : Field => K) h) ∂μ =
      ∫ h, |F (originField γ h) - f (LQGMetric.restrictTo (a1Ball a) (originField γ h))| ∂μ +
        ∫ h, (As n).indicator (fun _ : Field => K) h ∂μ := integral_add hRint hIint
  have h3 : ∫ h, (As n).indicator (fun _ : Field => K) h ∂μ ≤ ε / 2 := by
    rw [integral_indicator_const K (hAs n), smul_eq_mul, mul_comm]
    exact hAn
  linarith

/-- **The approximation of an invariant functional by the local observation at the origin** (answer 58, §2,
fourth paragraph): a bounded non-negative measurable functional `F` of the circle-average embedding of the
`0`-quantum cone, almost surely invariant under the coordinate changes `h ↦ h(C · + z) + Q log C`, is approximated in
`L¹` by `J(·, 0) = f(H_0|_{B_a(0)}) 1{0 < a r_1(0) < r_{b₀}(0)}` for some `a`, `b₀ ≥ 1` and a bounded measurable
`f`. -/
theorem exists_rootObs_approx (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ)
    (hP : IsProbabilityMeasure P') (hX : LQGMetric.IsWholePlaneGFF X₀' P') (hb : IsBrownianReal b P')
    (hb' : IsBrownianReal b' P')
    (hXbb : IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P')
    (hbb' : IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P')
    (hA4 : ZeroConeUniformRootLemmaA4 γ hγ) {F : Field → ℝ} (hFm : Measurable F) {K : ℝ}
    (hF0 : ∀ h, 0 ≤ F h) (hFK : ∀ h, F h ≤ K)
    (hinv : ∀ᵐ ω ∂P', ∀ C : ℝ, 0 < C → ∀ z : ℂ,
      F (lqgSimilarityField γ C z (zeroConeFieldOf γ X₀' b b' ω)) = F (zeroConeFieldOf γ X₀' b b' ω))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : ℕ) (f : LQGMetric.DistOn (a1Ball a) → ℝ) (b₀ : ℝ), 1 ≤ b₀ ∧ Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, f x ≤ K) ∧ ∫ h, |F h - rootObs γ f b₀ h 0| ∂(P'.map (zeroConeFieldOf γ X₀' b b')) ≤ ε := by
  classical
  have hHm : AEMeasurable (zeroConeFieldOf γ X₀' b b') P' :=
    ZeroConeRoot.aemeasurable_zeroConeFieldOf γ hX hb hb' hbb'
  have : IsProbabilityMeasure (P'.map (zeroConeFieldOf γ X₀' b b')) :=
    (Measure.isProbabilityMeasure_map_iff hHm).2 hP
  have hfacts := ae_originFacts γ hγ P' X₀' b b' hP hX hb hb' hXbb hbb' hA4
  -- invariance at the normalization `r_1(0)`
  have hS : MeasurableSet {h : Field | F (originField γ h) = F h ∨ ¬ 0 < originRadius γ 1 h} :=
    (measurableSet_eq_fun (hFm.comp (measurable_originField γ)) hFm).union
      (measurableSet_lt measurable_const (measurable_originRadius γ 1)).compl
  have hFH : ∀ᵐ h ∂(P'.map (zeroConeFieldOf γ X₀' b b')),
      F (originField γ h) = F h ∨ ¬ 0 < originRadius γ 1 h := by
    refine (ae_map_iff hHm hS).2 ?_
    filter_upwards [hinv] with ω hω
    by_cases hpos : 0 < originRadius γ 1 (zeroConeFieldOf γ X₀' b b' ω)
    · left
      have := hω _ hpos 0
      rwa [← lqgSimilarityAction_of_pos γ (t := (originRadius γ 1 (zeroConeFieldOf γ X₀' b b' ω), 0))
        hpos] at this
    · right
      exact hpos
  exact exists_rootObs_approx_aux γ hFm hF0 hFK hfacts hFH hε

end MatedCRT
