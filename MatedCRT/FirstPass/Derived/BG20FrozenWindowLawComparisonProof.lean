import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonInner
import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonEvents
import MatedCRT.FirstPass.Derived.FixedMarginalAdjoin
import MatedCRT.FirstPass.Derived.HN5OfDefinesTimeChange
import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# The frozen window laws are close to the chart laws of the walk

Proof of `BG20FrozenWindowLawComparison` (Berestycki–Gwynne (2020), proof of Lemma 7.21; written answer MQ-sbl-35,
lines 5-49): for the multiplicities of the map, the integral of a bounded continuous path functional against the
frozen window law is close in probability to its integral against the chart law of the window for the interpolated
walk law.

By the subsequence criterion it suffices to treat a subsequence along which the pairs (curve, interpolated walk law)
converge jointly in law (tightness from the uniform-start invariance principle). The chart and the signed distance of
the window, Borel functions of the curve, are adjoined to this joint convergence since the curve has the same law at
every level (`tendsto_integral_comp_prodMk_of_map_fst_eq`). Almost every limiting law family defines a time change of
Brownian motion (the binder `hN5a`), so almost every limiting path crosses the window
(`ae_windowGap_crossing_of_definesTimeChangedBM`). The extended continuous mapping theorem in probability
(`ExtendedMapping.tendsto_measure_le_of_badness`) applies with the badness given by the Lévy–Prokhorov distance of the
walk law from the start cell to the interpolated law at `η(u)` plus the indicator of the bad environments: along the
admissible sequences, the frozen window integrals converge by `tendsto_integral_frozenWindowLaw`, and the chart law
integrals converge by `continuousAt_integral_chartLaw_gapDomain`, both to the integral against the chart image of the
limiting law at `η(u)`.

* `MatedCRT.FrozenPath.tendsto_prob_abs_sub_of_jointLimit`: the comparison along a jointly convergent sequence.
* `MatedCRT.bg20FrozenWindowLawComparison`: `BG20FrozenWindowLawComparison`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open MatedCRT.FirstPass.Derived (walkLawModulus maxCellDiam pathLevyProkhorovEDist)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

namespace FrozenPath

variable {Ω : Type} [MeasurableSpace Ω]

/-- The environments in which the comparison is deterministic: the window is good and contains `η(u)`, the intrinsic
chart agrees with the inverse chart on the window domain, the curve visits the window domain during `[a, b]` only,
adjacent cells meet, and `η'` is the curve. -/
abbrev CompGood (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (a u b : ℝ) (ω : Ω) : Prop :=
  (WindowGoodIntr a u b (η' ω) ∧ η' ω ∈ windowChartCurves a u b ∧
      (∀ x ∈ windowDomain (η' ω) a u b, windowChartBG a u b (η' ω) x = windowChartIntr a u b (η' ω) x) ∧
      η' ω u ∈ windowDomain (η' ω) a u b) ∧
    (∀ t, η' ω t ∈ windowDomain (η' ω) a u b → t ∈ Icc a b) ∧
    (∀ e : ℝ, 0 < e → ∀ j k : ℤ, S.mult e ω j k ≠ 0 → (cell e (S.η ω) j ∩ cell e (S.η ω) k).Nonempty) ∧
    ⇑(η' ω) = S.η ω

/-- `CompGood` at the cell size `ε`, with the start cell inside and `ε ≤ min (a - p) (q - b)`. -/
abbrev CompGoodAt (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (a u b p q ε : ℝ) (ω : Ω) : Prop :=
  CompGood S η' a u b ω ∧ WindowCellInside a u b p q ε (η' ω) ⌈u / ε⌉ ∧ ε ≤ min (a - p) (q - b)

/-- **The comparison along a jointly convergent sequence** (Berestycki–Gwynne (2020), proof of Lemma 7.21; written
answer MQ-sbl-35, lines 5-49). Let the laws of (curve, interpolated walk law at level `ε n`) converge weakly to `ν₀`,
under which almost every law family defines a time change of Brownian motion. Then the difference of the integrals of
`g` against the frozen window law and against the chart law of the window tends to `0` in probability. -/
theorem tendsto_prob_abs_sub_of_jointLimit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hJF : WindowFrontierJordanInput 𝒮)
    (hJ : JordanDomainExteriorRegularity) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hmε : Tendsto (fun n => S.mε (ε n)) atTop atTop)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    {ν₀ : Measure (C(ℝ, ℂ) × PathLawFamily)} [IsProbabilityMeasure ν₀]
    (hconv : ∀ f : (C(ℝ, ℂ) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (η' ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ x, f x ∂ν₀)))
    (hdef : ∀ᵐ x ∂ν₀, DefinesTimeChangedBM x.2)
    {a u b p q : ℝ} (hpa : p < a) (hau : a < u) (hub : u < b) (hbq : b < q)
    (g : ContinuousPath ℂ →ᵇ ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => S.P {ω | δ ≤
      |∫ x, g x ∂(frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n)) (S.mult (ε n) ω) (η' ω) :
          Measure (ContinuousPath ℂ)) -
        ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0) := by
  classical
  have hPP := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  have : PolishSpace C(ℂ, ℝ) := LatticeProb.polishSpace_continuousMap ℂ ℝ
  have : PolishSpace PathLawFamily :=
    LatticeProb.polishSpace_continuousMap ℂ (ProbabilityMeasure (ContinuousPath ℂ))
  -- the curve, the interpolated walk law and the adjoined chart coordinates
  let Fa : C(ℝ, ℂ) → C(ℂ, ℂ) × C(ℂ, ℝ) := fun η => (windowChartBG a u b η, windowGapBG a u b η)
  have hFa : Measurable Fa := (measurable_windowChartBG a u b).prodMk (measurable_windowGapBG a u b)
  let Z : ℕ → Ω → C(ℝ, ℂ) × PathLawFamily := fun n ω => (η' ω, interpWalkLaw S η' (ε n) ω)
  have hZ : ∀ n, AEMeasurable (Z n) S.P := fun n =>
    hη'.aemeasurable.prodMk (aemeasurable_interpWalkLaw hS hη' hae (hε0 n))
  let gr : C(ℝ, ℂ) × PathLawFamily → (C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)) := fun x => (x, Fa x.1)
  have hgr : Measurable gr := measurable_id.prodMk (hFa.comp measurable_fst)
  let I : ℕ → Ω → (C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)) := fun n ω => gr (Z n ω)
  have hI : ∀ n, AEMeasurable (I n) S.P := fun n => hgr.comp_aemeasurable (hZ n)
  have hνP : ∀ n, IsProbabilityMeasure (S.P.map (Z n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hZ n)).2 inferInstance
  let μs : ℕ → ProbabilityMeasure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ))) := fun n =>
    ⟨S.P.map (I n), (Measure.isProbabilityMeasure_map_iff (hI n)).2 inferInstance⟩
  let μ : ProbabilityMeasure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ))) :=
    ⟨ν₀.map gr, (Measure.isProbabilityMeasure_map_iff hgr.aemeasurable).2 inferInstance⟩
  -- the adjoined joint convergence
  have hmarg : ν₀.map Prod.fst = S.P.map η' := FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hη' hconv
  have hνμ : ∀ n, (S.P.map (Z n)).map Prod.fst = S.P.map η' := fun n => by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hZ n)]
    rfl
  have hconv' : ∀ f : (C(ℝ, ℂ) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(S.P.map (Z n))) atTop (𝓝 (∫ x, f x ∂ν₀)) := fun f =>
    (hconv f).congr fun n => (integral_map (hZ n) f.continuous.aestronglyMeasurable).symm
  have hweak : Tendsto μs atTop (𝓝 μ) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
    have h1 : ∀ n, ∫ x, f x ∂(μs n : Measure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)))) =
        ∫ x, f (x, Fa x.1) ∂(S.P.map (Z n)) := fun n => by
      show ∫ x, f x ∂(S.P.map (gr ∘ Z n)) = _
      rw [← AEMeasurable.map_map_of_aemeasurable hgr.aemeasurable (hZ n)]
      exact integral_map hgr.aemeasurable f.continuous.aestronglyMeasurable
    have h2 : ∫ x, f x ∂(μ : Measure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)))) =
        ∫ x, f (x, Fa x.1) ∂ν₀ :=
      integral_map hgr.aemeasurable f.continuous.aestronglyMeasurable
    rw [h2]
    exact (tendsto_integral_comp_prodMk_of_map_fst_eq hνμ hmarg hconv' hFa f).congr fun n => (h1 n).symm
  -- the good environments
  have hGood : ∀ᵐ ω ∂S.P, CompGood S η' a u b ω := by
    filter_upwards [ae_windowGood hγ hγ2 hS hJF hae hau hub, ae_windowDomain_preimage_subset hS hae a u b,
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS, hae] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hnull : S.P {ω | ¬ CompGood S η' a u b ω} = 0 := ae_iff.1 hGood
  -- the badness: Lévy–Prokhorov distance at `η(u)` plus the indicator of the bad environments
  let LPd : ℕ → Ω → ℝ := fun n ω => (pathLevyProkhorovEDist
    (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n) ⌈u / ε n⌉ ω)
    (interpWalkLaw S η' (ε n) ω (η' ω u))).toReal
  let h : ℕ → Ω → ℝ := fun n ω => LPd n ω + if CompGoodAt S η' a u b p q (ε n) ω then 0 else 1
  have hLPd0 : ∀ n ω, 0 ≤ LPd n ω := fun _ _ => ENNReal.toReal_nonneg
  have hind0 : ∀ n ω, (0 : ℝ) ≤ if CompGoodAt S η' a u b p q (ε n) ω then 0 else 1 := fun n ω => by
    split_ifs <;> norm_num
  have hh : ∀ c : ℝ, 0 < c → Tendsto (fun n => S.P {ω | c < h n ω}) atTop (𝓝 0) := by
    intro c hc
    have hA := tendsto_prob_pathLevyProkhorovEDist_ceil hS hη' hae hε0 hε hEqLaw hdiam u (half_pos hc)
    have hB : Tendsto (fun n => S.P {ω | ¬ WindowCellInside a u b p q (ε n) (η' ω) ⌈u / ε n⌉}) atTop (𝓝 0) := by
      refine tendsto_measure_of_ae_eventually_notMem
        (fun n => (hη' (measurableSet_setOf_windowCellInside a u b p q (ε n) ⌈u / ε n⌉)).compl) ?_
      filter_upwards [hGood] with ω hω
      filter_upwards [eventually_windowCellInside_ceil hω.1.1 (hpa.trans hau) (hub.trans hbq) hω.1.2.2.2 hε0 hε]
        with n hn
      exact fun h' => h' hn
    have hsum := hA.add hB
    rw [add_zero] at hsum
    have hsmall : ∀ᶠ n in atTop, ε n ≤ min (a - p) (q - b) :=
      hε.eventually (eventually_le_nhds (lt_min (by linarith) (by linarith)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hsmall] with n hn
    have hsub : {ω | c < h n ω} ⊆ ({ω | ENNReal.ofReal (c / 2) < pathLevyProkhorovEDist
        (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n) ⌈u / ε n⌉ ω)
        (interpWalkLaw S η' (ε n) ω (η' ω u))} ∪
          {ω | ¬ WindowCellInside a u b p q (ε n) (η' ω) ⌈u / ε n⌉}) ∪ {ω | ¬ CompGood S η' a u b ω} := by
      intro ω hω
      have hω' : c < LPd n ω + if CompGoodAt S η' a u b p q (ε n) ω then 0 else 1 := hω
      by_cases hP : CompGoodAt S η' a u b p q (ε n) ω
      · rw [ite_eq_left hP, add_zero] at hω'
        refine Or.inl (Or.inl ?_)
        exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (pathLevyProkhorovEDist_ne_top _ _)).2
          (by linarith)
      · by_cases hg : CompGood S η' a u b ω
        · exact Or.inl (Or.inr fun hin => hP ⟨hg, hin, hn⟩)
        · exact Or.inr hg
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hnull, add_zero]
    exact measure_union_le _ _
  -- almost surely under the limit: the adjoined coordinates are the chart coordinates of the curve, and the law
  -- family defines a time change of Brownian motion
  have hgraph : ∀ᵐ e ∂(μ : Measure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)))), e.2 = Fa e.1.1 := by
    have hmeas : MeasurableSet ((fun e : (C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)) =>
        (e.2, Fa e.1.1)) ⁻¹' diagonal (C(ℂ, ℂ) × C(ℂ, ℝ))) :=
      isClosed_diagonal.measurableSet.preimage
        (measurable_snd.prodMk (hFa.comp (measurable_fst.comp measurable_fst)))
    exact (ae_map_iff hgr.aemeasurable hmeas).2 (ae_of_all _ fun x => rfl)
  have hdtc : ∀ᵐ e ∂(μ : Measure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)))),
      DefinesTimeChangedBM e.1.2 := by
    have hfst : (μ : Measure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)))).map Prod.fst = ν₀ := by
      show (ν₀.map gr).map Prod.fst = ν₀
      rw [Measure.map_map measurable_fst hgr]
      exact Measure.map_id
    have h' : ∀ᵐ x ∂((μ : Measure ((C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)))).map Prod.fst),
        DefinesTimeChangedBM x.2 := by
      rw [hfst]
      exact hdef
    exact ae_of_ae_map measurable_fst.aemeasurable h'
  refine ExtendedMapping.tendsto_measure_le_of_badness (lam := fun _ => S.P) (I := I) hI (μs := μs)
    (fun n => rfl) hweak (h := h) hh
    (G := fun n ω => |∫ x, g x ∂(frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n)) (S.mult (ε n) ω) (η' ω) :
          Measure (ContinuousPath ℂ)) -
        ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|) ?_ hδ
  filter_upwards [hgraph, hdtc] with e he hK
  intro k x hk hsm hIx
  -- the coordinates converge
  have hη : Tendsto (fun l => η' (x l)) atTop (𝓝 e.1.1) :=
    ((continuous_fst.comp continuous_fst).tendsto e).comp hIx
  have hKs : Tendsto (fun l => interpWalkLaw S η' (ε (k l)) (x l)) atTop (𝓝 e.1.2) :=
    ((continuous_snd.comp continuous_fst).tendsto e).comp hIx
  have hψ : Tendsto (fun l => windowChartBG a u b (η' (x l))) atTop (𝓝 e.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto e).comp hIx
  have hD : Tendsto (fun l => windowGapBG a u b (η' (x l))) atTop (𝓝 e.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto e).comp hIx
  have hD2 : e.2.2 = windowGapBG a u b e.1.1 := congrArg Prod.snd he
  -- almost every limiting path from `η(u)` crosses the window
  have hcross : ∀ᵐ y ∂(e.1.2 (e.1.1 u) : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ e.2.2 w} y ≤ ContinuousPath.exitTime (gapDomain e.2.2) y := by
    rw [hD2]
    exact ae_windowGap_crossing_of_definesTimeChangedBM hK hJ a u b e.1.1
  -- eventually the environments are good
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hsm (1 / 2) (by norm_num))
  have hPL : ∀ l, L ≤ l → CompGoodAt S η' a u b p q (ε (k l)) (x l) := fun l hl => by
    by_contra hnP
    have h1 : LPd (k l) (x l) + (if CompGoodAt S η' a u b p q (ε (k l)) (x l) then 0 else 1) ≤ 1 / 2 :=
      hL l hl
    rw [ite_eq_right hnP] at h1
    linarith [hLPd0 (k l) (x l)]
  -- the Lévy–Prokhorov distances tend to `0`
  have hLP : Tendsto (fun l => LPd (k l) (x l)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun c hc => Eventually.of_forall fun l => hc.trans_le (hLPd0 _ _), fun c hc => ?_⟩
    filter_upwards [hsm (c / 2) (by linarith)] with l hl
    have hl' : LPd (k l) (x l) + (if CompGoodAt S η' a u b p q (ε (k l)) (x l) then 0 else 1) ≤ c / 2 := hl
    linarith [hind0 (k l) (x l)]
  -- the walk laws from the start cell converge to the limiting law at `η(u)`
  have hzs : Tendsto (fun l => η' (x l) u) atTop (𝓝 (e.1.1 u)) := ((continuous_eval_const u).tendsto _).comp hη
  have hKz : Tendsto (fun l => interpWalkLaw S η' (ε (k l)) (x l) (η' (x l) u)) atTop
      (𝓝 (e.1.2 (e.1.1 u))) :=
    (continuous_eval.tendsto (e.1.2, e.1.1 u)).comp (hKs.prodMk_nhds hzs)
  have hW : Tendsto (fun l => walkPathLaw S (fun ω => vertexPoint (ε (k l)) (⇑(η' ω))) (S.mε_nonneg (ε (k l)))
      (ε (k l)) ⌈u / ε (k l)⌉ (x l)) atTop (𝓝 (e.1.2 (e.1.1 u))) :=
    tendsto_of_tendsto_pathLevyProkhorovEDist hKz hLP
  -- shift past `L`
  have hL0 : Tendsto (fun l : ℕ => l + L) atTop atTop := tendsto_add_atTop_nat L
  have hks : Tendsto (fun l => k (l + L)) atTop atTop := hk.comp hL0
  have hgood' : ∀ l, CompGood S η' a u b (x (l + L)) := fun l => (hPL _ (Nat.le_add_left L l)).1
  have hin' : ∀ l, WindowCellInside a u b p q (ε (k (l + L))) (η' (x (l + L))) ⌈u / ε (k (l + L))⌉ :=
    fun l => (hPL _ (Nat.le_add_left L l)).2.1
  have hsm' : ∀ l, ε (k (l + L)) ≤ min (a - p) (q - b) := fun l => (hPL _ (Nat.le_add_left L l)).2.2
  -- the frozen window integrals converge
  have hF := tendsto_integral_frozenWindowLaw (a := a) (u := u) (b := b) (p := p) (q := q) hbq.le
    (ε := fun l => ε (k (l + L))) (fun l => hε0 _) (hε.comp hks) (fun l => (hsm' l).trans (min_le_left _ _))
    (mε := fun l => S.mε (ε (k (l + L)))) (fun l => S.mε_nonneg _) (hmε.comp hks)
    (ηs := fun l => η' (x (l + L))) (η := e.1.1) (hη.comp hL0)
    (ψ := e.2.1) (hψ.comp hL0) (D := e.2.2) (hD.comp hL0)
    (fun l => (hgood' l).1.1) (fun l => (hgood' l).1.2.1) (fun l => (hgood' l).1.2.2.1)
    (fun l => (hgood' l).2.1) hin'
    (ms := fun l => S.mult (ε (k (l + L))) (x (l + L)))
    (fun l i j hi hm => windowRetained_of_inter_nonempty (hgood' l).1.1 (hε0 _)
      ((hsm' l).trans (min_le_left _ _)) ((hsm' l).trans (min_le_right _ _)) (hgood' l).2.1 hi
      (by
        have hmeet := (hgood' l).2.2.1 _ (hε0 _) i j hm
        rwa [← (hgood' l).2.2.2] at hmeet))
    (μs := fun l => walkPathLaw S (fun ω => vertexPoint (ε (k (l + L))) (⇑(η' ω))) (S.mε_nonneg _)
      (ε (k (l + L))) ⌈u / ε (k (l + L))⌉ (x (l + L)))
    (fun l => rfl) (hW.comp hL0) hcross g
  -- the chart law integrals converge
  have hBc := continuousAt_integral_chartLaw_gapDomain
    (Kf := fun e : (C(ℝ, ℂ) × PathLawFamily) × (C(ℂ, ℂ) × C(ℂ, ℝ)) => e.1.2) (zf := fun e => e.1.1 u)
    (ψf := fun e => e.2.1) (Df := fun e => e.2.2) (p₀ := e)
    (continuous_snd.comp continuous_fst).continuousAt
    ((continuous_eval_const u).comp (continuous_fst.comp continuous_fst)).continuousAt
    (continuous_fst.comp continuous_snd).continuousAt (continuous_snd.comp continuous_snd).continuousAt
    hcross g
  have hB := (hBc.tendsto.comp hIx).comp hL0
  have hlim : ∫ x, g x ∂chartLaw e.1.2 (e.1.1 u) (gapDomain e.2.2) e.2.1 =
      ∫ y, g (chartStopPath (gapDomain e.2.2) e.2.1 y) ∂(e.1.2 (e.1.1 u) : Measure (ContinuousPath ℂ)) :=
    integral_map (measurable_chartStopPath _ (isOpen_gapDomain _) _).aemeasurable
      g.continuous.aestronglyMeasurable
  have hB' : Tendsto (fun l => ∫ x, g x ∂windowLawBG a u b (η' (x (l + L)))
      (interpWalkLaw S η' (ε (k (l + L))) (x (l + L)))) atTop
      (𝓝 (∫ y, g (chartStopPath (gapDomain e.2.2) e.2.1 y) ∂(e.1.2 (e.1.1 u) : Measure (ContinuousPath ℂ)))) := by
    rw [← hlim]
    refine hB.congr fun l => ?_
    show ∫ x, g x ∂chartLaw (interpWalkLaw S η' (ε (k (l + L))) (x (l + L))) (η' (x (l + L)) u)
      (gapDomain (windowGapBG a u b (η' (x (l + L))))) (windowChartBG a u b (η' (x (l + L)))) = _
    rw [chartLaw_gapDomain_windowGapBG]
  have hdiff := (hF.sub hB').abs
  rw [sub_self, abs_zero] at hdiff
  refine (tendsto_add_atTop_iff_nat L).1 ?_
  exact hdiff

end FrozenPath

/-- **`BG20FrozenWindowLawComparison`** (Berestycki–Gwynne (2020), proof of Lemma 7.21; written answer MQ-sbl-35,
lines 5-49), from the uniform-start invariance principle with the reference environments of the model (`hEnvS`,
`hN4`, `hν`, `href`, `hU`, as in `hN5_of_defines`), the time-change half `hN5a` of Lemma 7.4 of Berestycki–Gwynne, the
Jordan frontier of the window domain (`WindowFrontierJordanInput`) and the regularity of Jordan domains for the exterior
(`JordanDomainExteriorRegularity`). By the subsequence criterion, along a subsequence the pairs (curve, interpolated
walk law) converge jointly in law (tightness, `isTightMeasureSet_data_interpWalkLaw_of_uniformStart_holder`), and
`FrozenPath.tendsto_prob_abs_sub_of_jointLimit` applies. -/
theorem bg20FrozenWindowLawComparison {𝒮 : SpaceFillingSLEModel} (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮) {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν)
    (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hN5a : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, DefinesTimeChangedBM P)
    (hJF : WindowFrontierJordanInput 𝒮) (hJ : JordanDomainExteriorRegularity) :
    BG20FrozenWindowLawComparison 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae ε hε0 hε a u b p q hpa hau hub hbq g δ hδ
  have hPP := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace PathLawFamily :=
    LatticeProb.polishSpace_continuousMap ℂ (ProbabilityMeasure (ContinuousPath ℂ))
  have h213 := FirstPass.Derived.greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hν href hU
  have h214 := FirstPass.Derived.exitTimeUpperBoundStmt_of_greenKernelUpper
    (FirstPass.Derived.greenKernelUpperBoundStmt_of_reference_of_forall_gamma hν href hU)
  have hmε := FirstPass.Derived.tendsto_mε_atTop_of_uniformStart h213 h214 hN4 hγ hγ2 hS hε0 hε
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have he0 : ∀ n, 0 < ε (ns n) := fun n => hε0 _
  have he : Tendsto (fun n => ε (ns n)) atTop (𝓝 0) := hε.comp hns
  have hmeas : ∀ n, AEMeasurable (fun ω => (η' ω, interpWalkLaw S η' (ε (ns n)) ω)) S.P := fun n =>
    hη'.aemeasurable.prodMk (aemeasurable_interpWalkLaw hS hη' hae (he0 n))
  have hprob : ∀ n, IsProbabilityMeasure (S.P.map fun ω => (η' ω, interpWalkLaw S η' (ε (ns n)) ω)) :=
    fun n => (Measure.isProbabilityMeasure_map_iff (hmeas n)).2 inferInstance
  have htight := FirstPass.Derived.isTightMeasureSet_data_interpWalkLaw_of_uniformStart_holder hEnvS hN4 hγ hγ2
    hν href hU hS hη' hae he0 he η' hη'.aemeasurable
  obtain ⟨φ, hφ, ν₀, hν₀, hconv⟩ := LatticeProb.exists_subseq_tendsto_integral_of_isTightMeasureSet
    (fun n => S.P.map fun ω => (η' ω, interpWalkLaw S η' (ε (ns n)) ω))
    (by
      convert htight using 1
      ext p
      simp only [Set.mem_range, Set.mem_ofPred_eq]
      exact exists_congr fun n => eq_comm)
  have hconv' : ∀ f : (C(ℝ, ℂ) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, f (η' ω, interpWalkLaw S η' (ε (ns (φ k))) ω) ∂S.P) atTop
        (𝓝 (∫ x, f x ∂ν₀)) :=
    fun f => (hconv f).congr fun k => integral_map (hmeas _) f.continuous.aestronglyMeasurable
  refine ⟨φ, ?_⟩
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hE0 : ∀ k, 0 < ε (ns (φ k)) := fun k => hε0 _
  have hE : Tendsto (fun k => ε (ns (φ k))) atTop (𝓝 0) := he.comp hφt
  have hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, f (interpWalkLaw S η' (ε (ns (φ k))) ω) ∂S.P) atTop
        (𝓝 (∫ K, f K ∂(ν₀.map Prod.snd))) := fun f => by
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    exact hconv' (f.compContinuous ⟨Prod.snd, continuous_snd⟩)
  have hν₂ : IsProbabilityMeasure (ν₀.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance
  have hdef : ∀ᵐ x ∂ν₀, DefinesTimeChangedBM x.2 :=
    ae_of_ae_map measurable_snd.aemeasurable
      (hN5a γ hγ hγ2 Ω S hS η' hη' hae _ hE0 hE (ν₀.map Prod.snd) hν₂ hlaw)
  exact FrozenPath.tendsto_prob_abs_sub_of_jointLimit hγ hγ2 hS hJF hJ hη' hae hE0 hE
    (hmε.comp (hns.comp hφt))
    (FirstPass.Derived.hEqLaw_of_uniformStart_holder hEnvS hN4 hγ hγ2 hν href hU hS hae hE0 hE)
    (FirstPass.Derived.hdiam_of_isValid hS hae hE) hconv' hdef hpa hau hub hbq g hδ

end MatedCRT
