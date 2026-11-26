import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonGood
import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonMapping
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# The frozen window laws converge to the chart law of the limiting path law

Deterministic half of the comparison of Berestycki–Gwynne (2020), proof of Lemma 7.21 (written answer MQ-sbl-35,
lines 40-47). Along a sequence of curves `η_l → η`, cell sizes `ε_l → 0` and time scales `m_l → ∞`, let the
interpolated walk laws from the start cell `⌈u/ε_l⌉` converge weakly to a law `K` under which almost every path leaves
`{D ≥ 0}` no later than `{D > 0}`, where `D` is the limit of the signed distances of the windows and `ψ` the limit of
their inverse charts. If each window has an intrinsic chart that agrees with the inverse chart on the window, the curves
visit the window domain during `[a, b]` only, the start cell is inside and the inside rows charge retained labels only,
then the frozen window laws converge weakly to the image of `K` under "stop at the exit from `{D > 0}` and apply `ψ`".

* `MatedCRT.FrozenPath.tendsto_integral_frozenWindowLaw`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

namespace FrozenPath

/-- **The frozen window laws converge to the chart image of the limiting path law** (written answer MQ-sbl-35,
lines 40-47): the extended continuous mapping theorem on the label sequences of the walks, with the convergence of the
frozen chart paths (`tendsto_linPath_frozen`). -/
theorem tendsto_integral_frozenWindowLaw {a u b p q : ℝ} (hbq : b ≤ q)
    {ε : ℕ → ℝ} (hε : ∀ l, 0 < ε l) (hε0 : Tendsto ε atTop (𝓝 0)) (hεa : ∀ l, ε l ≤ a - p)
    {mε : ℕ → ℝ} (hm : ∀ l, 0 ≤ mε l) (hmε : Tendsto mε atTop atTop)
    {ηs : ℕ → C(ℝ, ℂ)} {η : C(ℝ, ℂ)} (hη : Tendsto ηs atTop (𝓝 η))
    {ψ : C(ℂ, ℂ)} (hψ : Tendsto (fun l => windowChartBG a u b (ηs l)) atTop (𝓝 ψ))
    {D : C(ℂ, ℝ)} (hD : Tendsto (fun l => windowGapBG a u b (ηs l)) atTop (𝓝 D))
    (hG : ∀ l, WindowGoodIntr a u b (ηs l)) (hC : ∀ l, ηs l ∈ windowChartCurves a u b)
    (hchart : ∀ l, ∀ x ∈ windowDomain (ηs l) a u b,
      windowChartBG a u b (ηs l) x = windowChartIntr a u b (ηs l) x)
    (hpre : ∀ l t, ηs l t ∈ windowDomain (ηs l) a u b → t ∈ Icc a b)
    (h0 : ∀ l, WindowCellInside a u b p q (ε l) (ηs l) ⌈u / ε l⌉)
    {ms : ℕ → ℤ → ℤ → ℕ}
    (hrow : ∀ l i j, WindowCellInside a u b p q (ε l) (ηs l) i → ms l i j ≠ 0 → WindowRetained p q (ε l) j)
    {μs : ℕ → ProbabilityMeasure (ContinuousPath ℂ)}
    (hμs : ∀ l, (μs l : Measure (ContinuousPath ℂ)) =
      (srwLaw (ms l) ⌈u / ε l⌉).map (interpPathCM (vertexPoint (ε l) ⇑(ηs l)) (hm l)))
    {K : ProbabilityMeasure (ContinuousPath ℂ)} (hK : Tendsto μs atTop (𝓝 K))
    (hcross : ∀ᵐ y ∂(K : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ D w} y ≤ ContinuousPath.exitTime (gapDomain D) y)
    (g : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun l => ∫ x, g x ∂(frozenWindowLaw a u b p q (ε l) (hm l) (ms l) (ηs l) :
        Measure (ContinuousPath ℂ))) atTop
      (𝓝 (∫ y, g (chartStopPath (gapDomain D) ψ y) ∂(K : Measure (ContinuousPath ℂ)))) := by
  classical
  have hrw : ∀ l, ∫ x, g x ∂(frozenWindowLaw a u b p q (ε l) (hm l) (ms l) (ηs l) : Measure (ContinuousPath ℂ)) =
      ∫ x, g (interpPathCM (frozenChartVertex a u b p q (ε l) (ηs l)) (hm l)
        (frozenSeq {j | WindowCellInside a u b p q (ε l) (ηs l) j} x)) ∂srwLaw (ms l) ⌈u / ε l⌉ := by
    intro l
    rw [frozenWindowLaw_eq_map_srwLaw (hm l) (hG l) (h0 l) (hrow l)]
    exact integral_map ((measurable_interpPathCM _ (hm l)).comp (measurable_frozenSeq_const _)).aemeasurable
      g.continuous.measurable.aestronglyMeasurable
  refine Tendsto.congr (fun l => (hrw l).symm) ?_
  have hstart : ∀ l, srwLaw (ms l) ⌈u / ε l⌉ {x : ℕ → ℤ | x 0 = ⌈u / ε l⌉}ᶜ = 0 := fun l => by
    rw [Set.compl_def]
    exact ae_iff.1 (srwLaw_ae_start _ _)
  refine ExtendedMapping.tendsto_integral_comp (lam := fun l => srwLaw (ms l) ⌈u / ε l⌉)
    (I := fun l => interpPathCM (vertexPoint (ε l) ⇑(ηs l)) (hm l))
    (fun l => (measurable_interpPathCM _ (hm l)).aemeasurable) hμs hK
    (good := fun l => {x | x 0 = ⌈u / ε l⌉}) ?_
    (G := fun l x => interpPathCM (frozenChartVertex a u b p q (ε l) (ηs l)) (hm l)
      (frozenSeq {j | WindowCellInside a u b p q (ε l) (ηs l) j} x))
    (fun l => (measurable_interpPathCM _ (hm l)).comp (measurable_frozenSeq_const _))
    (measurable_chartStopPath _ (isOpen_gapDomain D) ψ) ?_ g
  · simp only [hstart]
    exact tendsto_const_nhds
  filter_upwards [hcross] with y hy
  intro k x hk hx hIx
  have hx0 : ∀ l, WindowCellInside a u b p q (ε (k l)) (ηs (k l)) (x l 0) := fun l => by
    have h : x l 0 = ⌈u / ε (k l)⌉ := hx l
    rw [h]
    exact h0 (k l)
  have hfun : ∀ l, (fun i => windowChartBG a u b (ηs (k l)) (vertexPoint (ε (k l)) ⇑(ηs (k l))
      (x l (frozenIdx (fun i => x l i ∈ {j | WindowCellInside a u b p q (ε (k l)) (ηs (k l)) j}) i)))) =
      fun i => frozenChartVertex a u b p q (ε (k l)) (ηs (k l))
        (frozenSeq {j | WindowCellInside a u b p q (ε (k l)) (ηs (k l)) j} (x l) i) := by
    intro l
    funext i
    rw [frozenSeq_eq_comp_frozenIdx]
    have hin : WindowCellInside a u b p q (ε (k l)) (ηs (k l))
        (x l (frozenIdx (fun i => x l i ∈ {j | WindowCellInside a u b p q (ε (k l)) (ηs (k l)) j}) i)) :=
      frozenIdx_mem (In := fun i => x l i ∈ {j | WindowCellInside a u b p q (ε (k l)) (ηs (k l)) j}) (hx0 l) i
    have hmem := (hG (k l)).mem_windowDomain_of_windowCellInside (hε (k l)) hin
      (t := ε (k l) * (x l (frozenIdx (fun i => x l i ∈
        {j | WindowCellInside a u b p q (ε (k l)) (ηs (k l)) j}) i) : ℝ))
      ⟨mul_le_mul_of_nonneg_left (by linarith) (hε (k l)).le, le_rfl⟩
    unfold frozenChartVertex
    rw [ite_eq_left hin]
    exact hchart (k l) _ hmem
  have key := tendsto_linPath_frozen hy (m := fun l => mε (k l))
    (r := fun l => modulusOn (ηs (k l)) p q (ε (k l))) (fun l => hm (k l)) (hmε.comp hk)
    (tendsto_modulusOn (hη.comp hk) (hε0.comp hk) p q)
    (ψk := fun l => windowChartBG a u b (ηs (k l))) (hψ.comp hk)
    (Dk := fun l => windowGapBG a u b (ηs (k l))) (hD.comp hk)
    (P := fun l i => vertexPoint (ε (k l)) ⇑(ηs (k l)) (x l i))
    (In := fun l i => x l i ∈ {j | WindowCellInside a u b p q (ε (k l)) (ηs (k l)) j})
    (hIx.congr fun l => interpPathCM_eq_linPath _ _ _)
    (fun l _ hi => windowGapBG_pos_of_windowCellInside (hG (k l)) (hC (k l)) (hε (k l)) hi)
    (fun l _ hlt => windowCellInside_of_modulusOn_lt (hG (k l)) (hC (k l)) (hε (k l)) (hεa (k l)) hbq
      (hpre (k l)) hlt)
    hx0
  refine key.congr fun l => ?_
  refine (congrArg (fun v => linPath v (hm (k l))) (hfun l)).trans ?_
  exact (interpPathCM_eq_linPath _ (hm (k l)) _).symm

end FrozenPath

end MatedCRT
