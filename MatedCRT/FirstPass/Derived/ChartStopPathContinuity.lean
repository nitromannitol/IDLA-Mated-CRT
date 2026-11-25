import MatedCRT.FirstPass.Derived.HN9OfChartLaws
import LatticeProb.Topology.PolishContinuousMap

/-!
# Continuity of the chart image of a path stopped at its exit from `{D > 0}`

For a continuous function `D : ℂ → ℝ`, a continuous map `ψ : ℂ → ℂ` and a path `x`, `chartStopPath {D > 0} ψ x` is
`ψ ∘ x(· ∧ τ)`, `τ` the exit time of `x` from the open set `{D > 0}`. Reading the open set off a continuous function
lets it vary (locally uniformly) together with the chart and the path.

* `continuous_exitClamp`: the time change `t ↦ t ∧ τ` depends continuously on `τ ∈ [0, ∞]`.
* `continuousAt_pathExitTime_Ioi`: the first time `inf {t : g t ≤ 0}` of a continuous real function `g` depends
  continuously on `g` (locally uniform convergence) as soon as `g` crosses: its first negative time is at most its
  first nonpositive time.
* `continuousAt_chartStopPath_gapDomain`: hence `(D, ψ, x) ↦ chartStopPath {D > 0} ψ x` is continuous at every
  `(D, ψ, x)` at which the exit time of `x` from `{D ≥ 0}` is at most its exit time from `{D > 0}`;
  `measurable_chartStopPath_gapDomain`: this map is Borel.
* `tendsto_integral_comp_of_ae_tendsto`: the extended continuous mapping theorem with an exceptional null set
  (Billingsley, *Convergence of Probability Measures*, Theorem 5.5): if `μ n → μ` weakly and `fs n y → f x` as
  `(n, y) → (∞, x)` for `μ`-almost every `x`, then the image laws converge weakly.
* `tendsto_integral_chartLaw_gapDomain`: the chart laws `chartLaw K z {D > 0} ψ` converge weakly along convergent
  sequences of `(K, z, ψ, D)` when almost every path under the limiting law `K z` crosses.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

/-! ### The clamp `t ↦ t ∧ τ` -/

theorem exitClamp_apply_eq_toNNReal (τ : ℝ≥0∞) (t : ℝ≥0) :
    exitClamp τ t = (min (t : ℝ≥0∞) τ).toNNReal := by
  rw [exitClamp_apply]
  by_cases hτ : τ = ⊤
  · subst hτ
    simp
  · simp only [hτ, ↓reduceIte]
    obtain ⟨s, rfl⟩ : ∃ s : ℝ≥0, (s : ℝ≥0∞) = τ := ⟨τ.toNNReal, ENNReal.coe_toNNReal hτ⟩
    rw [ENNReal.toNNReal_coe, ← ENNReal.coe_min, ENNReal.toNNReal_coe]

/-- **The clamp `t ↦ t ∧ τ` depends continuously on `τ ∈ [0, ∞]`** (compact-open topology). -/
theorem continuous_exitClamp : Continuous exitClamp := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : (Function.uncurry fun (τ : ℝ≥0∞) (t : ℝ≥0) => exitClamp τ t) =
      fun p : ℝ≥0∞ × ℝ≥0 => (min (p.2 : ℝ≥0∞) p.1).toNNReal :=
    funext fun p => exitClamp_apply_eq_toNNReal p.1 p.2
  rw [h]
  exact ENNReal.continuousOn_toNNReal.comp_continuous
    ((ENNReal.continuous_coe.comp continuous_snd).min continuous_fst)
    fun p => show min (p.2 : ℝ≥0∞) p.1 ≠ ⊤ from ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)

/-! ### Exit times of general paths -/

namespace GapExit

variable {α : Type*}

theorem pathExitTime_le_of_notMem {U : Set α} {f : ℝ≥0 → α} {t : ℝ≥0} (h : f t ∉ U) :
    pathExitTime U f ≤ t :=
  sInf_le ⟨t, rfl, h⟩

theorem mem_of_lt_pathExitTime {U : Set α} {f : ℝ≥0 → α} {t : ℝ≥0}
    (h : (t : ℝ≥0∞) < pathExitTime U f) : f t ∈ U := by
  by_contra hf
  exact absurd (pathExitTime_le_of_notMem hf) (not_le.2 h)

theorem le_pathExitTime_of_forall_mem {U : Set α} {f : ℝ≥0 → α} {a : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < a → f t ∈ U) : a ≤ pathExitTime U f := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  by_contra hlt
  exact ht (h t (not_le.1 hlt))

theorem exists_lt_of_pathExitTime_lt {U : Set α} {f : ℝ≥0 → α} {a : ℝ≥0∞}
    (h : pathExitTime U f < a) : ∃ t : ℝ≥0, (t : ℝ≥0∞) < a ∧ f t ∉ U := by
  unfold pathExitTime at h
  obtain ⟨_, ⟨t, rfl, ht⟩, hta⟩ := sInf_lt_iff.1 h
  exact ⟨t, hta, ht⟩

end GapExit

/-! ### The first nonpositive time of a continuous real function -/

/-- The continuous real functions positive on `[0, u]` form an open set (locally uniform convergence). -/
theorem isOpen_setOf_forall_Icc_pos (u : ℝ≥0) :
    IsOpen {h : C(ℝ≥0, ℝ) | ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < h s} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hg' : ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < g s := hg
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le) g.continuous.continuousOn
  have hmin' := isMinOn_iff.1 hmin
  have hm : 0 < g t₀ := hg' t₀ ht₀
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (tendsto_id : Tendsto (id : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) (𝓝 g) (𝓝 g)) (Icc 0 u) isCompact_Icc
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu (g t₀) hm] with h hh
  show ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < h s
  intro s hs
  have h1 : dist (g s) (h s) < g t₀ := hh s hs
  have h2 : g t₀ ≤ g s := hmin' s hs
  rw [Real.dist_eq] at h1
  have h3 := (abs_lt.1 h1).2
  linarith

/-- The first nonpositive time of a continuous real function is a Borel function of the function. -/
theorem measurable_pathExitTime_Ioi :
    Measurable fun h : C(ℝ≥0, ℝ) => pathExitTime (Ioi (0 : ℝ)) ⇑h := by
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top =>
    rw [Ioi_top, preimage_empty]
    exact MeasurableSet.empty
  | coe t =>
    have heq : (fun h : C(ℝ≥0, ℝ) => pathExitTime (Ioi (0 : ℝ)) ⇑h) ⁻¹' Ioi (t : ℝ≥0∞) =
        ⋃ u : {u : ℝ≥0 // t < u}, {h : C(ℝ≥0, ℝ) | ∀ s ∈ Icc (0 : ℝ≥0) (u : ℝ≥0), 0 < h s} := by
      ext h
      rw [mem_preimage, mem_Ioi, mem_iUnion]
      constructor
      · intro hlt
        obtain ⟨u, htu, hu⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
        refine ⟨⟨u, ENNReal.coe_lt_coe.1 htu⟩, ?_⟩
        show ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < h s
        intro s hs
        exact GapExit.mem_of_lt_pathExitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) hu)
      · rintro ⟨⟨u, htu⟩, hu⟩
        have hu' : ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < h s := hu
        refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 htu)
          (GapExit.le_pathExitTime_of_forall_mem fun s hs => ?_)
        exact hu' s ⟨zero_le, ENNReal.coe_le_coe.1 hs.le⟩
    rw [heq]
    exact (isOpen_iUnion fun u : {u : ℝ≥0 // t < u} => isOpen_setOf_forall_Icc_pos (u : ℝ≥0)).measurableSet

/-- The first negative time of a continuous real function is a Borel function of the function. -/
theorem measurable_pathExitTime_Ici :
    Measurable fun h : C(ℝ≥0, ℝ) => pathExitTime (Ici (0 : ℝ)) ⇑h := by
  refine measurable_of_Ici fun a => ?_
  have heq : (fun h : C(ℝ≥0, ℝ) => pathExitTime (Ici (0 : ℝ)) ⇑h) ⁻¹' Ici a =
      ⋂ t : {t : ℝ≥0 // (t : ℝ≥0∞) < a}, {h : C(ℝ≥0, ℝ) | 0 ≤ h t} := by
    ext h
    rw [mem_preimage, mem_Ici, mem_iInter]
    constructor
    · intro ha t
      exact GapExit.mem_of_lt_pathExitTime (lt_of_lt_of_le t.2 ha)
    · intro h'
      exact GapExit.le_pathExitTime_of_forall_mem fun t ht => h' ⟨t, ht⟩
  rw [heq]
  refine IsClosed.measurableSet (isClosed_iInter fun t => ?_)
  exact isClosed_le continuous_const
    (continuous_eval_const (t : ℝ≥0) : Continuous fun h : C(ℝ≥0, ℝ) => h (t : ℝ≥0))

/-- **Continuity of the first nonpositive time at a crossing.** If the first negative time of the continuous real
function `g` is at most its first nonpositive time, then the first nonpositive time is continuous at `g` for locally
uniform convergence. -/
theorem continuousAt_pathExitTime_Ioi {g : C(ℝ≥0, ℝ)}
    (hcross : pathExitTime (Ici (0 : ℝ)) ⇑g ≤ pathExitTime (Ioi (0 : ℝ)) ⇑g) :
    ContinuousAt (fun h : C(ℝ≥0, ℝ) => pathExitTime (Ioi (0 : ℝ)) ⇑h) g := by
  show Tendsto (fun h : C(ℝ≥0, ℝ) => pathExitTime (Ioi (0 : ℝ)) ⇑h) (𝓝 g)
    (𝓝 (pathExitTime (Ioi (0 : ℝ)) ⇑g))
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨u, hau, huτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hg : ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < g s := fun s hs =>
      GapExit.mem_of_lt_pathExitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) huτ)
    filter_upwards [(isOpen_setOf_forall_Icc_pos u).mem_nhds hg] with h hh
    have hh' : ∀ s ∈ Icc (0 : ℝ≥0) u, 0 < h s := hh
    refine lt_of_lt_of_le hau (GapExit.le_pathExitTime_of_forall_mem fun s hs => ?_)
    exact hh' s ⟨zero_le, ENNReal.coe_le_coe.1 hs.le⟩
  · obtain ⟨t, hta, ht⟩ := GapExit.exists_lt_of_pathExitTime_lt (lt_of_le_of_lt hcross ha)
    have hneg : g t < 0 := not_le.1 (show ¬ (0 ≤ g t) from ht)
    filter_upwards [((continuous_eval_const t).tendsto g).eventually (eventually_lt_nhds hneg)] with h hh
    have hh' : ¬ (0 < h t) := not_lt.2 (le_of_lt hh)
    exact lt_of_le_of_lt (GapExit.pathExitTime_le_of_notMem (U := Ioi (0 : ℝ)) (f := ⇑h) (t := t) hh') hta

/-! ### The open set `{D > 0}` and the stopped chart path -/

/-- The open set `{z : 0 < D z}` of a continuous function `D`. -/
def gapDomain (D : C(ℂ, ℝ)) : Set ℂ := {z | 0 < D z}

theorem isOpen_gapDomain (D : C(ℂ, ℝ)) : IsOpen (gapDomain D) :=
  isOpen_lt continuous_const D.continuous

/-- The exit time of a path from `{D > 0}` is the first nonpositive time of `D ∘ x`. -/
theorem exitTime_gapDomain (D : C(ℂ, ℝ)) (x : ContinuousPath ℂ) :
    ContinuousPath.exitTime (gapDomain D) x = pathExitTime (Ioi (0 : ℝ)) ⇑(D.comp x) :=
  rfl

/-- The exit time of a path from `{D ≥ 0}` is the first negative time of `D ∘ x`. -/
theorem exitTime_setOf_nonneg (D : C(ℂ, ℝ)) (x : ContinuousPath ℂ) :
    ContinuousPath.exitTime {z | 0 ≤ D z} x = pathExitTime (Ici (0 : ℝ)) ⇑(D.comp x) :=
  rfl

theorem chartStopPath_gapDomain (D : C(ℂ, ℝ)) (ψ : C(ℂ, ℂ)) (x : ContinuousPath ℂ) :
    chartStopPath (gapDomain D) ψ x =
      ψ.comp (x.comp (exitClamp (pathExitTime (Ioi (0 : ℝ)) ⇑(D.comp x)))) :=
  rfl

/-- **Continuity of the stopped chart path at a crossing.** If the exit time of the path `x` from `{D ≥ 0}` is at most
its exit time from `{D > 0}`, then `(D, ψ, x) ↦ ψ ∘ x(· ∧ τ_{D > 0}(x))` is continuous at `(D, ψ, x)` (compact-open
topologies). -/
theorem continuousAt_chartStopPath_gapDomain {D : C(ℂ, ℝ)} {ψ : C(ℂ, ℂ)} {x : ContinuousPath ℂ}
    (hcross : ContinuousPath.exitTime {z | 0 ≤ D z} x ≤ ContinuousPath.exitTime (gapDomain D) x) :
    ContinuousAt (fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      chartStopPath (gapDomain p.1.1) p.1.2 p.2) ((D, ψ), x) := by
  have hc : Continuous fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ => p.1.1.comp p.2 :=
    ContinuousMap.continuous_comp'.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))
  have hcross' : pathExitTime (Ici (0 : ℝ)) ⇑(D.comp x) ≤ pathExitTime (Ioi (0 : ℝ)) ⇑(D.comp x) :=
    (exitTime_setOf_nonneg D x).symm.trans_le (hcross.trans_eq (exitTime_gapDomain D x))
  have hσ : ContinuousAt (fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      pathExitTime (Ioi (0 : ℝ)) ⇑(p.1.1.comp p.2)) ((D, ψ), x) :=
    ContinuousAt.comp (g := fun h : C(ℝ≥0, ℝ) => pathExitTime (Ioi (0 : ℝ)) ⇑h)
      (f := fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ => p.1.1.comp p.2)
      (continuousAt_pathExitTime_Ioi hcross') hc.continuousAt
  have hcl : ContinuousAt (fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      p.2.comp (exitClamp (pathExitTime (Ioi (0 : ℝ)) ⇑(p.1.1.comp p.2)))) ((D, ψ), x) :=
    ContinuousMap.continuous_comp'.continuousAt.comp
      ((continuous_exitClamp.continuousAt.comp hσ).prodMk continuousAt_snd)
  have hfin : ContinuousAt (fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      p.1.2.comp (p.2.comp (exitClamp (pathExitTime (Ioi (0 : ℝ)) ⇑(p.1.1.comp p.2))))) ((D, ψ), x) :=
    ContinuousMap.continuous_comp'.continuousAt.comp
      (hcl.prodMk (continuous_snd.comp continuous_fst).continuousAt)
  have heq : (fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      chartStopPath (gapDomain p.1.1) p.1.2 p.2) = fun p =>
      p.1.2.comp (p.2.comp (exitClamp (pathExitTime (Ioi (0 : ℝ)) ⇑(p.1.1.comp p.2)))) :=
    funext fun p => chartStopPath_gapDomain p.1.1 p.1.2 p.2
  rw [heq]
  exact hfin

/-- The exit time of the path from `{D > 0}` is a Borel function of `(D, x)`. -/
theorem measurable_exitTime_gapDomain :
    Measurable fun p : C(ℂ, ℝ) × ContinuousPath ℂ => ContinuousPath.exitTime (gapDomain p.1) p.2 := by
  have : PolishSpace C(ℂ, ℝ) := LatticeProb.polishSpace_continuousMap ℂ ℝ
  have hc : Continuous fun p : C(ℂ, ℝ) × ContinuousPath ℂ => p.1.comp p.2 :=
    ContinuousMap.continuous_comp'.comp continuous_swap
  exact measurable_pathExitTime_Ioi.comp hc.measurable

/-- The exit time of the path from `{D ≥ 0}` is a Borel function of `(D, x)`. -/
theorem measurable_exitTime_setOf_nonneg :
    Measurable fun p : C(ℂ, ℝ) × ContinuousPath ℂ => ContinuousPath.exitTime {z | 0 ≤ p.1 z} p.2 := by
  have : PolishSpace C(ℂ, ℝ) := LatticeProb.polishSpace_continuousMap ℂ ℝ
  have hc : Continuous fun p : C(ℂ, ℝ) × ContinuousPath ℂ => p.1.comp p.2 :=
    ContinuousMap.continuous_comp'.comp continuous_swap
  exact measurable_pathExitTime_Ici.comp hc.measurable

/-- **The stopped chart path is a Borel function of `(D, ψ, x)`.** -/
theorem measurable_chartStopPath_gapDomain :
    Measurable fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      chartStopPath (gapDomain p.1.1) p.1.2 p.2 := by
  have : PolishSpace C(ℂ, ℝ) := LatticeProb.polishSpace_continuousMap ℂ ℝ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  have : PolishSpace (ContinuousPath ℂ) := LatticeProb.polishSpace_continuousMap ℝ≥0 ℂ
  have hτ : Measurable fun p : (C(ℂ, ℝ) × C(ℂ, ℂ)) × ContinuousPath ℂ =>
      ContinuousPath.exitTime (gapDomain p.1.1) p.2 :=
    measurable_exitTime_gapDomain.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h1 : Continuous fun q : (C(ℂ, ℂ) × ContinuousPath ℂ) × ℝ≥0∞ => q.1.2.comp (exitClamp q.2) :=
    ContinuousMap.continuous_comp'.comp
      ((continuous_exitClamp.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst))
  have hG : Continuous fun q : (C(ℂ, ℂ) × ContinuousPath ℂ) × ℝ≥0∞ =>
      q.1.1.comp (q.1.2.comp (exitClamp q.2)) :=
    ContinuousMap.continuous_comp'.comp (h1.prodMk (continuous_fst.comp continuous_fst))
  exact hG.measurable.comp (((measurable_snd.comp measurable_fst).prodMk measurable_snd).prodMk hτ)

/-! ### The extended continuous mapping theorem with an exceptional null set -/

section ExtendedMapping

variable {E T : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E]
  [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] [TopologicalSpace.PseudoMetrizableSpace T]

omit [MeasurableSpace T] [OpensMeasurableSpace T] [TopologicalSpace.PseudoMetrizableSpace T] in
/-- **The closed-set half of the extended continuous mapping theorem.** If `μs n → μ` weakly and, for `μ`-almost
every `x`, `fs n y → f x` as `(n, y) → (∞, x)`, then `limsup (μs n) (fs n ⁻¹' F) ≤ μ (f ⁻¹' F)` for closed `F`. -/
theorem limsup_measure_preimage_le_of_ae_tendsto {μ : ProbabilityMeasure E} {μs : ℕ → ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : E → T} {fs : ℕ → E → T}
    (hc : ∀ᵐ x ∂(μ : Measure E), Tendsto (fun p : ℕ × E => fs p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (f x)))
    {F : Set T} (hF : IsClosed F) :
    limsup (fun n => (μs n : Measure E) (fs n ⁻¹' F)) atTop ≤ (μ : Measure E) (f ⁻¹' F) := by
  set B : ℕ → Set E := fun k => closure (⋃ n ∈ Ici k, fs n ⁻¹' F)
  have hBclosed : ∀ k, IsClosed (B k) := fun k => isClosed_closure
  have hBanti : Antitone B := by
    intro k l hkl
    exact closure_mono (iUnion₂_subset fun n hn => subset_iUnion₂_of_subset n (le_trans hkl hn) le_rfl)
  have hstep : ∀ k, limsup (fun n => (μs n : Measure E) (fs n ⁻¹' F)) atTop ≤ (μ : Measure E) (B k) := by
    intro k
    have hev : ∀ᶠ n in atTop, (μs n : Measure E) (fs n ⁻¹' F) ≤ (μs n : Measure E) (B k) := by
      filter_upwards [eventually_ge_atTop k] with n hn
      exact measure_mono (le_trans (subset_iUnion₂_of_subset n hn le_rfl) subset_closure)
    calc limsup (fun n => (μs n : Measure E) (fs n ⁻¹' F)) atTop
        ≤ limsup (fun n => (μs n : Measure E) (B k)) atTop := limsup_le_limsup hev
      _ ≤ (μ : Measure E) (B k) := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hBclosed k)
  set Z : Set E := {x | ¬ Tendsto (fun p : ℕ × E => fs p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (f x))}
  have hZnull : (μ : Measure E) Z = 0 := ae_iff.1 hc
  have hinter : (⋂ k, B k) ⊆ f ⁻¹' F ∪ Z := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact Or.inr hxZ
    · left
      have hT : Tendsto (fun p : ℕ × E => fs p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
        by_contra h
        exact hxZ h
      by_contra hxF
      have hev := hT.eventually (hF.isOpen_compl.mem_nhds hxF)
      obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_prod_iff.1 hev
      obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 hs
      have hxB : x ∈ B N := mem_iInter.1 hx N
      obtain ⟨y, hyt, hyU⟩ := mem_closure_iff_nhds.1 hxB t ht
      obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 hyU
      have hmem : (n, y) ∈ s ×ˢ t := ⟨hN n hn, hyt⟩
      have hout : fs n y ∉ F := hst hmem
      exact hout hyn
  have hmeas : ∀ k, NullMeasurableSet (B k) (μ : Measure E) :=
    fun k => (hBclosed k).measurableSet.nullMeasurableSet
  have htend : Tendsto (fun k => (μ : Measure E) (B k)) atTop (𝓝 ((μ : Measure E) (⋂ k, B k))) :=
    tendsto_measure_iInter_atTop hmeas hBanti ⟨0, measure_ne_top _ _⟩
  have hle : (μ : Measure E) (⋂ k, B k) ≤ (μ : Measure E) (f ⁻¹' F) :=
    (measure_mono hinter).trans ((measure_union_le _ _).trans (by rw [hZnull, add_zero]))
  exact le_trans (ge_of_tendsto htend (Eventually.of_forall hstep)) hle

omit [TopologicalSpace.PseudoMetrizableSpace T] in
/-- **The extended continuous mapping theorem with an exceptional null set** (Billingsley, *Convergence of
Probability Measures*, Theorem 5.5). If `μs n → μ` weakly, the maps `fs n, f` are Borel and `fs n y → f x` as
`(n, y) → (∞, x)` for `μ`-almost every `x`, then `∫ g ∘ fs n dμs n → ∫ g ∘ f dμ` for every bounded continuous `g`. -/
theorem tendsto_integral_comp_of_ae_tendsto {μ : ProbabilityMeasure E} {μs : ℕ → ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : E → T} {fs : ℕ → E → T} (hfs : ∀ n, Measurable (fs n))
    (hf : Measurable f)
    (hc : ∀ᵐ x ∂(μ : Measure E), Tendsto (fun p : ℕ × E => fs p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (f x)))
    (g : T →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, g (fs n x) ∂(μs n : Measure E)) atTop (𝓝 (∫ x, g (f x) ∂(μ : Measure E))) := by
  let ν : ProbabilityMeasure T :=
    ⟨(μ : Measure E).map f, (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance⟩
  let νs : ℕ → ProbabilityMeasure T := fun n =>
    ⟨(μs n : Measure E).map (fs n), (Measure.isProbabilityMeasure_map_iff (hfs n).aemeasurable).2 inferInstance⟩
  have hopen : ∀ U : Set T, IsOpen U →
      (ν : Measure T) U ≤ liminf (fun n => (νs n : Measure T) U) atTop := by
    intro U hU
    refine le_measure_liminf_of_limsup_measure_compl_le hU.measurableSet ?_
    have hkey := limsup_measure_preimage_le_of_ae_tendsto hμ hc (isClosed_compl_iff.2 hU)
    have hc' : ∀ n, (νs n : Measure T) Uᶜ = (μs n : Measure E) (fs n ⁻¹' Uᶜ) :=
      fun n => Measure.map_apply (hfs n) hU.measurableSet.compl
    simp only [hc']
    exact hkey.trans_eq (Measure.map_apply hf hU.measurableSet.compl).symm
  have hweak : Tendsto νs atTop (𝓝 ν) := tendsto_of_forall_isOpen_le_liminf' hopen
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak g
  have hL : ∀ n, ∫ t, g t ∂(νs n : Measure T) = ∫ x, g (fs n x) ∂(μs n : Measure E) := fun n =>
    integral_map (hfs n).aemeasurable g.continuous.measurable.aestronglyMeasurable
  have hR : ∫ t, g t ∂(ν : Measure T) = ∫ x, g (f x) ∂(μ : Measure E) :=
    integral_map hf.aemeasurable g.continuous.measurable.aestronglyMeasurable
  simpa only [hL, hR] using hint

end ExtendedMapping

/-! ### Convergence of the chart laws -/

/-- **Weak convergence of the chart laws at a crossing.** Let `K n → K₀` (locally uniformly in the starting point),
`z n → z₀`, `ψ n → ψ₀` and `D n → D₀` (locally uniformly), and assume that almost every path under the law `K₀ z₀`
leaves `{D₀ ≥ 0}` no later than `{D₀ > 0}`. Then the chart laws `chartLaw (K n) (z n) {D n > 0} (ψ n)` converge weakly
to `chartLaw K₀ z₀ {D₀ > 0} ψ₀`. -/
theorem tendsto_integral_chartLaw_gapDomain {K : ℕ → PathLawFamily} {K₀ : PathLawFamily}
    (hK : Tendsto K atTop (𝓝 K₀)) {z : ℕ → ℂ} {z₀ : ℂ} (hz : Tendsto z atTop (𝓝 z₀))
    {ψ : ℕ → C(ℂ, ℂ)} {ψ₀ : C(ℂ, ℂ)} (hψ : Tendsto ψ atTop (𝓝 ψ₀))
    {D : ℕ → C(ℂ, ℝ)} {D₀ : C(ℂ, ℝ)} (hD : Tendsto D atTop (𝓝 D₀))
    (hcross : ∀ᵐ x ∂(K₀ z₀ : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ D₀ w} x ≤ ContinuousPath.exitTime (gapDomain D₀) x)
    (g : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, g x ∂chartLaw (K n) (z n) (gapDomain (D n)) (ψ n)) atTop
      (𝓝 (∫ x, g x ∂chartLaw K₀ z₀ (gapDomain D₀) ψ₀)) := by
  have : PolishSpace (ContinuousPath ℂ) := LatticeProb.polishSpace_continuousMap ℝ≥0 ℂ
  have hμ : Tendsto (fun n => K n (z n)) atTop (𝓝 (K₀ z₀)) :=
    (ContinuousEval.continuous_eval.tendsto (K₀, z₀)).comp (hK.prodMk_nhds hz)
  have hm : ∀ (D' : C(ℂ, ℝ)) (ψ' : C(ℂ, ℂ)), Measurable (chartStopPath (gapDomain D') ψ') :=
    fun D' ψ' => measurable_chartStopPath _ (isOpen_gapDomain D') ψ'
  have hint : ∀ (L : PathLawFamily) (w : ℂ) (D' : C(ℂ, ℝ)) (ψ' : C(ℂ, ℂ)),
      ∫ x, g x ∂chartLaw L w (gapDomain D') ψ' =
        ∫ x, g (chartStopPath (gapDomain D') ψ' x) ∂(L w : Measure (ContinuousPath ℂ)) :=
    fun L w D' ψ' => integral_map (hm D' ψ').aemeasurable g.continuous.measurable.aestronglyMeasurable
  simp only [hint]
  refine tendsto_integral_comp_of_ae_tendsto (μ := K₀ z₀) (μs := fun n => K n (z n)) hμ
    (f := chartStopPath (gapDomain D₀) ψ₀) (fs := fun n => chartStopPath (gapDomain (D n)) (ψ n))
    (fun n => hm (D n) (ψ n)) (hm D₀ ψ₀) ?_ g
  filter_upwards [hcross] with x hx
  have hθ : Tendsto (fun p : ℕ × ContinuousPath ℂ => ((D p.1, ψ p.1), p.2)) (atTop ×ˢ 𝓝 x)
      (𝓝 ((D₀, ψ₀), x)) :=
    ((hD.prodMk_nhds hψ).comp tendsto_fst).prodMk_nhds tendsto_snd
  exact (continuousAt_chartStopPath_gapDomain (ψ := ψ₀) hx).tendsto.comp hθ

end MatedCRT
