import MatedCRT.FirstPass.Derived.StoppedRayIntervalComparison
import MatedCRT.FirstPass.Derived.GMS21Theorem310Form
import LatticeProb.Topology.ReparamDistanceIsometry

/-!
# From the local curve metric on unbounded rays to curves stopped at the exit of a disc

Theorem 3.10 of Gwynne–Miller–Sheffield (arXiv:1807.07515, `GMSTheorem310Form`) compares laws of curves modulo time
parametrization in the local metric (1.8), `localEDist f g = ∫_{r > 1} e^{-r} (1 ∧ d(f|[0,T_{f,r}], g|[0,T_{g,r}])) dr`,
where `T_{f,r}` is the exit time of `f` from `B_r(0)` (`rayClock`). In the proof of Theorem 3.4, case 1, of
arXiv:1705.11161 the walk and Brownian motion are compared after they are stopped at their exits from a bounded
domain. This file provides the passage from the first comparison to the one-sided bounds at variable radii of
`GMS21AnnulusUniformTransfer`:

* `rayClock_eq_pathExitTime`: the clock of a Euclidean ray is the first exit time of the complex path with the same
  coordinates.
* `exists_intervalEDist_lt_of_localEDist_lt`: if `localEDist f g < e^{-b} s (b - a)` with `1 ≤ a` and `0 ≤ s ≤ 1`,
  some radius `r ∈ (a, b)` has interval distance less than `s` (otherwise the integrand is at least `e^{-b} s` on
  `(a, b)`).
* `exists_cmpEDist_stopAtExit_lt_of_localEDist_lt`: for such a radius the complex paths stopped at their exits from
  `B_r(0)` are within `s` modulo time parametrization.
* `measure_le_of_levyProkhorovEDist_curveLaw_lt`: if the law of the curve class of a random path (restricted to the
  unbounded paths) is within `δ` in the Lévy–Prokhorov distance of the curve law of an almost surely unbounded random
  path, then every set of paths has probability at most the probability that the second path is within `δ` of the
  set in the local metric, plus `2 δ`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open LatticeProb LatticeProb.IntervalReparamEDist LatticeProb.UnboundedRayIntervalIntegrand
  LatticeProb.UnboundedRayLocalDistance LatticeProb.UnboundedRayCurveSpace

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _
local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩

/-- The exit time of a Euclidean ray from `B_r(0)` (the clock of the local curve metric) is the first exit time from
`B_r(0)` of the complex path with the same coordinates. -/
theorem rayClock_eq_pathExitTime {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2)} {g : ℝ≥0 → ℂ}
    (hfg : ∀ t, f t = Complex.orthonormalBasisOneI.repr (g t)) (r : ℝ) :
    rayClock f r = pathExitTime (ball (0 : ℂ) r) g := by
  have hmem : ∀ t, f t ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) r ↔ g t ∈ ball (0 : ℂ) r := fun t => by
    rw [hfg t, mem_ball_zero_iff, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  unfold LatticeProb.UnboundedRayLocalDistance.rayClock LatticeProb.openExitTime pathExitTime
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le_of_le ⟨t, fun h => ht ((hmem t).1 h)⟩ le_rfl
  · exact le_iInf fun t => sInf_le ⟨t.1, rfl, fun h => t.2 ((hmem t.1).2 h)⟩

/-- A path with unbounded range leaves every ball. -/
theorem exists_not_mem_ball_of_unbounded {E : Type*} [PseudoMetricSpace E] {f : ℝ≥0 → E}
    (hf : ¬ Bornology.IsBounded (range f)) (x : E) (r : ℝ) : ∃ t, f t ∉ ball x r := by
  by_contra hno
  refine hf ((isBounded_ball (x := x) (r := r)).subset ?_)
  rintro _ ⟨t, rfl⟩
  by_contra ht
  exact hno ⟨t, ht⟩

/-- A path that is outside `U` at some time leaves `U` at a finite time. -/
theorem pathExitTime_ne_top_of_not_mem {U : Set ℂ} {g : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : g t ∉ U) :
    pathExitTime U g ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (sInf_le ⟨t, rfl, ht⟩)

/-- A path stopped at a finite exit time is the path read at `min t T`. -/
theorem stopAtExit_eq_of_ne_top {U : Set ℂ} {g : ℝ≥0 → ℂ} (h : pathExitTime U g ≠ ⊤) :
    stopAtExit U g = fun t => g (min t (pathExitTime U g).toNNReal) := by
  funext t
  simp only [stopAtExit, h, ↓reduceIte]

/-- **Stopped complex paths and the interval distance of their coordinates.** If the complex paths `g₁`, `g₂` leave
`B_r(0)` at finite times, their curves stopped at these exits are within the interval distance of the Euclidean rays
with the same coordinates, on the intervals given by the clock of the local metric. -/
theorem cmpEDist_stopAtExit_ball_le_intervalEDist {f₁ f₂ : ℝ≥0 → EuclideanSpace ℝ (Fin 2)} {g₁ g₂ : ℝ≥0 → ℂ}
    (h₁ : ∀ t, f₁ t = Complex.orthonormalBasisOneI.repr (g₁ t))
    (h₂ : ∀ t, f₂ t = Complex.orthonormalBasisOneI.repr (g₂ t)) {r : ℝ}
    (hfin₁ : pathExitTime (ball (0 : ℂ) r) g₁ ≠ ⊤) (hfin₂ : pathExitTime (ball (0 : ℂ) r) g₂ ≠ ⊤) :
    cmpEDist (stopAtExit (ball (0 : ℂ) r) g₁) (stopAtExit (ball (0 : ℂ) r) g₂) ≤
      intervalEDist f₁ f₂ (rayClock f₁ r) (rayClock f₂ r) := by
  have hf₁ : f₁ = Complex.orthonormalBasisOneI.repr ∘ g₁ := funext h₁
  have hf₂ : f₂ = Complex.orthonormalBasisOneI.repr ∘ g₂ := funext h₂
  rw [rayClock_eq_pathExitTime h₁, rayClock_eq_pathExitTime h₂, hf₁, hf₂,
    ReparamDistanceIsometry.intervalEDist_comp_isometry _ Complex.orthonormalBasisOneI.repr.isometry,
    stopAtExit_eq_of_ne_top hfin₁, stopAtExit_eq_of_ne_top hfin₂]
  have h := LocalCurveMetricPick.cmpEDist_stopped_le_intervalEDist g₁ g₂
    (pathExitTime (ball (0 : ℂ) r) g₁).toNNReal (pathExitTime (ball (0 : ℂ) r) g₂).toNNReal
  rwa [ENNReal.coe_toNNReal hfin₁, ENNReal.coe_toNNReal hfin₂] at h

/-- **Radius pick for the local metric over radii `r > 1`.** If
`localEDist f g < e^{-b} s (b - a)` with `1 ≤ a` and `0 ≤ s ≤ 1`, then some radius `r ∈ (a, b)` has interval
distance less than `s`. -/
theorem exists_intervalEDist_lt_of_localEDist_lt {E : Type*} [PseudoEMetricSpace E]
    (clock : (ℝ≥0 → E) → ℝ → ℝ≥0∞) {f g : ℝ≥0 → E} {a b s : ℝ} (ha : 1 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : LocalCurveIntervalDistance.localEDist clock f g <
      ENNReal.ofReal (Real.exp (-b) * s * (b - a))) :
    ∃ r ∈ Ioo a b, intervalEDist f g (clock f r) (clock g r) < ENNReal.ofReal s := by
  by_contra hcon
  have hge : ∀ r ∈ Ioo a b, ENNReal.ofReal s ≤ intervalEDist f g (clock f r) (clock g r) :=
    fun r hr => not_lt.1 fun hlt => hcon ⟨r, hr, hlt⟩
  have hes : 0 ≤ Real.exp (-b) * s := mul_nonneg (Real.exp_pos _).le hs0
  refine (not_le.2 h) ?_
  unfold LocalCurveIntervalDistance.localEDist
  calc ENNReal.ofReal (Real.exp (-b) * s * (b - a))
      = ENNReal.ofReal (Real.exp (-b) * s) * volume (Ioo a b) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hes]
    _ = ∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.exp (-b) * s) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo a b, ENNReal.ofReal (Real.exp (-r)) *
          min 1 (intervalEDist f g (clock f r) (clock g r)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hr.2]))) ?_
        exact le_min (ENNReal.ofReal_le_one.2 hs1) (hge r hr)
    _ ≤ _ := lintegral_mono_set fun r hr => (lt_of_le_of_lt ha hr.1 : (1 : ℝ) < r)

/-- **Small local metric gives a disc with close stopped curves.** Let `f₁`, `f₂` be unbounded Euclidean rays with
the coordinates of the complex paths `g₁`, `g₂`. If `localEDist f₁ f₂ < e^{-b} s (b - a)` with `1 ≤ a` and
`0 ≤ s ≤ 1`, then for some `r ∈ (a, b)` the complex paths stopped at their exits from `B_r(0)` are within `s` modulo
time parametrization. -/
theorem exists_cmpEDist_stopAtExit_lt_of_localEDist_lt (f₁ f₂ : UnboundedRay 2) {g₁ g₂ : ℝ≥0 → ℂ}
    (h₁ : ∀ t, f₁.1 t = Complex.orthonormalBasisOneI.repr (g₁ t))
    (h₂ : ∀ t, f₂.1 t = Complex.orthonormalBasisOneI.repr (g₂ t)) {a b s : ℝ} (ha : 1 ≤ a) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1)
    (h : UnboundedRayLocalDistance.localEDist f₁ f₂ < ENNReal.ofReal (Real.exp (-b) * s * (b - a))) :
    ∃ r ∈ Ioo a b, cmpEDist (stopAtExit (ball (0 : ℂ) r) g₁) (stopAtExit (ball (0 : ℂ) r) g₂) <
      ENNReal.ofReal s := by
  obtain ⟨r, hr, hlt⟩ := exists_intervalEDist_lt_of_localEDist_lt (rayClock (d := 2)) (f := ⇑f₁.1)
    (g := ⇑f₂.1) ha hs0 hs1 h
  have hfin : ∀ (f : UnboundedRay 2) (g : ℝ≥0 → ℂ),
      (∀ t, f.1 t = Complex.orthonormalBasisOneI.repr (g t)) → pathExitTime (ball (0 : ℂ) r) g ≠ ⊤ := by
    intro f g hfg
    obtain ⟨t, ht⟩ := exists_not_mem_ball_of_unbounded f.2 0 r
    refine pathExitTime_ne_top_of_not_mem (t := t) fun hg => ht ?_
    rw [hfg t, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.1 hg
  exact ⟨r, hr, lt_of_le_of_lt
    (cmpEDist_stopAtExit_ball_le_intervalEDist h₁ h₂ (hfin f₁ g₁ h₁) (hfin f₂ g₂ h₂)) hlt⟩

/-- **From the Lévy–Prokhorov distance of curve laws to a one-sided bound on sets of paths.** Let `ν`, `μ` be
probability laws of continuous Euclidean paths, `μ` almost surely of unbounded range. If the curve law of `ν`
restricted to the unbounded paths (`GMS310.unboundedCurveLaw`) is within `δ > 0` of the curve law of `μ` in the
Lévy–Prokhorov distance, then for every set `S` of paths, `ν S` is at most the `μ`-probability that the path is within
`δ` in the local metric of an unbounded path of `S`, plus `2 δ`. (The mass of the bounded paths under `ν` is at most
`δ`.) -/
theorem measure_le_of_levyProkhorovEDist_curveLaw_lt (ν μ : Measure (Path 2)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f)) {δ : ℝ}
    (hδ : 0 < δ) (h : levyProkhorovEDist (GMS310.unboundedCurveLaw ν) (curveLaw μ hμ) < ENNReal.ofReal δ)
    (S : Set (Path 2)) :
    ν S ≤ μ {f : Path 2 | ∃ hf : ¬ Bornology.IsBounded (Set.range f), ∃ g ∈ S,
        ∃ hg : ¬ Bornology.IsBounded (Set.range g),
          UnboundedRayLocalDistance.localEDist ⟨g, hg⟩ ⟨f, hf⟩ < ENNReal.ofReal δ} +
      2 * ENNReal.ofReal δ := by
  set Unb : Set (Path 2) := {f | ¬ Bornology.IsBounded (Set.range f)} with hUnb
  set T : Set (Path 2) := {f : Path 2 | ∃ hf : ¬ Bornology.IsBounded (Set.range f), ∃ g ∈ S,
        ∃ hg : ¬ Bornology.IsBounded (Set.range g),
          UnboundedRayLocalDistance.localEDist ⟨g, hg⟩ ⟨f, hf⟩ < ENNReal.ofReal δ} with hTdef
  have hUm : MeasurableSet Unb := measurableSet_continuousMap_unbounded_range 0
  have hemb : MeasurableEmbedding (Subtype.val : UnboundedRay 2 → Path 2) :=
    MeasurableEmbedding.subtype_coe hUm
  set X : Set (UnboundedRayCurveSpace 2) := project '' (Subtype.val ⁻¹' S) with hX
  have hB : MeasurableSet (closure X) := isClosed_closure.measurableSet
  have hT : MeasurableSet (thickening δ X) := isOpen_thickening.measurableSet
  -- the paths of `S` with unbounded range
  have h1 : ν (S ∩ Unb) ≤ GMS310.unboundedCurveLaw ν (closure X) := by
    unfold GMS310.unboundedCurveLaw
    rw [Measure.map_apply continuous_project.measurable hB, hemb.comap_apply]
    refine measure_mono ?_
    rintro f ⟨hfS, hf⟩
    exact ⟨⟨f, hf⟩, subset_closure ⟨⟨f, hf⟩, hfS, rfl⟩, rfl⟩
  -- the neighbourhood in the local metric
  have h2 : curveLaw μ hμ (thickening δ X) ≤ μ T := by
    rw [curveLaw_apply μ hμ hT]
    have hρ : (supportedLaw μ Unb hμ).map Subtype.val = μ := map_supportedLaw μ Unb hμ
    calc supportedLaw μ Unb hμ (project ⁻¹' thickening δ X)
        ≤ supportedLaw μ Unb hμ (Subtype.val ⁻¹' T) := by
          refine measure_mono fun y hy => ?_
          obtain ⟨x, ⟨y', hy'S, rfl⟩, hxy⟩ := (mem_thickening_iff_exists_edist_lt _ _).1 hy
          refine ⟨y.2, y'.1, hy'S, y'.2, ?_⟩
          rw [edist_project, UnboundedRayLocalDistance.localEDist_comm] at hxy
          exact hxy
      _ = (supportedLaw μ Unb hμ).map Subtype.val T :=
          ((MeasurableEmbedding.subtype_coe hUm).map_apply _ _).symm
      _ = μ T := by rw [hρ]
  -- the mass of the bounded paths
  have h3 : ν Unbᶜ ≤ ENNReal.ofReal δ := by
    have hr := right_measure_le_of_levyProkhorovEDist_lt h MeasurableSet.univ
    rw [measure_univ] at hr
    have hν : GMS310.unboundedCurveLaw ν (thickening (ENNReal.ofReal δ).toReal univ) ≤ ν Unb := by
      unfold GMS310.unboundedCurveLaw
      rw [Measure.map_apply continuous_project.measurable isOpen_thickening.measurableSet,
        hemb.comap_apply]
      refine measure_mono ?_
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    rw [prob_compl_eq_one_sub hUm, tsub_le_iff_left]
    exact hr.trans (add_le_add hν le_rfl)
  have hl := left_measure_le_of_levyProkhorovEDist_lt h hB
  rw [ENNReal.toReal_ofReal hδ.le, thickening_closure] at hl
  calc ν S ≤ ν (S ∩ Unb) + ν Unbᶜ := by
        refine (measure_mono fun f hf => ?_).trans (measure_union_le _ _)
        by_cases hfU : f ∈ Unb
        · exact Or.inl ⟨hf, hfU⟩
        · exact Or.inr hfU
    _ ≤ (μ T + ENNReal.ofReal δ) + ENNReal.ofReal δ :=
        add_le_add (h1.trans (hl.trans (add_le_add h2 le_rfl))) h3
    _ = μ T + 2 * ENNReal.ofReal δ := by rw [add_assoc, two_mul]

end MatedCRT.GMS310Transfer
