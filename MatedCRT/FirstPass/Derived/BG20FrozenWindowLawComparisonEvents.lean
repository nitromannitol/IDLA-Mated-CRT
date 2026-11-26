import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonGood
import MatedCRT.FirstPass.Derived.WalkLawInterpClosenessInMeasure

/-!
# Almost sure and in-probability events of the frozen window comparison

Probabilistic inputs of the proof of `BG20FrozenWindowLawComparison` (Berestycki–Gwynne (2020), proof of Lemma 7.21;
written answer MQ-sbl-35).

* `MatedCRT.FrozenPath.ae_windowGood`: if the frontier of the window domain is almost surely a Jordan curve, then
  almost surely the window has an intrinsic chart, which agrees with the inverse chart of Berestycki–Gwynne on the
  window domain, and the window domain contains `η(u)` (written answer MQ-sbl-35, line 3).
* `MatedCRT.FrozenPath.tendsto_measure_of_ae_eventually_notMem`: events which almost surely eventually fail have
  probabilities tending to `0`.
* `MatedCRT.FrozenPath.mem_cell_ceil`: `η(u)` lies in the cell `⌈u/ε⌉`.
* `MatedCRT.FrozenPath.tendsto_prob_pathLevyProkhorovEDist_ceil`: the quenched walk law from the cell `⌈u/ε⌉` and the
  interpolated law at the random point `η(u)` are close in probability for the Lévy–Prokhorov distance.
* `MatedCRT.FrozenPath.tendsto_of_tendsto_pathLevyProkhorovEDist`: laws at Lévy–Prokhorov distance tending to `0` from
  a weakly convergent sequence converge weakly to the same limit.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open MatedCRT.FirstPass.Derived (walkLawModulus maxCellDiam pathLevyProkhorovEDist
  pathLevyProkhorovEDist_eq_ofReal_dist pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell_of_nonneg)
open scoped NNReal ENNReal

namespace MatedCRT

namespace FrozenPath

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The window is good almost surely** (written answer MQ-sbl-35, line 3). If the frontier of the window domain is
almost surely a Jordan curve, then almost surely the window `(a, u, b)` of a continuous version `η'` of the curve has an
inverse chart at `η(u)`, the intrinsic construction succeeds (`WindowGoodIntr`), the intrinsic chart agrees with the
inverse chart `windowChartBG` on the window domain, and the window domain contains `η(u)`. -/
theorem ae_windowGood {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hJF : WindowFrontierJordanInput 𝒮) {η' : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {a u b : ℝ} (hau : a < u) (hub : u < b) :
    ∀ᵐ ω ∂S.P, WindowGoodIntr a u b (η' ω) ∧ η' ω ∈ windowChartCurves a u b ∧
      (∀ x ∈ windowDomain (η' ω) a u b, windowChartBG a u b (η' ω) x = windowChartIntr a u b (η' ω) x) ∧
      η' ω u ∈ windowDomain (η' ω) a u b := by
  filter_upwards [hS.ae_fixedTime_mem_interior_image u, hJF γ hγ hγ2 Ω S hS a u b hau hub,
    hS.ae_regularClosed_segmentImages, hS.ae_fixedTime_singleton_fibre u, hae] with ω hω hJ hr hfb he
  have hψ : ∃ ψ, IsInverseChart (windowDomain (η' ω) a u b) (η' ω u) ψ := by
    refine exists_isInverseChart_windowDomain (η' ω) ?_ ?_
    · rw [he]
      exact hω a b hau hub
    · rw [windowDomain_eq_of_coe_eq he]
      exact hJ
  have hreg : SegmentsRegularClosed (η' ω) := fun c d hcd => by
    rw [he]
    exact hr c d hcd
  have hfib : ∀ t, η' ω t = η' ω u → t = u := fun t ht => by
    rw [he] at ht
    exact hfb t ht
  obtain ⟨hG, heq⟩ := windowGoodIntr_and_eqOn_windowChartBG hau hψ hreg hfib
  obtain ⟨ψ, hψ'⟩ := hψ
  exact ⟨hG, ⟨ψ, hψ'⟩, heq, hψ'.mem⟩

/-- **Events which almost surely eventually fail have probabilities tending to `0`.** -/
theorem tendsto_measure_of_ae_eventually_notMem {μ : Measure Ω} [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n)) (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n) :
    Tendsto (fun n => μ (s n)) atTop (𝓝 0) := by
  set B : ℕ → Set Ω := fun N => ⋃ n ∈ Ici N, s n with hB
  have hBm : ∀ N, NullMeasurableSet (B N) μ := fun N =>
    (MeasurableSet.biUnion (to_countable _) fun n _ => hs n).nullMeasurableSet
  have hanti : Antitone B := fun N M hNM => biUnion_subset_biUnion_left (Ici_subset_Ici.2 hNM)
  have htend := tendsto_measure_iInter_atTop hBm hanti ⟨0, measure_ne_top _ _⟩
  have hnull : μ (⋂ N, B N) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro ω hω
    change ¬ ∀ᶠ n in atTop, ω ∉ s n
    intro hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    obtain ⟨n, hn, hns⟩ := mem_iUnion₂.1 (mem_iInter.1 hω N)
    exact hN n hn hns
  rw [hnull] at htend
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend (fun _ => zero_le)
    fun N => measure_mono (subset_biUnion_of_mem (u := s) (mem_Ici.2 le_rfl))

/-- `η(u)` lies in the cell `⌈u/ε⌉ = η([ε (⌈u/ε⌉ - 1), ε ⌈u/ε⌉])`. -/
theorem mem_cell_ceil {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (u : ℝ) : η u ∈ cell ε η ⌈u / ε⌉ := by
  have hne : ε ≠ 0 := hε.ne'
  have he : ε * (u / ε) = u := by field_simp
  refine ⟨u, ⟨?_, ?_⟩, rfl⟩
  · have hc2 : (⌈u / ε⌉ : ℝ) < u / ε + 1 := Int.ceil_lt_add_one _
    have h := mul_lt_mul_of_pos_left hc2 hε
    rw [mul_add, he, mul_one] at h
    rw [mul_sub, mul_one]
    linarith
  · have hc1 : u / ε ≤ ⌈u / ε⌉ := Int.le_ceil _
    have h := mul_le_mul_of_nonneg_left hc1 hε.le
    rwa [he] at h

/-- **The walk law from the cell `⌈u/ε⌉` against the interpolated law at `η(u)`, in probability.** Let `ε_n → 0⁺`,
assume the walk laws are equicontinuous in law (`hEqLaw`) and the cell diameters tend to `0` in probability
(`hdiam`). Then `LP(Q^{ε_n}(⌈u/ε_n⌉), P̃^{ε_n}_{η(u)}) → 0` in probability: on the event `|η(u)| ≤ R`, which has
probability close to `1` for large `R`, the point `η(u)` of the cell `⌈u/ε_n⌉` is handled by
`pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell_of_nonneg`. -/
theorem tendsto_prob_pathLevyProkhorovEDist_ceil {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    (u : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun n => S.P {ω | ENNReal.ofReal θ < pathLevyProkhorovEDist
      (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n) ⌈u / ε n⌉ ω)
      (interpWalkLaw S η' (ε n) ω (η' ω u))}) atTop (𝓝 0) := by
  have := hS.isProbabilityMeasure
  have hgood := ae_all_iff.2 fun n => hS.ae_interpWeight_good hae (hε0 n)
  have hRt : Tendsto (fun R : ℕ => S.P {ω | (R : ℝ) < ‖η' ω u‖}) atTop (𝓝 0) := by
    refine tendsto_measure_of_ae_eventually_notMem (fun R => measurableSet_lt measurable_const
      ((continuous_eval_const u).norm.measurable.comp hη')) (ae_of_all _ fun ω => ?_)
    obtain ⟨R, hR⟩ := exists_nat_ge ‖η' ω u‖
    filter_upwards [eventually_ge_atTop R] with R' hR'
    exact not_lt.2 (hR.trans (by exact_mod_cast hR'))
  rw [ENNReal.tendsto_nhds_zero]
  intro r' hr'
  obtain ⟨r, hr0, hrr'⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ r' := by
    rcases eq_or_ne r' ⊤ with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · exact ⟨r'.toReal, ENNReal.toReal_pos hr'.ne' h, (ENNReal.ofReal_toReal h).le⟩
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 hRt) (ENNReal.ofReal (r / 3))
    (ENNReal.ofReal_pos.2 (by linarith))).exists
  obtain ⟨a', ha'0, ha'r, ha'θ⟩ : ∃ a' : ℝ, 0 < a' ∧ a' ≤ r / 3 ∧ a' < θ :=
    ⟨min (r / 3) (θ / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨δ, hδ0, hδ⟩ := hEqLaw R a' ha'0
  obtain ⟨δ', hδ'0, hδ'δ, hδ'1⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 :=
    ⟨min δ 1, lt_min hδ0 one_pos, min_le_left _ _, min_le_right _ _⟩
  have hD' : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) R}
      ≤ ENNReal.ofReal (r / 3) :=
    (ENNReal.tendsto_nhds_zero.1 (hdiam R (δ' / 4) (by linarith))) _
      (ENNReal.ofReal_pos.2 (by linarith))
  have hεs : ∀ᶠ n in atTop, ε n < δ' / 2 := hε.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hδ, hD', hεs] with n hn1 hn2 hn3
  refine (measure_mono_ae (t := {ω | ENNReal.ofReal a' < walkLawModulus S η' (ε n) R δ ω} ∪
      {ω | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) R} ∪ {ω | (R : ℝ) < ‖η' ω u‖}) ?_).trans ?_
  · filter_upwards [hgood] with ω hω hmem
    by_contra hnot
    have h2 : ¬ ENNReal.ofReal a' < walkLawModulus S η' (ε n) R δ ω := fun h => hnot (Or.inl (Or.inl h))
    have h3 : ¬ ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) R := fun h => hnot (Or.inl (Or.inr h))
    have h4 : ¬ (R : ℝ) < ‖η' ω u‖ := fun h => hnot (Or.inr h)
    obtain ⟨hloc, hpos⟩ := hω n
    have hLP := pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell_of_nonneg S η' (hε0 n).le
      hloc hpos (R := R) (δ := δ) (d := δ' / 4) (a := a') (by linarith) (by linarith) (by linarith) ha'0.le
      (not_lt.1 h3) (not_lt.1 h2) (mem_cell_ceil (hε0 n) (⇑(η' ω)) u) (not_lt.1 h4)
    exact absurd hmem (not_lt.2 (hLP.trans (ENNReal.ofReal_le_ofReal ha'θ.le)))
  · refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) hR).trans ?_
    refine (add_le_add (add_le_add (hn1.trans (ENNReal.ofReal_le_ofReal ha'r)) hn2) le_rfl).trans ?_
    have hr3 : (0 : ℝ) ≤ r / 3 := by linarith
    rw [← ENNReal.ofReal_add hr3 hr3, ← ENNReal.ofReal_add (by linarith) hr3]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hrr'

section LevyProkhorovTopology

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- The Lévy–Prokhorov distance of laws on paths is finite. -/
theorem pathLevyProkhorovEDist_ne_top (μ ν : ProbabilityMeasure (ContinuousPath ℂ)) :
    pathLevyProkhorovEDist μ ν ≠ ⊤ := by
  rw [pathLevyProkhorovEDist_eq_ofReal_dist]
  exact ENNReal.ofReal_ne_top

/-- **Converging together.** If `νs → ν` weakly and the Lévy–Prokhorov distances of the local uniform metric between
`μs l` and `νs l` tend to `0`, then `μs → ν` weakly. -/
theorem tendsto_of_tendsto_pathLevyProkhorovEDist {μs νs : ℕ → ProbabilityMeasure (ContinuousPath ℂ)}
    {ν : ProbabilityMeasure (ContinuousPath ℂ)} (hν : Tendsto νs atTop (𝓝 ν))
    (hd : Tendsto (fun l => (pathLevyProkhorovEDist (μs l) (νs l)).toReal) atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 ν) := by
  have h1 : Tendsto (fun l => LevyProkhorov.ofMeasure (νs l)) atTop (𝓝 (LevyProkhorov.ofMeasure ν)) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto ν).comp hν
  have h2 : Tendsto (fun l => dist (LevyProkhorov.ofMeasure (νs l)) (LevyProkhorov.ofMeasure (μs l))) atTop
      (𝓝 0) := by
    refine hd.congr fun l => ?_
    rw [pathLevyProkhorovEDist_eq_ofReal_dist, ENNReal.toReal_ofReal dist_nonneg, dist_comm]
  exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp (h1.congr_dist h2)

end LevyProkhorovTopology

end FrozenPath

end MatedCRT
