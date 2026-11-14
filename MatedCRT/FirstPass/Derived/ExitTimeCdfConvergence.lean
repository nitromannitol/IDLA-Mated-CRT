import MatedCRT.FirstPass.S3t.LBMRegular

/-!
# Convergence of exit-time distribution functions under weak convergence of path laws

Paths are the continuous maps `ℝ≥0 → ℂ` with the topology of local uniform convergence
(`MarkovProcess.ContinuousPath ℂ`), and `pathExitTime U g` is the first time the path `g` is outside `U`.

* For `U` open, `{g | pathExitTime U g ≤ s}` is closed
  (`isClosed_pathExitTime_le`): its complement is `{g | g (Iic s) ⊆ U}`, open for the compact-open topology.
* A path that exits `U` regularly (`MatedCRT.TruncatedLaws.RegularExit`: it visits the complement of
  `closure U` at times arbitrarily close to the exit time from above) and whose exit time is `< s`
  lies in the interior of `{pathExitTime U ≤ s}` (`mem_interior_pathExitTime_le`).
* Hence if the limit law `μ` is carried by the regular-exit paths and `μ (pathExitTime U = s) = 0`, the
  frontier of `{pathExitTime U ≤ s}` is `μ`-null (`measure_frontier_pathExitTime_le_eq_zero`), and weak
  convergence `μₙ → μ` gives `μₙ (pathExitTime U ≤ s) → μ (pathExitTime U ≤ s)`
  (`tendsto_measure_pathExitTime_le`), by the portmanteau theorem.
* For a finite measure the exit time has at most countably many atoms, so the distribution function of
  the exit time is the limit at every point of a dense subset of `(0, ∞)`
  (`exists_mem_Ioo_measure_pathExitTime_eq_zero`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.ExitTimeCdf

open MatedCRT.TruncatedLaws (RegularExit pathExitTime_eq_top_of_forall_mem)

/-- A continuous path has not left the open set `U` before time `s` iff it stays in `U` up to time `s`. -/
theorem lt_pathExitTime_iff {U : Set ℂ} (hU : IsOpen U) {g : ContinuousPath ℂ} {s : ℝ≥0} :
    (s : ℝ≥0∞) < pathExitTime U ⇑g ↔ ∀ t ≤ s, g t ∈ U := by
  constructor
  · intro h t ht
    by_contra hg
    have hle : pathExitTime U ⇑g ≤ t := sInf_le ⟨t, rfl, hg⟩
    exact absurd (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr ht) h) (not_lt_of_ge hle)
  · intro h
    set C : Set ℝ≥0 := {t | g t ∉ U} with hC
    have hCclosed : IsClosed C := (hU.preimage g.continuous).isClosed_compl
    by_cases hne : C.Nonempty
    · have hmem : sInf C ∈ C := hCclosed.csInf_mem hne (OrderBot.bddBelow C)
      have hgt : s < sInf C := by
        by_contra hle
        exact hmem (h _ (not_lt.mp hle))
      calc (s : ℝ≥0∞) < ↑(sInf C) := ENNReal.coe_lt_coe.mpr hgt
        _ ≤ pathExitTime U ⇑g := by
          unfold pathExitTime
          refine le_sInf ?_
          rintro _ ⟨t, rfl, ht⟩
          exact ENNReal.coe_le_coe.mpr (csInf_le (OrderBot.bddBelow C) ht)
    · have hall : ∀ t, g t ∈ U := fun t => by
        by_contra ht
        exact hne ⟨t, ht⟩
      rw [pathExitTime_eq_top_of_forall_mem hall]
      exact ENNReal.coe_lt_top

/-- For an open set `U`, the paths that have left `U` by time `s` form a closed set of paths. -/
theorem isClosed_pathExitTime_le {U : Set ℂ} (hU : IsOpen U) (s : ℝ≥0) :
    IsClosed {g : ContinuousPath ℂ | pathExitTime U ⇑g ≤ s} := by
  have hc : {g : ContinuousPath ℂ | pathExitTime U ⇑g ≤ s}ᶜ =
      {g : ContinuousPath ℂ | MapsTo g (Iic s) U} := by
    ext g
    simp only [mem_compl_iff, mem_ofPred_eq, not_le]
    rw [lt_pathExitTime_iff hU]
    rfl
  rw [← isOpen_compl_iff, hc]
  have hK : IsCompact (Iic s) := by
    have : Iic s = Icc (0 : ℝ≥0) s := by
      ext x
      simp
    rw [this]
    exact isCompact_Icc
  exact ContinuousMap.isOpen_setOfPred_mapsTo hK hU

/-- A path that exits `U` regularly, at a time strictly before `s`, has a neighbourhood of paths that have
all left `U` by time `s`. -/
theorem mem_interior_pathExitTime_le {U : Set ℂ} {g : ContinuousPath ℂ} {s : ℝ≥0}
    (hreg : RegularExit U ⇑g) (hlt : pathExitTime U ⇑g < s) :
    g ∈ interior {h : ContinuousPath ℂ | pathExitTime U ⇑h ≤ s} := by
  rcases hreg with htop | hfreq
  · rw [htop] at hlt
    exact absurd hlt (not_lt_of_ge le_top)
  · have hfin : pathExitTime U ⇑g ≠ ⊤ := ne_top_of_lt hlt
    have hlt' : (pathExitTime U ⇑g).toNNReal < s := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin]
      exact hlt
    obtain ⟨t, ht1, ht2⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT hlt')).exists
    have hW : IsOpen {h : ContinuousPath ℂ | h t ∉ closure U} :=
      isClosed_closure.isOpen_compl.preimage (continuous_eval_const t)
    have hsub : {h : ContinuousPath ℂ | h t ∉ closure U} ⊆
        {h : ContinuousPath ℂ | pathExitTime U ⇑h ≤ s} := by
      intro h hh
      have hle : pathExitTime U ⇑h ≤ t := sInf_le ⟨t, rfl, fun hu => hh (subset_closure hu)⟩
      exact hle.trans (ENNReal.coe_le_coe.mpr ht2.2.le)
    exact interior_maximal hsub hW ht1

/-- If the law `μ` carries only regularly exiting paths and has no atom at the exit time `s`, the set of paths
that have left `U` by time `s` has `μ`-null frontier. -/
theorem measure_frontier_pathExitTime_le_eq_zero {U : Set ℂ} (hU : IsOpen U)
    {μ : Measure (ContinuousPath ℂ)} (hreg : ∀ᵐ g : ContinuousPath ℂ ∂μ, RegularExit U ⇑g) {s : ℝ≥0}
    (hs : μ {g : ContinuousPath ℂ | pathExitTime U ⇑g = s} = 0) :
    μ (frontier {g : ContinuousPath ℂ | pathExitTime U ⇑g ≤ s}) = 0 := by
  refine measure_mono_null (t := {g : ContinuousPath ℂ | pathExitTime U ⇑g = s} ∪ {g : ContinuousPath ℂ | ¬ RegularExit U ⇑g}) ?_
    (measure_union_null hs (ae_iff.mp hreg))
  intro g hg
  rw [(isClosed_pathExitTime_le hU s).frontier_eq] at hg
  by_cases hr : RegularExit U ⇑g
  · left
    refine le_antisymm hg.1 (not_lt.mp fun hlt => hg.2 ?_)
    exact mem_interior_pathExitTime_le hr hlt
  · right
    exact hr

/-- **Convergence of the exit-time distribution function.** Let `μₙ → μ` weakly on the path space, with
`μ`-almost every path exiting `U` regularly and `μ (pathExitTime U = s) = 0`. Then
`μₙ (pathExitTime U ≤ s) → μ (pathExitTime U ≤ s)`. -/
theorem tendsto_measure_pathExitTime_le {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure (ContinuousPath ℂ)} {μ : ProbabilityMeasure (ContinuousPath ℂ)}
    (hlim : Tendsto μs L (𝓝 μ)) {U : Set ℂ} (hU : IsOpen U)
    (hreg : ∀ᵐ g : ContinuousPath ℂ ∂(μ : Measure (ContinuousPath ℂ)), RegularExit U ⇑g) {s : ℝ≥0}
    (hs : (μ : Measure (ContinuousPath ℂ)) {g : ContinuousPath ℂ | pathExitTime U ⇑g = s} = 0) :
    Tendsto (fun i => (μs i : Measure (ContinuousPath ℂ)) {g : ContinuousPath ℂ | pathExitTime U ⇑g ≤ s}) L
      (𝓝 ((μ : Measure (ContinuousPath ℂ)) {g : ContinuousPath ℂ | pathExitTime U ⇑g ≤ s})) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim
    (measure_frontier_pathExitTime_le_eq_zero hU hreg hs)

/-- The exit time from an open set is a measurable function of the path. -/
theorem measurable_pathExitTime {U : Set ℂ} (hU : IsOpen U) :
    Measurable (fun g : ContinuousPath ℂ => pathExitTime U ⇑g) := by
  refine measurable_of_Iic fun x => ?_
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · have : (fun g : ContinuousPath ℂ => pathExitTime U ⇑g) ⁻¹' Iic x =
        {g : ContinuousPath ℂ | pathExitTime U ⇑g ≤ x.toNNReal} := by
      ext g
      simp [ENNReal.coe_toNNReal hx]
    rw [this]
    exact (isClosed_pathExitTime_le hU _).measurableSet

/-- **Points of continuity of the exit-time distribution function.** For a finite measure on paths, every
nonempty open subinterval of `(0, ∞)` contains a time `s` at which the exit time from `U` has no atom. -/
theorem exists_mem_Ioo_measure_pathExitTime_eq_zero {U : Set ℂ} (hU : IsOpen U)
    (μ : Measure (ContinuousPath ℂ)) [IsFiniteMeasure μ] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ s : ℝ, a < s ∧ s < b ∧ μ {g : ContinuousPath ℂ | pathExitTime U ⇑g = ENNReal.ofReal s} = 0 := by
  have hC : Set.Countable {t : ℝ≥0∞ | 0 < μ {g : ContinuousPath ℂ | pathExitTime U ⇑g = t}} :=
    Measure.countable_meas_level_set_pos (measurable_pathExitTime hU)
  have hC' : Set.Countable {s : ℝ | 0 < s ∧ ENNReal.ofReal s ∈ {t : ℝ≥0∞ | 0 < μ {g : ContinuousPath ℂ | pathExitTime U ⇑g = t}}} := by
    refine (hC.image ENNReal.toReal).mono ?_
    rintro s ⟨hs0, hs⟩
    exact ⟨ENNReal.ofReal s, hs, ENNReal.toReal_ofReal hs0.le⟩
  obtain ⟨s, hsC, hsab⟩ := (hC'.dense_compl ℝ).exists_mem_open (isOpen_Ioo (a := a) (b := b))
    ⟨(a + b) / 2, by constructor <;> linarith⟩
  refine ⟨s, hsab.1, hsab.2, ?_⟩
  by_contra hne
  exact hsC ⟨by linarith [hsab.1], pos_iff_ne_zero.mpr hne⟩

end MatedCRT.ExitTimeCdf
