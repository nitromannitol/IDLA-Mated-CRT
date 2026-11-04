import MatedCRT.Steps.Sec6.IDLAUpperBound
import MatedCRT.Proofs.Sec5.IDLALowerBound.Geometry

/-!
# Proposition 6.1: the boundary layer of a harmonic ball (eq:zero-measure-boundary, line 2857)

* `tendsto_measure_boundaryLayer`: for an open set `L` of finite measure, `μ(L \ B⁻_{1/(k+1)}(L)) → 0`.
* `exists_boundaryLayer_prob_le`: if the events `{p, μ(L \ B⁻_{δ₁}(L)) ≥ s}` are null measurable (the step
  `BoundaryLayerMeasurableStep`) and almost surely `L` is open of finite measure on `p`, then for each `s > 0` their
  probability is as small as we like for a deterministic `δ₁ > 0` (continuity from above).
-/

namespace MatedCRT

namespace IDLAUpperBound

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

theorem one_div_succ_anti {i j : ℕ} (hij : i ≤ j) : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
  refine one_div_le_one_div_of_le (by positivity) ?_
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- The layer `L \ B⁻_δ(L)` grows with `δ`. -/
theorem boundaryLayer_mono {L : Set ℂ} {δ δ' : ℝ} (h : δ' ≤ δ) :
    L \ innerNbhd δ' L ⊆ L \ innerNbhd δ L :=
  fun _ hy => ⟨hy.1, fun hyi => hy.2 (IDLALowerBound.innerNbhd_anti h L hyi)⟩

/-- For an open set `L` of finite measure, the mass of the layer `L \ B⁻_{1/(k+1)}(L)` tends to `0`. -/
theorem tendsto_measure_boundaryLayer {μ : Measure ℂ} {L : Set ℂ} (hL : IsOpen L) (hμ : μ L ≠ ⊤) :
    Tendsto (fun k : ℕ => μ (L \ innerNbhd (1 / ((k : ℝ) + 1)) L)) atTop (𝓝 0) := by
  have hmeas : ∀ k : ℕ, NullMeasurableSet (L \ innerNbhd (1 / ((k : ℝ) + 1)) L) μ := by
    intro k
    refine (hL.measurableSet.diff ?_).nullMeasurableSet
    have hin : innerNbhd (1 / ((k : ℝ) + 1)) L =
        L ∩ {y | ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ infEDist y Lᶜ} := rfl
    rw [hin]
    exact hL.measurableSet.inter (isClosed_le continuous_const continuous_infEDist).measurableSet
  have hanti : Antitone fun k : ℕ => L \ innerNbhd (1 / ((k : ℝ) + 1)) L :=
    fun i j hij => boundaryLayer_mono (one_div_succ_anti hij)
  have hfin : μ (L \ innerNbhd (1 / (((0 : ℕ) : ℝ) + 1)) L) ≠ ⊤ :=
    ((measure_mono fun y (hy : y ∈ L \ _) => hy.1).trans_lt (lt_top_iff_ne_top.2 hμ)).ne
  have h := tendsto_measure_iInter_atTop hmeas hanti ⟨0, hfin⟩
  have hempty : (⋂ k : ℕ, L \ innerNbhd (1 / ((k : ℝ) + 1)) L) = ∅ := by
    ext y
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hy : y ∈ L
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hL y hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
      refine ⟨k, fun h => h.2 ⟨hy, ?_⟩⟩
      refine le_infEDist.2 fun z hz => ?_
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal (hk.le.trans ?_)
      by_contra hlt
      exact hz (hball (mem_ball.2 (by rw [dist_comm]; exact not_le.1 hlt)))
    · exact ⟨0, fun h => hy h.1⟩
  rw [hempty, measure_empty] at h
  exact h

/-- **Continuity from above for the boundary layer.** If the events `{p, μ(L \ B⁻_{δ₁}(L)) ≥ s}` are null measurable
and almost surely `L` is open of finite measure on `{p}`, then for `s > 0` their probability is at most any `e > 0`
for some deterministic `δ₁ > 0`. -/
theorem exists_boundaryLayer_prob_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ) (L : Ω → Set ℂ) (p : Ω → Prop)
    (hae : ∀ᵐ ω ∂P, p ω → IsOpen (L ω) ∧ μ ω (L ω) ≠ ⊤) {s : ℝ} (hs : 0 < s)
    (hmeas : ∀ δ₁ : ℝ, 0 < δ₁ →
      NullMeasurableSet {ω | p ω ∧ ENNReal.ofReal s ≤ μ ω (L ω \ innerNbhd δ₁ (L ω))} P)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ P {ω | p ω ∧ ENNReal.ofReal s ≤ μ ω (L ω \ innerNbhd δ₁ (L ω))} ≤ e := by
  set E : ℕ → Set Ω := fun k =>
    {ω | p ω ∧ ENNReal.ofReal s ≤ μ ω (L ω \ innerNbhd (1 / ((k : ℝ) + 1)) (L ω))} with hE
  have hanti : Antitone E := by
    intro i j hij ω hω
    exact ⟨hω.1, hω.2.trans (measure_mono (boundaryLayer_mono (one_div_succ_anti hij)))⟩
  have hlim := tendsto_measure_iInter_atTop (fun k => hmeas _ (by positivity)) hanti ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ k, E k) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro ω hω hgood
    simp only [hE, mem_iInter, mem_ofPred_eq] at hω
    obtain ⟨hopen, hfin⟩ := hgood (hω 0).1
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal s := ENNReal.ofReal_pos.2 hs
    obtain ⟨k, hk⟩ := ((tendsto_measure_boundaryLayer hopen hfin).eventually (gt_mem_nhds hpos)).exists
    exact absurd (hω k).2 (not_le.2 hk)
  rw [hnull] at hlim
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1 hlim e he).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

end IDLAUpperBound

end MatedCRT
