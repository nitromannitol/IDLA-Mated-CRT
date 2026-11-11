import MatedCRT.Draft.Section4

/-!
# FIRST PASS, Lemma 5.3: generic bad-event probabilities

Two facts for the Borel-Cantelli step: (1) an event family whose complements have polynomially
small probability (`HarmonicBalls.PolyHighProb`, Harmonic-Balls-LQG HarmonicBalls/Defs/Notation.lean:27) has complement
probabilities tending to zero along `ε ↓ 0`; (2) a finite union of events, each with probability tending to zero, has
probability tending to zero. No measurability is used (`P` is an outer measure).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal

/-- **Polynomially high probability gives vanishing failure** (B2): if `PolyHighProb P E`, then `P (E r)ᶜ → 0` as `r ↓ 0`. -/
theorem tendsto_compl_of_polyHighProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (h : PolyHighProb P E) : Tendsto (fun r => P (E r)ᶜ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ := h
  have hcont : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] 0) (𝓝 0) := by
    have h0 : ContinuousAt (fun r : ℝ => C * r ^ p) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
    have h1 : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] 0) (𝓝 (C * 0 ^ p)) :=
      h0.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hp.ne'] using h1
  have hof : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof ?_ ?_
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    exact hbound r hr.1 hr.2

/-- **Finite unions** (B2): if each of the events `A i ε`, `i ≤ k`, has probability tending to zero as `ε ↓ 0`, so does their union. -/
theorem tendsto_measure_biUnion_range_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (A : ℕ → ℝ → Set Ω) (k : ℕ)
    (hA : ∀ i ≤ k, Tendsto (fun ε => P (A i ε)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => P (⋃ i ∈ Finset.range (k + 1), A i ε)) (𝓝[>] 0) (𝓝 0) := by
  have hsum : Tendsto (fun ε => ∑ i ∈ Finset.range (k + 1), P (A i ε)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (k + 1))
      (fun i hi => hA i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => ?_)
  exact measure_biUnion_finset_le _ _

end MatedCRT.S5c
