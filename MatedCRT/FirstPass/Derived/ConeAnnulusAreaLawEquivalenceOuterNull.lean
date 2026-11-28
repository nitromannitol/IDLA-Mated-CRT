import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterMarkov
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterCM
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial

/-!
# Null sets of the outer window for two positive drifts

Let `b` be a Brownian motion with continuous paths, `v₁, v₂ > 0`, `S ≥ 0` and `A` a measurable set of
paths. If the window after the last zero of `t ↦ b_t + v₂ t` lies in `A` with probability zero, then
so does the window after the last zero of `t ↦ b_t + v₁ t` (`measure_window_eq_zero_of_drift`).

Proof. Fix a time `N`. Almost surely the drifted path `x₁ = b + v₁ ·` is a good drift (`b_t / t → 0`,
so `x₁ → ∞`) and is positive after its last zero `ℓ`. On `{ℓ + S < N}` the window of `x₁` lies in `A`
iff the stopped path `x₁(min(·, N))` lies in the event `stoppedWindowEvent N S A`
(`window_mem_of_stopped`, `stopped_mem_of_window`), an event of the path up to time `N`. For the drift
`v₂` this event has probability zero (`measure_stopped_event_eq_zero`, the Markov property at the
time `N`: the path after `N` stays positive with positive probability). By Cameron–Martin on `[0, N]`
(`map_driftStop_absolutelyContinuous`) it has probability zero for the drift `v₁` too. Hence the
probability that the window of `x₁` lies in `A` is at most `P(ℓ + S ≥ N)`, which tends to `0` as
`N → ∞`.

Source: this is the absolute continuity of Williams' path decomposition of Brownian motion with drift
at its last zero (D. Williams, Proc. LMS 28 (1974); Rogers–Pitman, Ann. Probab. 9 (1981), Theorem 1;
Revuz–Yor VII.4) proved here directly by the Markov property and Cameron–Martin.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

open LatticeProb

/-- Almost surely the drifted path `t ↦ b_t + v t` is a good drift: continuous, zero at the origin and
`c u / u → v`. -/
theorem ae_goodDrift_path {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}
    (hb : IsBrownianReal b P) {v : ℝ} (hv : 0 < v) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.CellScaling.GoodDrift
      (fun u : ℝ => b u.toNNReal ω + v * (u.toNNReal : ℝ)) v := by
  filter_upwards [hb.cont, hb.eval_zero_ae_eq_zero, QuantumZipper.BMLLN.ae_tendsto_div_atTop hb]
    with ω hcont hzero hlln
  refine ⟨?_, ?_, hv, ?_⟩
  · exact (hcont.comp continuous_real_toNNReal).add
      (continuous_const.mul (NNReal.continuous_coe.comp continuous_real_toNNReal))
  · simp [hzero]
  · have hcomp : Tendsto (fun u : ℝ => ((u.toNNReal : ℝ≥0) : ℝ)⁻¹ * b u.toNNReal ω) atTop
        (𝓝 0) := hlln.comp tendsto_real_toNNReal_atTop
    have hsum := hcomp.add (tendsto_const_nhds (x := v))
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hu' : u ≠ 0 := hu.ne'
    simp only [Real.coe_toNNReal _ hu.le]
    field_simp

/-- **Null sets of the outer window for two positive drifts.** -/
theorem measure_window_eq_zero_of_drift {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) {v₁ v₂ S : ℝ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hS : 0 ≤ S) {A : Set (ℝ≥0 → ℝ)} (hA : MeasurableSet A)
    (h₂ : P {ω | outerWindowOfPath S (fun t => driftMap v₂ (pathMap b hc ω) t) ∈ A} = 0) :
    P {ω | outerWindowOfPath S (fun t => driftMap v₁ (pathMap b hc ω) t) ∈ A} = 0 := by
  have hpmm : Measurable (pathMap b hc) := measurable_pathMap b hm hc
  set L : Ω → ℝ := fun ω => pathLastZero (fun t => driftMap v₁ (pathMap b hc ω) t) with hL
  have hLm : Measurable L :=
    measurable_pathLastZero.comp ((measurable_driftMap v₁).comp hpmm)
  have hbad : P {ω | ¬ MatedCRTHarmonic.CellScaling.GoodDrift
      (fun u : ℝ => b u.toNNReal ω + v₁ * (u.toNNReal : ℝ)) v₁} = 0 :=
    ae_iff.1 (ae_goodDrift_path hb hv₁)
  have hZm : ∀ (v : ℝ) (N : ℝ≥0),
      Measurable fun ω => driftStop v N (stopAt (N : ℝ≥0∞) (pathMap b hc ω)) :=
    fun v N => (measurable_driftStop v N).comp (measurable_stopAt_pathMap_const hm hc N)
  have key : ∀ N : ℕ, P {ω | outerWindowOfPath S (fun t => driftMap v₁ (pathMap b hc ω) t) ∈ A} ≤
      P {ω | (N : ℝ) ≤ L ω + S} := by
    intro N
    have hE := measurableSet_stoppedWindowEvent (N : ℝ≥0) S hA
    have hZ2 := measure_stopped_event_eq_zero hb hm hc hv₂ hA (N : ℝ≥0) h₂
    have hac := map_driftStop_absolutelyContinuous hb hm hc v₁ v₂ (N : ℝ≥0)
    have hpre : ∀ v : ℝ, {ω | stopAt ((N : ℝ≥0) : ℝ≥0∞) (driftMap v (pathMap b hc ω)) ∈
        stoppedWindowEvent (N : ℝ≥0) S A} =
        (fun ω => driftStop v (N : ℝ≥0) (stopAt ((N : ℝ≥0) : ℝ≥0∞) (pathMap b hc ω))) ⁻¹'
          stoppedWindowEvent (N : ℝ≥0) S A := fun v => by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, stopAt_driftMap]
    have hZ1 : P {ω | stopAt ((N : ℝ≥0) : ℝ≥0∞) (driftMap v₁ (pathMap b hc ω)) ∈
        stoppedWindowEvent (N : ℝ≥0) S A} = 0 := by
      have h2 : (P.map fun ω => driftStop v₂ (N : ℝ≥0)
          (stopAt ((N : ℝ≥0) : ℝ≥0∞) (pathMap b hc ω))) (stoppedWindowEvent (N : ℝ≥0) S A) = 0 := by
        rw [Measure.map_apply (hZm v₂ N) hE, ← hpre v₂]
        exact hZ2
      have h1 := hac h2
      rw [Measure.map_apply (hZm v₁ N) hE, ← hpre v₁] at h1
      exact h1
    have hsub : {ω | outerWindowOfPath S (fun t => driftMap v₁ (pathMap b hc ω) t) ∈ A} ⊆
        ({ω | stopAt ((N : ℝ≥0) : ℝ≥0∞) (driftMap v₁ (pathMap b hc ω)) ∈
            stoppedWindowEvent (N : ℝ≥0) S A} ∪ {ω | (N : ℝ) ≤ L ω + S}) ∪
          {ω | ¬ MatedCRTHarmonic.CellScaling.GoodDrift
            (fun u : ℝ => b u.toNNReal ω + v₁ * (u.toNNReal : ℝ)) v₁} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hnot
      obtain ⟨⟨hn1, hn2⟩, hgd⟩ := hnot
      have hl : L ω + S < N := not_le.1 hn2
      refine hn1 (stopped_mem_of_window (x := driftMap v₁ (pathMap b hc ω)) ?_ hl hω)
      intro s hs
      have hlt : MatedCRTHarmonic.CellScaling.lastZeroR
          (fun u : ℝ => b u.toNNReal ω + v₁ * (u.toNNReal : ℝ)) < (s : ℝ) := by
        have : (N : ℝ) ≤ s := by exact_mod_cast hs
        change L ω < s
        linarith
      have := hgd.pos_of_lastZeroR_lt hlt
      simpa [driftMap_apply, pathMap] using this
    calc P {ω | outerWindowOfPath S (fun t => driftMap v₁ (pathMap b hc ω) t) ∈ A}
        ≤ P (({ω | stopAt ((N : ℝ≥0) : ℝ≥0∞) (driftMap v₁ (pathMap b hc ω)) ∈
            stoppedWindowEvent (N : ℝ≥0) S A} ∪ {ω | (N : ℝ) ≤ L ω + S}) ∪
          {ω | ¬ MatedCRTHarmonic.CellScaling.GoodDrift
            (fun u : ℝ => b u.toNNReal ω + v₁ * (u.toNNReal : ℝ)) v₁}) := measure_mono hsub
      _ ≤ P ({ω | stopAt ((N : ℝ≥0) : ℝ≥0∞) (driftMap v₁ (pathMap b hc ω)) ∈
            stoppedWindowEvent (N : ℝ≥0) S A} ∪ {ω | (N : ℝ) ≤ L ω + S}) +
          P {ω | ¬ MatedCRTHarmonic.CellScaling.GoodDrift
            (fun u : ℝ => b u.toNNReal ω + v₁ * (u.toNNReal : ℝ)) v₁} := measure_union_le _ _
      _ ≤ (P {ω | stopAt ((N : ℝ≥0) : ℝ≥0∞) (driftMap v₁ (pathMap b hc ω)) ∈
            stoppedWindowEvent (N : ℝ≥0) S A} + P {ω | (N : ℝ) ≤ L ω + S}) +
          P {ω | ¬ MatedCRTHarmonic.CellScaling.GoodDrift
            (fun u : ℝ => b u.toNNReal ω + v₁ * (u.toNNReal : ℝ)) v₁} :=
          add_le_add_left (measure_union_le _ _) _
      _ = P {ω | (N : ℝ) ≤ L ω + S} := by rw [hZ1, hbad]; simp
  have hlim : Tendsto (fun N : ℕ => P {ω | (N : ℝ) ≤ L ω + S}) atTop (𝓝 0) := by
    have hanti : Antitone fun N : ℕ => {ω | (N : ℝ) ≤ L ω + S} :=
      fun N M hNM ω hω => by
        have hω' : (M : ℝ) ≤ L ω + S := hω
        exact (le_trans (Nat.cast_le.2 hNM) hω' : (N : ℝ) ≤ L ω + S)
    have hmeas : ∀ N : ℕ, NullMeasurableSet {ω | (N : ℝ) ≤ L ω + S} P := fun N =>
      (measurableSet_le measurable_const (hLm.add_const S)).nullMeasurableSet
    have h := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ N : ℕ, {ω | (N : ℝ) ≤ L ω + S} = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      exact exists_nat_gt (L ω + S)
    rwa [hempty, measure_empty] at h
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim key)

end MatedCRT
