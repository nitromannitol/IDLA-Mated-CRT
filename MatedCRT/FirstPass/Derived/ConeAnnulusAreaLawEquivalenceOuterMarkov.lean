import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterStop
import LatticeProb.Prob.BrownianDriftSurvival

/-!
# The Markov property at a fixed time and the survival of the drifted path

Let `b` be a Brownian motion with continuous paths, `v > 0`, `N ≥ 0`, `S ≥ 0` and `A` a measurable
set of paths. If the window `outerWindowOfPath S` of the drifted path `t ↦ b_t + v t` lies in `A` with
probability zero, then the drifted path stopped at `N` lies in `stoppedWindowEvent N S A` with
probability zero (`measure_stopped_event_eq_zero`).

Proof. The path of `b` stopped at `N` is independent of the increments of `b` after `N`, which have the
law of `b` (the Markov property at the fixed time `N`, `LatticeProb.map_pair_restart_path`). Cut the
event along the value `z N ≥ 1/(k+1)` of the stopped drifted path. On the intersection with the event
that the increments `r` of `b` after `N` satisfy `r t + v t ≥ -1/(2(k+1))` for all `t`, the drifted path
is positive from time `N` on, so the window of the whole path lies in `A`
(`window_mem_of_stopped`). The increments satisfy this with probability at least
`1 - exp(-v/(k+1)) > 0`, the survival probability of Brownian motion with drift
(`LatticeProb.measure_forall_drift_gt`). Hence the probability of the stopped event cut along
`z N ≥ 1/(k+1)` is zero for every `k`.

Source: the weak Markov property of Brownian motion at a fixed time (for example Le Gall, *Brownian
Motion, Martingales, and Stochastic Calculus*, Springer GTM 274, 2016, Chapter 2); the survival
probability `1 - exp(-2 v δ)` of Brownian motion with drift `v` is the standard gambler's-ruin formula
(see for example Borodin–Salminen, *Handbook of Brownian Motion*, or Revuz–Yor, *Continuous
Martingales and Brownian Motion*).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

open LatticeProb

/-- **The Markov property at the fixed time `N` for the window event.** -/
theorem measure_stopped_event_eq_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    (hm : ∀ t, Measurable (b t)) (hc : ∀ ω, Continuous fun t => b t ω) {v S : ℝ} (hv : 0 < v)
    {A : Set (ℝ≥0 → ℝ)} (hA : MeasurableSet A) (N : ℝ≥0)
    (h0 : P {ω | outerWindowOfPath S (fun t => driftMap v (pathMap b hc ω) t) ∈ A} = 0) :
    P {ω | stopAt (N : ℝ≥0∞) (driftMap v (pathMap b hc ω)) ∈ stoppedWindowEvent N S A} = 0 := by
  have hpmm : Measurable (pathMap b hc) := measurable_pathMap b hm hc
  let 𝔽 := natFiltration (liftOne b) (stronglyMeasurable_liftOne hm)
  have hσ : IsStoppingTime 𝔽 fun _ : Ω => (((N : ℝ≥0) : ℝ≥0∞)) := isStoppingTime_const 𝔽 N
  let Y : Ω → C(ℝ≥0, ℝ) := fun ω => stopAt (N : ℝ≥0∞) (pathMap b hc ω)
  have hY : Measurable[hσ.measurableSpace] Y :=
    measurable_stopAt_pathMap (stronglyAdapted_natFiltration_real hm) hc hσ
  have hYm : Measurable Y := measurable_stopAt_pathMap_const hm hc N
  have hRm : Measurable fun ω => restartAt N (pathMap b hc ω) :=
    measurable_restartAt_pathMap hm hc (σ := fun _ => N) measurable_const
  have hpair : Measure.map (fun ω => (Y ω, restartAt N (pathMap b hc ω))) P =
      (Measure.map Y P).prod (Measure.map (pathMap b hc) P) := by
    have h := map_pair_restart_path hb hm hc (σ := fun _ => N) hσ hY
      (E := Set.univ) MeasurableSet.univ
    rwa [Measure.restrict_univ] at h
  have hZ : ∀ ω, stopAt (N : ℝ≥0∞) (driftMap v (pathMap b hc ω)) = driftStop v N (Y ω) :=
    fun ω => stopAt_driftMap v N _
  have hEk : ∀ k : ℕ, P {ω | driftStop v N (Y ω) ∈ stoppedWindowEvent N S A ∧
      1 / ((k : ℝ) + 1) ≤ driftStop v N (Y ω) N} = 0 := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set F : Set C(ℝ≥0, ℝ) := {z | z ∈ stoppedWindowEvent N S A ∧ δ ≤ z N} with hF
    have hFN : MeasurableSet {z : C(ℝ≥0, ℝ) | δ ≤ z N} :=
      measurableSet_le measurable_const (continuous_eval_const N).measurable
    have hFm : MeasurableSet F := (measurableSet_stoppedWindowEvent N S hA).inter hFN
    set U : Set C(ℝ≥0, ℝ) := driftStop v N ⁻¹' F with hU
    have hUm : MeasurableSet U := measurable_driftStop v N hFm
    set G : Set C(ℝ≥0, ℝ) := {r | ∀ t : ℝ≥0, -(δ / 2) ≤ r t + v * t} with hG
    have hGc : IsClosed G := by
      have : G = ⋂ t : ℝ≥0, {r : C(ℝ≥0, ℝ) | -(δ / 2) ≤ r t + v * t} := by
        ext r
        simp [hG]
      rw [this]
      exact isClosed_iInter fun t => isClosed_le continuous_const
        ((continuous_eval_const t).add continuous_const)
    have hGm : MeasurableSet G := hGc.measurableSet
    have hGpos : (P.map (pathMap b hc)) G ≠ 0 := by
      rw [Measure.map_apply hpmm hGm]
      have hsurv := measure_forall_drift_gt hb.toIsPreBrownianReal hm hc hv
        (δ := δ / 2) (by positivity)
      have hmono : P {ω | ∀ t : ℝ≥0, -(δ / 2) < b t ω + v * t} ≤ P (pathMap b hc ⁻¹' G) :=
        measure_mono fun ω hω t => (hω t).le
      rw [hsurv] at hmono
      refine (lt_of_lt_of_le ?_ hmono).ne'
      rw [ENNReal.ofReal_pos]
      have : Real.exp (-(2 * v * (δ / 2))) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith [mul_pos hv hδpos]
      linarith
    have hrect : P ((fun ω => (Y ω, restartAt N (pathMap b hc ω))) ⁻¹' (U ×ˢ G)) =
        P (Y ⁻¹' U) * (P.map (pathMap b hc)) G := by
      rw [← Measure.map_apply (hYm.prodMk hRm) (hUm.prod hGm), hpair, Measure.prod_prod,
        Measure.map_apply hYm hUm]
    have hsub : (fun ω => (Y ω, restartAt N (pathMap b hc ω))) ⁻¹' (U ×ˢ G) ⊆
        {ω | outerWindowOfPath S (fun t => driftMap v (pathMap b hc ω) t) ∈ A} := by
      intro ω hω
      obtain ⟨hωU, hωG⟩ := hω
      have hzF : driftStop v N (Y ω) ∈ F := hωU
      obtain ⟨hzE, hzN⟩ := hzF
      refine window_mem_of_stopped (x := driftMap v (pathMap b hc ω)) (N := N) ?_ ?_
      · intro s hs
        obtain ⟨t, rfl⟩ : ∃ t, s = N + t := ⟨s - N, (add_tsub_cancel_of_le hs).symm⟩
        have h1 : -(δ / 2) ≤ restartAt N (pathMap b hc ω) t + v * t := hωG t
        have h2 : driftStop v N (Y ω) N = b N ω + v * N := by
          simp [driftStop, Y]
        have h3 : restartAt N (pathMap b hc ω) t = b (N + t) ω - b N ω := rfl
        have h4 : driftMap v (pathMap b hc ω) (N + t) = b (N + t) ω + v * ((N : ℝ) + t) := by
          simp [driftMap_apply, pathMap]
        rw [h4]
        rw [h3] at h1
        rw [h2] at hzN
        nlinarith
      · rw [hZ ω]
        exact hzE
    have hzero : P (Y ⁻¹' U) * (P.map (pathMap b hc)) G = 0 :=
      hrect ▸ measure_mono_null hsub h0
    have hPU : P (Y ⁻¹' U) = 0 := by
      rcases mul_eq_zero.1 hzero with h | h
      · exact h
      · exact absurd h hGpos
    exact hPU
  have hcover : {ω | stopAt (N : ℝ≥0∞) (driftMap v (pathMap b hc ω)) ∈
      stoppedWindowEvent N S A} ⊆ ⋃ k : ℕ, {ω | driftStop v N (Y ω) ∈ stoppedWindowEvent N S A ∧
        1 / ((k : ℝ) + 1) ≤ driftStop v N (Y ω) N} := by
    intro ω hω
    rw [Set.mem_ofPred_eq, hZ] at hω
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hω.1
    exact Set.mem_iUnion.2 ⟨k, hω, hk.le⟩
  exact measure_mono_null hcover (measure_iUnion_null hEk)

end MatedCRT
