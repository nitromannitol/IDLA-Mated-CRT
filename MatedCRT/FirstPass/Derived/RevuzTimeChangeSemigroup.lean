import MatedCRT.FirstPass.Derived.RevuzMarkovAgainstClock
import MatedCRT.FirstPass.Derived.RevuzRegularize

/-!
# The semigroup property of the time change of planar Brownian motion by a PCAF

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock
and let `τ_u = inf {t | u < A_t}` be the right inverse of the clock.  The time-changed process
`Y_u = B_{τ_u}` has the transition kernels `P_u(y, S) = P_y[B_{τ_u} ∈ S]`, and they form a
semigroup (Revuz–Yor (1999), Chapter X, §1; Fukushima–Oshima–Takeda (2011), §6.2):
`P_{v+u}(z, S) = ∫ P_u(y, S) P_v(z, dy)`.  The proof is the strong Markov property at the optional
time `τ_v` together with the additivity `B_{τ_{v+u}} = (θ_{τ_v} B)_{τ_u ∘ θ_{τ_v}}`.

The event `{B_{τ_u} ∈ S}` is written with the raw clock and need not be measurable.  For every
starting point it agrees almost surely with the measurable event written with the rational-time
regularization `Ā` of the clock, and the kernel `timeChangeKernel A u` is built on the latter.

## Main statements

* `planarLaw_eval_clockInverse_add_mem`: `P_z[B_{τ_{v+u}} ∈ S] = E_z[P_{B_{τ_v}}[B_{τ_u} ∈ S]]`.
* `timeChangeKernel_apply`: `P_u(y, S) = P_y[B_{τ_u} ∈ S]` for Borel `S`.
* `timeChangeKernel_add`: `P_{v+u} = P_u ∘ₖ P_v`.
* `isInvTC_iff`: a measure `ν` is invariant for the time change iff `P_u ∘ₘ ν = ν` for every `u`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open _root_.HarmonicBalls

/-- The time-changed position `B_{τ_u}`, computed with the rational-time regularization `Ā` of the
clock. -/
noncomputable def timeChangeRegularized (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0)
    (ω : ContinuousPath ℂ) : ℂ :=
  ω (clockInverse (regularize A) u ω)

/-- Joint measurability of the evaluation `(t, ω) ↦ ω t` of the canonical planar path. -/
theorem measurable_path_eval_uncurry :
    Measurable fun p : ℝ≥0 × ContinuousPath ℂ => p.2 p.1 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t)
    (fun ω => ω.continuous) (fun t => (continuous_eval_const t).measurable)

/-- The regularized time-changed position is measurable. -/
theorem measurable_timeChangeRegularized {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (u : ℝ≥0) : Measurable (timeChangeRegularized A u) := by
  have h1 : Measurable fun ω : ContinuousPath ℂ => clockInverse (regularize A) u ω :=
    (measurable_clockInverse_uncurry (measurable_regularize hA) (regularize_monotone A)).comp
      (measurable_const.prodMk measurable_id)
  exact measurable_path_eval_uncurry.comp (h1.prodMk measurable_id)

/-- Almost surely, the raw and the regularized time-changed positions agree at every level. -/
theorem ae_eval_clockInverse_eq_timeChangeRegularized {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (y : ℂ) :
    ∀ᵐ ω ∂planarLaw y, ∀ u, ω (clockInverse A u ω) = timeChangeRegularized A u ω := by
  filter_upwards [ae_clockInverse_regularize_eq hA y] with ω h u
  rw [timeChangeRegularized, h u]

/-- The probability that the time-changed path lies in `S` at level `u` is the probability of the
measurable event written with the regularized clock. -/
theorem planarLaw_eval_clockInverse_mem {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (y : ℂ) (u : ℝ≥0) (S : Set ℂ) :
    planarLaw y {ω | ω (clockInverse A u ω) ∈ S} =
      planarLaw y (timeChangeRegularized A u ⁻¹' S) := by
  refine measure_congr ?_
  filter_upwards [ae_eval_clockInverse_eq_timeChangeRegularized hA y] with ω h
  show (ω (clockInverse A u ω) ∈ S) = (timeChangeRegularized A u ω ∈ S)
  rw [h u]

/-- The time-changed position at a fixed level is almost everywhere measurable. -/
theorem aemeasurable_eval_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) (u : ℝ≥0) :
    AEMeasurable (fun ω : ContinuousPath ℂ => ω (clockInverse A u ω)) (planarLaw z) :=
  ⟨timeChangeRegularized A u, measurable_timeChangeRegularized hA.meas u, by
    filter_upwards [ae_eval_clockInverse_eq_timeChangeRegularized hA z] with ω h using h u⟩

/-- **The transition kernel of the time change**: `P_u(y, ·)` is the law of `B_{τ_u}` under `P_y`,
computed with the regularized clock. -/
noncomputable def timeChangeKernel (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0) : Kernel ℂ ℂ :=
  planarBrownianMotion.map (timeChangeRegularized A u)

/-- `P_u(y, S) = P_y[B_{τ_u} ∈ S]` for a Borel set `S`. -/
theorem timeChangeKernel_apply {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (u : ℝ≥0) (y : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    timeChangeKernel A u y S = planarLaw y {ω | ω (clockInverse A u ω) ∈ S} := by
  rw [timeChangeKernel, Kernel.map_apply' _ (measurable_timeChangeRegularized hA.meas u) y hS]
  exact (planarLaw_eval_clockInverse_mem hA y u S).symm

/-- `P_u(y, ·)` is the image of `P_y` under the raw time-changed position `B_{τ_u}`. -/
theorem timeChangeKernel_eq_map {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (u : ℝ≥0) (y : ℂ) :
    timeChangeKernel A u y = (planarLaw y).map fun ω => ω (clockInverse A u ω) := by
  rw [timeChangeKernel, Kernel.map_apply _ (measurable_timeChangeRegularized hA.meas u)]
  refine Measure.map_congr ?_
  filter_upwards [ae_eval_clockInverse_eq_timeChangeRegularized hA y] with ω h
  exact (h u).symm

/-- The hitting probability `y ↦ P_y[B_{τ_u} ∈ S]` of the time change is measurable. -/
theorem measurable_planarLaw_eval_clockInverse_mem {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    Measurable fun y => planarLaw y {ω | ω (clockInverse A u ω) ∈ S} := by
  have h : (fun y => planarLaw y {ω | ω (clockInverse A u ω) ∈ S}) =
      fun y => timeChangeKernel A u y S :=
    funext fun y => (timeChangeKernel_apply hA u y hS).symm
  rw [h]
  exact Kernel.measurable_coe _ hS

/-- **The semigroup property of the time change**, pathwise form.  For a PCAF of planar Brownian
motion with a good clock, `P_z[B_{τ_{v+u}} ∈ S] = E_z[P_{B_{τ_v}}[B_{τ_u} ∈ S]]`. -/
theorem planarLaw_eval_clockInverse_add_mem {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (v u : ℝ≥0) {S : Set ℂ}
    (hS : MeasurableSet S) :
    planarLaw z {ω | ω (clockInverse A (v + u) ω) ∈ S} =
      ∫⁻ ω, planarLaw (ω (clockInverse A v ω)) {ω' | ω' (clockInverse A u ω') ∈ S}
        ∂planarLaw z := by
  have hEm : MeasurableSet (timeChangeRegularized A u ⁻¹' S) :=
    measurable_timeChangeRegularized hA.meas u hS
  have hH : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      (timeChangeRegularized A u ⁻¹' S).indicator (1 : ContinuousPath ℂ → ℝ≥0∞) p.2 :=
    (measurable_one.indicator hEm).comp measurable_snd
  have key : ∫⁻ ω, (timeChangeRegularized A u ⁻¹' S).indicator (1 : ContinuousPath ℂ → ℝ≥0∞)
        (ContinuousPath.shift (clockInverse A v ω) ω) ∂planarLaw z =
      ∫⁻ ω, ∫⁻ ω', (timeChangeRegularized A u ⁻¹' S).indicator (1 : ContinuousPath ℂ → ℝ≥0∞) ω'
        ∂planarLaw (ω (clockInverse A v ω)) ∂planarLaw z :=
    lintegral_shift_clockInverse_eq hA hG z v hH
  calc planarLaw z {ω | ω (clockInverse A (v + u) ω) ∈ S}
      = planarLaw z (timeChangeRegularized A (v + u) ⁻¹' S) :=
        planarLaw_eval_clockInverse_mem hA z _ S
    _ = ∫⁻ ω, (timeChangeRegularized A (v + u) ⁻¹' S).indicator
          (1 : ContinuousPath ℂ → ℝ≥0∞) ω ∂planarLaw z :=
        (lintegral_indicator_one (measurable_timeChangeRegularized hA.meas _ hS)).symm
    _ = ∫⁻ ω, (timeChangeRegularized A u ⁻¹' S).indicator (1 : ContinuousPath ℂ → ℝ≥0∞)
          (ContinuousPath.shift (clockInverse A v ω) ω) ∂planarLaw z := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_eval_clockInverse_eq_timeChangeRegularized hA z,
          ae_eval_clockInverse_add_eq_shift hA hG z v] with ω h1 h2
        have h3 : timeChangeRegularized A (v + u) ω =
            timeChangeRegularized A u (ContinuousPath.shift (clockInverse A v ω) ω) :=
          (h1 (v + u)).symm.trans (h2 u)
        by_cases hm : timeChangeRegularized A (v + u) ω ∈ S
        · have hm' : timeChangeRegularized A u (ContinuousPath.shift (clockInverse A v ω) ω) ∈ S :=
            h3 ▸ hm
          exact (Set.indicator_of_mem (s := timeChangeRegularized A (v + u) ⁻¹' S) (a := ω) hm
            1).trans (Set.indicator_of_mem (s := timeChangeRegularized A u ⁻¹' S)
              (a := ContinuousPath.shift (clockInverse A v ω) ω) hm' 1).symm
        · have hm' : timeChangeRegularized A u (ContinuousPath.shift (clockInverse A v ω) ω) ∉ S :=
            h3 ▸ hm
          exact (Set.indicator_of_notMem (s := timeChangeRegularized A (v + u) ⁻¹' S) (a := ω) hm
            1).trans (Set.indicator_of_notMem (s := timeChangeRegularized A u ⁻¹' S)
              (a := ContinuousPath.shift (clockInverse A v ω) ω) hm' 1).symm
    _ = _ := key
    _ = _ := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_indicator_one hEm, planarLaw_eval_clockInverse_mem hA]

/-- **The semigroup property of the time change**, image-measure form:
`P_z[B_{τ_{v+u}} ∈ S] = ∫ P_y[B_{τ_u} ∈ S] d(P_z ∘ B_{τ_v}⁻¹)(y)`. -/
theorem planarLaw_eval_clockInverse_add_mem_eq_lintegral_map {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (v u : ℝ≥0) {S : Set ℂ}
    (hS : MeasurableSet S) :
    planarLaw z {ω | ω (clockInverse A (v + u) ω) ∈ S} =
      ∫⁻ y, planarLaw y {ω' | ω' (clockInverse A u ω') ∈ S}
        ∂(planarLaw z).map fun ω => ω (clockInverse A v ω) := by
  rw [lintegral_map' (measurable_planarLaw_eval_clockInverse_mem hA u hS).aemeasurable
    (aemeasurable_eval_clockInverse hA z v)]
  exact planarLaw_eval_clockInverse_add_mem hA hG z v u hS

/-- **The time-change kernels form a semigroup**: `P_{v+u} = P_u ∘ₖ P_v`. -/
theorem timeChangeKernel_add {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (hG : GoodClock planarLaw A) (v u : ℝ≥0) :
    timeChangeKernel A (v + u) = timeChangeKernel A u ∘ₖ timeChangeKernel A v := by
  ext z S hS
  rw [Kernel.comp_apply' _ _ z hS, timeChangeKernel_apply hA _ z hS,
    planarLaw_eval_clockInverse_add_mem_eq_lintegral_map hA hG z v u hS,
    timeChangeKernel_eq_map hA v z]
  exact lintegral_congr fun y => (timeChangeKernel_apply hA u y hS).symm

/-- The semigroup property acting on measures: `ν P_{v+u} = (ν P_v) P_u`. -/
theorem comp_timeChangeKernel_add {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (hG : GoodClock planarLaw A) (ν : Measure ℂ) (v u : ℝ≥0) :
    timeChangeKernel A (v + u) ∘ₘ ν = timeChangeKernel A u ∘ₘ (timeChangeKernel A v ∘ₘ ν) := by
  rw [Measure.comp_assoc, timeChangeKernel_add hA hG v u]

/-- The integrated hitting probability of the time change is the image measure `ν P_u`. -/
theorem lintegral_planarLaw_eval_clockInverse_mem {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (ν : Measure ℂ) (u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ z, planarLaw z {ω | ω (clockInverse A u ω) ∈ S} ∂ν = (timeChangeKernel A u ∘ₘ ν) S := by
  rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
  exact lintegral_congr fun z => (timeChangeKernel_apply hA u z hS).symm

/-- A measure is invariant for the time change iff it is fixed by every time-change kernel. -/
theorem isInvTC_iff {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (ν : Measure ℂ) :
    IsInvTC planarLaw A ν ↔ ∀ u, timeChangeKernel A u ∘ₘ ν = ν := by
  constructor
  · intro h u
    ext S hS
    rw [← lintegral_planarLaw_eval_clockInverse_mem hA ν u hS]
    exact h u S hS
  · intro h u S hS
    rw [lintegral_planarLaw_eval_clockInverse_mem hA ν u hS, h u]

end MatedCRT
