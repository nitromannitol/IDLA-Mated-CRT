import MatedCRT.FirstPass.Derived.PlanarBrownianStoppingTimeTrial
import MatedCRT.FirstPass.Derived.ContinuousPathVisitTimes
import LatticeProb.Prob.GeometricTrialsFrequently
import LatticeProb.Prob.BrownianPointPolarity
import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace

/-!
# Trials at the successive visits of a closed set by planar Brownian motion

Let `F ⊆ ℂ` be closed and let `σ_j` be the successive visit times of `F` (the first hitting time
of `F`, then the first hitting time of `F` at least one unit of time after the previous visit,
`visitTime`). Suppose that planar Brownian motion from `x` almost surely visits `F` at arbitrarily
large times, and that a path event `Γ` has probability at least `p` for planar Brownian motion
started from every point of `F`. Then:

* given the stopped sigma-algebra at `σ_j`, the path shifted at `σ_j` misses `Γ` with
  probability at most `1 - p` (strong Markov property at `σ_j`);
* if `p > 0` and `Γ` is determined by the path up to time `1`, then almost surely the shifted
  path at `σ_j` lies in `Γ` for infinitely many `j` (geometric trials: the `j`-th trial event is
  measurable for the stopped sigma-algebra at `σ_{j+1}`).

## Main results

* `planarBrownianMotion_inter_shift_visitTime_compl_le`: the trial bound at the `j`-th visit.
* `planarBrownianMotion_ae_frequently_shift_visitTime_mem`: infinitely many successful trials.
* `planarBrownianMotion_ae_forall_exists_le_norm_sub_lt`: neighbourhood recurrence of planar
  Brownian motion (from `IsBrownianSpace.ae_forall_exists_le_norm_sub_lt` through the half-speed
  coordinates `PlanarBrownianSpace.halfSpeedPath`).
* `planarBrownianMotion_ae_frequently_shift_visitTime_closedBall_mem`: infinitely many successful
  trials at the successive visits of a closed disc, with the recurrence hypothesis discharged.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open _root_.HarmonicBalls

/-- **The trial bound at the `j`-th visit of a closed set.** If planar Brownian motion from `x`
almost surely visits the closed set `F` at arbitrarily large times and the measurable path event
`Γ` has probability at least `p` from every start in `F`, then for every event `E` of the stopped
sigma-algebra at the `j`-th visit time `σ_j`,
`P^x(E ∩ {θ_{σ_j} B ∈ Γ}ᶜ) ≤ (1 - p) P^x(E)`. -/
theorem planarBrownianMotion_inter_shift_visitTime_compl_le {x : ℂ} {F : Set ℂ}
    (hF : IsClosed F)
    (hrec : ∀ᵐ ω ∂(planarBrownianMotion x), ∀ a : ℝ≥0, ∃ s : ℝ≥0, a ≤ s ∧ ω s ∈ F)
    {Γ : Set (ContinuousPath ℂ)} (hΓ : MeasurableSet Γ) {p : ℝ≥0∞}
    (hp : ∀ u ∈ F, p ≤ planarBrownianMotion u Γ) (j : ℕ) (E : Set (ContinuousPath ℂ))
    (hE : MeasurableSet[(isStoppingTime_visitTime hF j).measurableSpace] E) :
    planarBrownianMotion x
        (E ∩ {ω | ContinuousPath.shift ((visitTime F j ω).untopD 0) ω ∈ Γ}ᶜ) ≤
      (1 - p) * planarBrownianMotion x E :=
  planarBrownianMotion_inter_shift_compl_le (isStoppingTime_visitTime hF j)
    (hrec.mono fun ω hω => visitTime_lt_top hF ω hω j)
    (fun ω hlt => mem_of_visitTime_lt_top hF j ω hlt) hΓ hp hE

/-- **Infinitely many successful trials at the visits of a closed set.** If planar Brownian
motion from `x` almost surely visits the closed set `F` at arbitrarily large times, and the path
event `Γ`, determined by the path up to time `1`, has probability at least `p > 0` from every
start in `F`, then almost surely the path shifted at the `j`-th visit time `σ_j` lies in `Γ` for
infinitely many `j`. -/
theorem planarBrownianMotion_ae_frequently_shift_visitTime_mem {x : ℂ} {F : Set ℂ}
    (hF : IsClosed F)
    (hrec : ∀ᵐ ω ∂(planarBrownianMotion x), ∀ a : ℝ≥0, ∃ s : ℝ≥0, a ≤ s ∧ ω s ∈ F)
    {Γ : Set (ContinuousPath ℂ)}
    (hΓ : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) 1] Γ) {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp : ∀ u ∈ F, p ≤ planarBrownianMotion u Γ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∃ᶠ j in atTop,
      ContinuousPath.shift ((visitTime F j ω).untopD 0) ω ∈ Γ := by
  have hΓm : MeasurableSet Γ := (ContinuousPath.canonicalFiltration (alpha := ℂ)).le 1 _ hΓ
  have hq : 1 - p < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne'
  exact LatticeProb.ae_frequently_mem_of_measure_inter_compl_le
    (fun j => (isStoppingTime_visitTime hF j).measurableSpace)
    (monotone_visitTime_measurableSpace hF)
    (fun j => measurableSet_shift_visitTime_preimage hF j hΓ) hq
    (planarBrownianMotion_inter_shift_visitTime_compl_le hF hrec hΓm hp)

/-- **Neighbourhood recurrence of planar Brownian motion.** Almost surely under planar Brownian
motion from `x`, for every point `c`, every `ε > 0` and every time `a`, the path comes within
distance `ε` of `c` at some time `s ≥ a`. -/
theorem planarBrownianMotion_ae_forall_exists_le_norm_sub_lt (x : ℂ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∀ (c : ℂ) (ε : ℝ), 0 < ε → ∀ a : ℝ≥0,
      ∃ s : ℝ≥0, a ≤ s ∧ ‖ω s - c‖ < ε := by
  filter_upwards
    [(MatedCRT.PlanarBrownianSpace.isBrownianSpace_halfSpeedPath x).ae_forall_exists_le_norm_sub_lt]
    with ω hω c ε hε a
  obtain ⟨t, hat, ht⟩ := hω (MatedCRT.PlanarBrownianSpace.toEuclid (c - x)) ε hε (2 * a)
  refine ⟨2⁻¹ * t, (le_inv_mul_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2 hat, ?_⟩
  rw [MatedCRT.PlanarBrownianSpace.halfSpeedPath, ← map_sub, sub_sub_sub_cancel_right,
    LinearIsometryEquiv.norm_map] at ht
  exact ht

/-- **Infinitely many successful trials at the visits of a closed disc.** For a closed disc
`F = closedBall c r` with `r > 0` and a path event `Γ`, determined by the path up to time `1`,
of probability at least `p > 0` for planar Brownian motion from every point of `F`, almost surely
under planar Brownian motion from `x` the path shifted at the `j`-th visit time of `F` lies in `Γ`
for infinitely many `j` (the recurrence of `F` is
`planarBrownianMotion_ae_forall_exists_le_norm_sub_lt`). -/
theorem planarBrownianMotion_ae_frequently_shift_visitTime_closedBall_mem (x c : ℂ) {r : ℝ}
    (hr : 0 < r) {Γ : Set (ContinuousPath ℂ)}
    (hΓ : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) 1] Γ) {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp : ∀ u ∈ Metric.closedBall c r, p ≤ planarBrownianMotion u Γ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∃ᶠ j in atTop,
      ContinuousPath.shift ((visitTime (Metric.closedBall c r) j ω).untopD 0) ω ∈ Γ := by
  refine planarBrownianMotion_ae_frequently_shift_visitTime_mem Metric.isClosed_closedBall
    ((planarBrownianMotion_ae_forall_exists_le_norm_sub_lt x).mono fun ω hω a => ?_) hΓ hp0 hp
  obtain ⟨s, has, hs⟩ := hω c r hr a
  exact ⟨s, has, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hs.le⟩

end MatedCRT.KilledOccupation
