import MatedCRT.FirstPass.Derived.PlanarBrownianStoppingTimeTrial
import MatedCRT.FirstPass.Derived.ContinuousPathVisitTimes
import LatticeProb.Prob.GeometricTrialsFrequently

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

end MatedCRT.KilledOccupation
