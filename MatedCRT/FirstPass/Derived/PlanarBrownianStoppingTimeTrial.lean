import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar
import MarkovProcess.Trajectory.StoppingLtTop

/-!
# A failed trial after a stopping time for planar Brownian motion

Let `τ` be a stopping time of the canonical filtration, almost surely finite for planar Brownian
motion started from `x`, at which the path lies in a set `D` of starting points. If a measurable
path event `Γ` has probability at least `p` for planar Brownian motion started from every point
of `D`, then for every event `A` of the stopped sigma-algebra, the path shifted at `τ` misses `Γ`
on `A` with probability at most `(1 - p) P^x(A)`.

This is the strong Markov property at `τ` in restart form
(`continuousProcess_restrict_map_shift_stoppingTime_lt_top`): the law of the shifted path on
`A ∩ {τ < ∞}` is the mixture of the laws of planar Brownian motion started from `B_τ`. It is the
trial bound of the geometric-trials argument for the divergence of an additive functional at the
successive visits of a disc.

## Main results

* `planarBrownianMotion_inter_shift_compl_le`: the one-trial bound.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open _root_.HarmonicBalls

/-- **A failed trial after a stopping time.** Let `τ` be a stopping time of the canonical
filtration that is almost surely finite under planar Brownian motion from `x`, with `B_τ ∈ D`
whenever `τ < ∞`, and let `Γ` be a measurable path event of probability at least `p` from every
start in `D`. Then for every event `A` of the stopped sigma-algebra,
`P^x(A ∩ {θ_τ B ∉ Γ}) ≤ (1 - p) P^x(A)` (strong Markov property at `τ`). -/
theorem planarBrownianMotion_inter_shift_compl_le {x : ℂ}
    {τ : ContinuousPath ℂ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) τ)
    (hfin : ∀ᵐ ω ∂(planarBrownianMotion x), τ ω < ⊤)
    {D : Set ℂ} (hD : ∀ ω, τ ω < ⊤ → ω ((τ ω).untopD 0) ∈ D)
    {Γ : Set (ContinuousPath ℂ)} (hΓ : MeasurableSet Γ) {p : ℝ≥0∞}
    (hp : ∀ u ∈ D, p ≤ planarBrownianMotion u Γ)
    {A : Set (ContinuousPath ℂ)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    planarBrownianMotion x
        (A ∩ (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' Γᶜ) ≤
      (1 - p) * planarBrownianMotion x A := by
  set T : Set (ContinuousPath ℂ) := {ω | τ ω < ⊤} with hT_def
  have hTm : MeasurableSet T :=
    hτ.measurableSpace_le _ (StoppingTime.measurableSet_stoppingTime_lt_top hτ)
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      x τ hτ A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m Γᶜ) hrestart
  rw [Measure.map_apply hshift hΓ.compl, Measure.bind_apply hΓ.compl (Kernel.aemeasurable _),
    Measure.restrict_apply (hshift hΓ.compl)] at happ
  simp only [Kernel.comap_apply] at happ
  have hre : (planarBrownianMotion x).restrict T = planarBrownianMotion x :=
    Measure.restrict_eq_self_of_ae_mem hfin
  calc planarBrownianMotion x
        (A ∩ (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' Γᶜ)
      = planarBrownianMotion x
          ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' Γᶜ ∩ (A ∩ T)) := by
        conv_lhs => rw [← hre]
        rw [Measure.restrict_apply' hTm]
        congr 1
        ext ω
        simp only [mem_inter_iff, mem_preimage]
        tauto
    _ = ∫⁻ ω in A ∩ T, planarBrownianMotion (ω ((τ ω).untopD 0)) Γᶜ ∂(planarBrownianMotion x) :=
        happ
    _ ≤ ∫⁻ _ in A ∩ T, (1 - p) ∂(planarBrownianMotion x) := by
        refine setLIntegral_mono' (hAm.inter hTm) fun ω hω => ?_
        rw [prob_compl_eq_one_sub hΓ]
        exact tsub_le_tsub_left (hp _ (hD ω hω.2)) 1
    _ = (1 - p) * planarBrownianMotion x (A ∩ T) := setLIntegral_const _ _
    _ ≤ (1 - p) * planarBrownianMotion x A :=
        mul_le_mul' le_rfl (measure_mono inter_subset_left)

end MatedCRT.KilledOccupation
