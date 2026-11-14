import HarmonicBalls.Proofs.Sec6.AvoidanceDiscRestart

/-!
# Restarting the Brownian exit point at an inner exit time

For an open set `U` and an open set `V` whose exit time comes strictly before the (finite) exit
time from `U`, the strong Markov property at the exit time `σ` of `V` gives the harmonic-measure
identity
`P_y(B_{τ_U} ∈ A) = E_y[P_{B_σ}(B_{τ_U} ∈ A)]`.
This is the first step towards the continuity of Euclidean harmonic measure in the base point
(Gwynne-Miller-Sheffield, invariance principle, proof of Lemma 3.14).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6

namespace MatedCRT

/-- Shifting a path by a time strictly before its finite exit time from `U` does not change the
exit point. -/
theorem exitPoint_shift {U : Set ℂ} (ω : ContinuousPath ℂ) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U ω)
    (hfin : ContinuousPath.exitTime U ω ≠ ⊤) :
    ContinuousPath.shift t ω ((ContinuousPath.exitTime U (ContinuousPath.shift t ω)).toNNReal) =
      ω ((ContinuousPath.exitTime U ω).toNNReal) := by
  have h := ContinuousPath.exitTime_shift_add U ω t ht
  have hs : ContinuousPath.exitTime U (ContinuousPath.shift t ω) ≠ ⊤ := by
    intro h'
    rw [h', top_add] at h
    exact hfin h.symm
  rw [ContinuousPath.shift_apply, ← h, ENNReal.toNNReal_add hs ENNReal.coe_ne_top,
    ENNReal.toNNReal_coe, add_comm]

/-- **Strong Markov restart of the exit point.**  If, `P_y`-almost surely, the exit time `σ` of
the open set `V` is finite and strictly smaller than the exit time of `U`, and the latter is
finite, then the exit distribution of `U` from `y` is the mixture of the exit distributions of
`U` from the exit point of `V`. -/
theorem planarBrownian_exitPoint_restart {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {y : ℂ}
    (hfin : ∀ᵐ ω ∂(planarBrownianMotion y), ContinuousPath.exitTime V ω < ⊤)
    (hlt : ∀ᵐ ω ∂(planarBrownianMotion y),
      ContinuousPath.exitTime V ω < ContinuousPath.exitTime U ω)
    (hUfin : ∀ᵐ ω ∂(planarBrownianMotion y), ContinuousPath.exitTime U ω ≠ ⊤)
    {A : Set ℂ} (hA : MeasurableSet A) :
    planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} =
      ∫⁻ ω, planarBrownianMotion (ω ((ContinuousPath.exitTime V ω).toNNReal))
        {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} ∂(planarBrownianMotion y) := by
  let E : Set (ContinuousPath ℂ) := {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime V
  have hτ := ContinuousPath.isStoppingTime_exitTime V hV
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hE : MeasurableSet E := hmU hA
  have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      y τ hτ univ (by simp)
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  simp only [univ_inter] at hrestart
  have hre : (planarBrownianMotion y).restrict {ω | (τ ω : WithTop ℝ≥0) < ⊤} =
      planarBrownianMotion y :=
    Measure.restrict_eq_self_of_ae_mem hfin
  change ((planarBrownianMotion y).restrict {ω | τ ω < ⊤}).map
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
    Kernel.comap planarBrownianMotion (fun ω => ω ((τ ω).untopD 0))
      (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ) ∘ₘ
        ((planarBrownianMotion y).restrict {ω | τ ω < ⊤}) at hrestart
  rw [hre] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m E) hrestart
  rw [Measure.map_apply hshift hE, Measure.bind_apply hE (Kernel.aemeasurable _)] at happ
  simp only [Kernel.comap_apply] at happ
  calc
    planarBrownianMotion y E = planarBrownianMotion y
        ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' E) := by
      apply measure_congr
      filter_upwards [hfin, hlt, hUfin] with ω hf hl hu
      have hcoe : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) = τ ω := by
        exact ENNReal.coe_toNNReal hf.ne
      have hpt := exitPoint_shift (U := U) ω ((τ ω).untopD 0) (by rw [hcoe]; exact hl) hu
      change (ω ∈ E) = (ContinuousPath.shift ((τ ω).untopD 0) ω ∈ E)
      simp only [E, Set.mem_ofPred_eq, hpt]
    _ = ∫⁻ ω, planarBrownianMotion (ω ((τ ω).untopD 0)) E ∂(planarBrownianMotion y) := happ
    _ = _ := by rfl

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.planarBrownian_exitPoint_restart
