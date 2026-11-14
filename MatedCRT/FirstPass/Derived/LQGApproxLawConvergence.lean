import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.FieldCoordinateCircleAverages

/-!
# Convergence of the approximating Liouville Brownian motion laws in a valid mated-CRT environment

Let `S` be a valid mated-CRT environment and `H` a version of its field, so that almost surely the circle-average
process `coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))` of the field coordinates recovers the circle averages
`S.hcirc ω r z` at every positive radius `r` and every center `z`. For such a sample:

* the circle averages at each dyadic radius `2^{-n}` are continuous in the center, since the circle-average
  process of the `γ`-quantum cone is continuous in `(r, z) ∈ (0, ∞) × ℂ`;
* the LQG clock `S.clock ω` of planar Brownian motion from every `z` (`IsLQGClock`) only involves the circle
  averages at the dyadic radii, so it is also the LQG clock for the circle-average process of the coordinates
  (`isLQGClock_of_eq_dyadicScale`), and it is almost surely a time-change clock.

The weak convergence of the approximating path laws for a fixed field
(`tendsto_planarBrownianPathLaw_lqgApproxClockPlus`) then applies to every sample of a conull set and every start
`z`: the laws under planar Brownian motion from `z` of the time-changed paths `t ↦ b (A_n(b, ·)⁻¹(t))`, with the
approximating clocks `A_n` built from the circle averages of `H ω`, converge weakly to the law of the Liouville
Brownian motion path `t ↦ b ((S.clock ω b)⁻¹(t))` from `z`.

The path laws carry almost-everywhere measurability proofs which are available only on the conull set; the main
statement `MatedCRTEnv.IsValid.ae_tendsto_approxLBMLaw` provides them inside an existential, and
`MatedCRTEnv.IsValid.ae_forall_tendsto_approxLBMLaw` states the convergence for any such proofs.

Terminology: positive continuous additive functional (the LQG clock) and the time change of planar Brownian motion
(Garban–Rhodes–Vargas, *Liouville Brownian motion*, Definition 2.17; Berestycki, *Diffusion in planar Liouville
quantum gravity*, Section 2); circle average embedding of the `γ`-quantum cone (Duplantier–Miller–Sheffield,
Definition 4.10).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

/-- The LQG clock property only involves the circle averages at the dyadic radii `2^{-k}`: if two circle-average
processes agree at every dyadic radius, an LQG clock for one of them is an LQG clock for the other. -/
theorem isLQGClock_of_eq_dyadicScale {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (h : ∀ (k : ℕ) (z : ℂ), hε (dyadicScale k) z = hε' (dyadicScale k) z)
    (hF : IsLQGClock Q γ hε' x F) : IsLQGClock Q γ hε x F := by
  have hA : ∀ (k : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0),
      lqgClockApprox γ hε (dyadicScale k) b t = lqgClockApprox γ hε' (dyadicScale k) b t := by
    intro k b t
    simp only [lqgClockApprox, h]
  unfold IsLQGClock at hF ⊢
  intro T η hη
  simp only [hA]
  exact hF T η hη

section ValidEnvironment

variable {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
  {H : Ω → LQGMetric.DistC}

/-- In a valid environment, for any version `H` of the field, almost surely the circle-average process of the field
coordinates is continuous in the center at every dyadic radius `2^{-n}`. -/
theorem MatedCRTEnv.IsValid.ae_continuous_coordCircleAverage_dyadicScale (hS : S.IsValid 𝒮 γ)
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ n : ℕ, Continuous (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω)) (dyadicScale n)) := by
  filter_upwards [hS.isQuantumCone.ae_continuousOn_circle, hS.ae_coordCircleAverage_eq hH] with ω hωc hωeq n
  have hd : 0 < dyadicScale n := HarmonicBalls.dyadicScale_pos n
  have heq : coordCircleAverage (LQGMetric.pairJ ⊤ (H ω)) (dyadicScale n) = S.hcirc ω (dyadicScale n) :=
    funext fun z => hωeq _ hd z
  have hpair : Continuous fun z : ℂ => ((dyadicScale n, z) : ℝ × ℂ) := continuous_const.prodMk continuous_id
  have hc := hωc.comp_continuous hpair fun z => Set.mk_mem_prod (Set.mem_Ioi.2 hd) (Set.mem_univ z)
  rw [heq]
  exact hc

/-- In a valid environment, for any version `H` of the field, almost surely, for every start `z`, the clock
`S.clock ω` is the LQG clock of planar Brownian motion from `z` for the circle-average process of the field
coordinates, and it is almost surely (in the Brownian path) a time-change clock. -/
theorem MatedCRTEnv.IsValid.ae_isLQGClock_coordCircleAverage (hS : S.IsValid 𝒮 γ)
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ z : ℂ,
      IsLQGClock planarBrownianMotion γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) z (S.clock ω) ∧
        ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b) := by
  filter_upwards [hS.ae_coordCircleAverage_eq hH, hS.isLQGClock] with ω hωeq hωclk z
  exact ⟨isLQGClock_of_eq_dyadicScale (fun k w => hωeq _ (HarmonicBalls.dyadicScale_pos k) w) (hωclk z).1,
    (hωclk z).2⟩

/-- **Convergence of the approximating Liouville Brownian motion laws.** In a valid environment, for any version
`H` of the field, almost surely, for every start `z`: the time-changed paths `t ↦ b (A_n(b, ·)⁻¹(t))` with the
approximating clocks `A_n` of the circle averages of `H ω`, and the Liouville Brownian motion path
`t ↦ b ((S.clock ω b)⁻¹(t))`, are almost everywhere measurable under planar Brownian motion from `z`, and the laws
of the former converge weakly to the law of the latter. -/
theorem MatedCRTEnv.IsValid.ae_tendsto_approxLBMLaw (hS : S.IsValid 𝒮 γ)
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ z : ℂ,
      ∃ (hA : ∀ n : ℕ, AEMeasurable
          (lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) n))
          (planarBrownianMotion z))
        (hL : AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z)),
        Tendsto (fun n : ℕ => planarBrownianPathLaw z
            (lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) n)) (hA n))
          atTop (𝓝 (planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) hL)) := by
  filter_upwards [hS.ae_continuous_coordCircleAverage_dyadicScale hH,
    hS.ae_isLQGClock_coordCircleAverage hH] with ω hcont hclk z
  exact ⟨fun n => (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hcont n)).aemeasurable,
    aemeasurable_lbmContinuousPath (hclk z).1 (hclk z).2 hcont,
    tendsto_planarBrownianPathLaw_lqgApproxClockPlus (hclk z).1 (hclk z).2 hcont⟩

/-- **Convergence of the approximating Liouville Brownian motion laws, for any measurability proofs.** In a valid
environment, for any version `H` of the field, almost surely, for every start `z` and any almost-everywhere
measurability proofs of the time-changed paths, the laws under planar Brownian motion from `z` of the approximating
time-changed paths converge weakly to the law of the Liouville Brownian motion path. -/
theorem MatedCRTEnv.IsValid.ae_forall_tendsto_approxLBMLaw (hS : S.IsValid 𝒮 γ)
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ z : ℂ,
      ∀ (hA : ∀ n : ℕ, AEMeasurable
          (lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) n))
          (planarBrownianMotion z))
        (hL : AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z)),
        Tendsto (fun n : ℕ => planarBrownianPathLaw z
            (lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) n)) (hA n))
          atTop (𝓝 (planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) hL)) := by
  filter_upwards [hS.ae_tendsto_approxLBMLaw hH] with ω hω z hA hL
  obtain ⟨_, _, h⟩ := hω z
  exact h

end ValidEnvironment

end MatedCRT
