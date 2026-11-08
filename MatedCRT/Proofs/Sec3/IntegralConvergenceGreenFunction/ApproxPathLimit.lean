import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathMeasurable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockSubsequence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffPathUniform
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GridStepApprox
import MatedCRT.Defs.Setting

/-!
# Lemma 3.4 (item 4): the bounded Lipschitz functional of the approximate and of the Liouville Brownian paths

Measurability in the Brownian path of a bounded Lipschitz functional `F` of the time-changed path, for an environment with
continuous circle averages (paper argument, `docs/campaign/GAPS-SEC3.md` item 4):

* for the approximate time-changed path `t ↦ b (cutInv (clock b) n (m t))`, the functional is measurable in `b`: it is the
  pointwise limit of the functionals of grid step paths, which depend measurably on finitely many evaluations of `b`;
* the functional of the Liouville Brownian path `t ↦ b (clockInverse (clock b) (m t))` is almost surely strongly measurable for
  the Brownian law: along a subsequence chosen by Borel–Cantelli, the approximate paths converge in the local uniform distance
  almost surely, so the limit functional is an almost sure limit of measurable functions.

The first clause of `LBMPathFunctionalMeasurableStep` follows for every valid environment. The second clause (measurability of the
expectations in the environment) is not proved here.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

section Grid

variable {γ ε : ℝ} {hε : ℝ → ℂ → ℝ}

/-- The bounded Lipschitz functional of the approximate time-changed path is measurable in the Brownian path. -/
theorem measurable_boundedLipschitz_approxPath {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    (hε0 : 0 < ε) (hcont : Continuous (hε ε)) (n m : ℝ≥0) :
    Measurable fun b : ContinuousPath ℂ =>
      F (fun t : ℝ≥0 => b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε b s) n (m * t))) := by
  have hLip := hF
  obtain ⟨-, L, hL⟩ := hLip
  have hmeasN : ∀ N : ℕ, Measurable fun b : ContinuousPath ℂ =>
      F (stepPath N fun j : ℕ =>
        b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε b s) n (m * ((j : ℝ≥0) / (N : ℝ≥0))))) := by
    intro N
    have hvec : Measurable fun b : ContinuousPath ℂ => fun j : ℕ =>
        b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε b s) n (m * ((j : ℝ≥0) / (N : ℝ≥0)))) :=
      measurable_pi_iff.mpr fun j => measurable_approxPath_eval hε0 hcont n (m * ((j : ℝ≥0) / (N : ℝ≥0)))
    exact (continuous_boundedLipschitz_stepPath hF N).measurable.comp hvec
  refine measurable_of_tendsto_metrizable hmeasN ?_
  rw [tendsto_pi_nhds]
  intro b
  have hc := continuous_approxPath (γ := γ) hε0 hcont b n m
  have hd := (tendsto_localUniformDist_gridStep hc).const_mul L
  rw [mul_zero] at hd
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hd
  rw [Real.dist_eq]
  exact hL _ _

end Grid

/-- **Almost sure strong measurability of the limit path functional.** Let the approximate clocks `lqgClockApprox γ H (dyadicScale k)`
converge in probability to `G`, uniformly on compact time intervals (the form of `IsLQGClock`), and let `G b` be a time change clock
for `μ`-almost every path. Then the bounded Lipschitz functional of the Liouville Brownian path `t ↦ b (clockInverse (G b) (m t))` is
almost surely strongly measurable for `μ`. -/
theorem aestronglyMeasurable_boundedLipschitz_limitPath {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    {γ : ℝ} {H : ℝ → ℂ → ℝ} (hH : ∀ k : ℕ, Continuous (H (dyadicScale k)))
    {G : ContinuousPath ℂ → ℝ≥0 → ℝ} (μ : Measure (ContinuousPath ℂ))
    (hconv : ∀ (T : ℝ≥0) (η : ℝ), 0 < η → Tendsto (fun k : ℕ =>
      μ {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ H (dyadicScale k) b t - G b t|}) atTop (𝓝 0))
    (hTC : ∀ᵐ b ∂μ, IsTimeChangeClock (G b)) (m : ℝ≥0) :
    AEStronglyMeasurable (fun b : ContinuousPath ℂ => F (fun t : ℝ≥0 => b (clockInverse (G b) (m * t)))) μ := by
  have hLip := hF
  obtain ⟨-, L, hL⟩ := hLip
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_forall_eventually_close μ
    (fun k b t => lqgClockApprox γ H (dyadicScale k) b t) G hconv
  have hcut : ∀ᵐ b ∂μ, Tendsto (fun j : ℕ => localUniformDist
      (fun t : ℝ≥0 => b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ H (dyadicScale (φ j)) b s) ((φ j : ℕ) : ℝ≥0) (m * t)))
      (fun t : ℝ≥0 => b (clockInverse (G b) (m * t)))) atTop (𝓝 0) := by
    filter_upwards [hae, hTC] with b hb hTCb
    have hc : ∀ T : ℝ≥0, ∀ᶠ j : ℕ in atTop, T ≤ ((φ j : ℕ) : ℝ≥0) := by
      intro T
      filter_upwards [eventually_ge_atTop ⌈T⌉₊] with j hj
      exact (Nat.le_ceil T).trans ((Nat.cast_le.2 hj).trans (Nat.cast_le.2 (hφ.id_le j)))
    exact cutoffPath_tendsto_localUniformDist hTCb
      (F := fun j t => lqgClockApprox γ H (dyadicScale (φ j)) b t)
      (fun j => strictMono_lqgClockApprox (dyadicScale_pos (φ j)) (hH (φ j)) b)
      (fun j => ((φ j : ℕ) : ℝ≥0)) hc (fun T η hη => hb T η hη) b m
  have hmeas : ∀ j : ℕ, AEStronglyMeasurable (fun b : ContinuousPath ℂ =>
      F (fun t : ℝ≥0 => b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ H (dyadicScale (φ j)) b s) ((φ j : ℕ) : ℝ≥0)
        (m * t)))) μ :=
    fun j => (measurable_boundedLipschitz_approxPath hF (dyadicScale_pos (φ j)) (hH (φ j))
      ((φ j : ℕ) : ℝ≥0) m).aestronglyMeasurable
  have hlim : ∀ᵐ b ∂μ, Tendsto (fun j : ℕ => F (fun t : ℝ≥0 =>
      b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ H (dyadicScale (φ j)) b s) ((φ j : ℕ) : ℝ≥0) (m * t))))
      atTop (𝓝 (F (fun t : ℝ≥0 => b (clockInverse (G b) (m * t))))) := by
    filter_upwards [hcut] with b hb
    have hd := hb.const_mul L
    rw [mul_zero] at hd
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hd
    rw [Real.dist_eq]
    exact hL _ _
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim

/-- **First clause of `LBMPathFunctionalMeasurableStep`.** For a valid mated-CRT environment and a bounded Lipschitz path
functional `F`, `F` of the Liouville Brownian path is almost surely strongly measurable in the Brownian path, for the Brownian law
of every starting point. (Paper argument, `docs/campaign/GAPS-SEC3.md` item 4.) -/
theorem lbmPathFunctional_aestronglyMeasurable {Ω : Type} [MeasurableSpace Ω] (𝒮 : SpaceFillingSLEModel) (γ : ℝ)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (y : ℂ) (F : (ℝ≥0 → ℂ) → ℝ)
    (hF : IsBoundedLipschitzPathFunctional F) :
    ∀ᵐ ω ∂S.P, AEStronglyMeasurable (fun b => F (rescaledLBMPath (S.clock ω) S.m₀ b))
      (planarBrownianMotion y) := by
  filter_upwards [hS.isLQGClock, hS.isQuantumCone.ae_continuousOn_circle] with ω hω hcirc
  have hH : ∀ k : ℕ, Continuous (S.hcirc ω (dyadicScale k)) := by
    intro k
    apply continuousOn_univ.mp
    apply hcirc.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z _
    exact ⟨dyadicScale_pos k, mem_univ z⟩
  exact aestronglyMeasurable_boundedLipschitz_limitPath hF hH (planarBrownianMotion y)
    (G := S.clock ω) (hω y).1 (hω y).2 S.m₀.toNNReal

end MatedCRT
