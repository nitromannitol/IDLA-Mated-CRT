import Mathlib
import MatedCRT.LPStaging.Prob.BrownianPathLaw
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import MarkovProcess.Main
import MarkovProcess.Examples.BrownianMotion

/-!
# Canonical planar Brownian motion: centred laws and the strong Markov restart at truncated exit times

For a planar Brownian motion `𝓑` started at `x`, the path centred at its starting point has a law
independent of `x` (Mörters–Peres, *Brownian Motion*, Theorem 2.16 and the Markov property). The
strong Markov property (MarkovProcess, `continuousProcess_restrict_map_shift_stoppingTime`) at the
truncated exit time `exitTimeTrunc U K` of an open set `U` gives the restart identity
`P(A ∩ {post-τ increments ∈ Γ}) = P(A) · μ(Γ)` for `A` in the stopped σ-algebra.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter
open scoped NNReal ENNReal

namespace MatedCRT.ExitRestart

open HarmonicBalls

/-- Real path centred at `x`. -/
def c1 (x : ℝ) (η : ContinuousPath ℝ) : ℝ≥0 → ℝ := fun t => η t - x

/-- Complex path centred at `x`. -/
def cC (x : ℂ) (η : ContinuousPath ℂ) : ℝ≥0 → ℂ := fun t => η t - x

/-- Complex path centred at its own value at time `0`. -/
def cStart (η : ContinuousPath ℂ) : ℝ≥0 → ℂ := fun t => η t - η 0

/-- Recombine two real paths into a complex path. -/
def psi (f g : ℝ≥0 → ℝ) : ℝ≥0 → ℂ := fun t => (f t : ℂ) + (g t : ℂ) * Complex.I

/-- Law of the real Brownian motion from `0`, centred at its start. -/
noncomputable def muOne : Measure (ℝ≥0 → ℝ) := (brownianMotion 0).map (c1 0)

/-- Law of the planar Brownian motion, centred at its start (independent of the starting point). -/
noncomputable def muPlanar : Measure (ℝ≥0 → ℂ) := ((muOne).prod muOne).map (fun p => psi p.1 p.2)

lemma measurable_c1 (x : ℝ) : Measurable (c1 x) :=
  Measurable.of_eval fun t => (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).sub
    measurable_const

lemma measurable_cC (x : ℂ) : Measurable (cC x) :=
  Measurable.of_eval fun t => (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).sub
    measurable_const

lemma measurable_cStart : Measurable cStart :=
  Measurable.of_eval fun t => (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).sub
    (MarkovProcess.ContinuousPath.measurable_coordinateProcess 0)

lemma measurable_psi : Measurable (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => psi p.1 p.2) := by
  refine Measurable.of_eval fun t => ?_
  have h1 : Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.1 t :=
    (measurable_pi_apply t).comp measurable_fst
  have h2 : Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.2 t :=
    (measurable_pi_apply t).comp measurable_snd
  exact (Complex.measurable_ofReal.comp h1).add ((Complex.measurable_ofReal.comp h2).mul_const _)

/-- The centred canonical real process is pre-Brownian in Mathlib's sense
(Mathlib `ProbabilityTheory.IsPreBrownianReal`), as in HB `isPreBrownianReal_brownianMotion`. -/
lemma brownianMotion_isPreBrownianReal (x : ℝ) :
    ProbabilityTheory.IsPreBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t - x)
      (brownianMotion x) := by
  apply ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · exact (MarkovProcess.isBrownianReal_brownianMotion x).hasLaw_eval
  · exact (MarkovProcess.isBrownianReal_brownianMotion x).hasIndepIncrements

/-- The real centred Brownian law does not depend on the starting point. -/
lemma map_c1_brownianMotion (x : ℝ) : (brownianMotion x).map (c1 x) = muOne := by
  unfold muOne c1
  exact LatticeProb.map_path_eq_of_isPreBrownianReal
    (brownianMotion_isPreBrownianReal x)
    (brownianMotion_isPreBrownianReal 0)
    (fun t => (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).sub measurable_const)
    (fun t => (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).sub measurable_const)

/-- The planar centred Brownian law does not depend on the starting point. -/
lemma map_cC_planarBrownianMotion (x : ℂ) : (planarBrownianMotion x).map (cC x) = muPlanar := by
  have hfun : cC x ∘ complexPathOfReIm =
      (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => psi p.1 p.2) ∘
        Prod.map (c1 x.re) (c1 x.im) := by
    funext p
    funext t
    simp only [Function.comp_apply, cC, c1, psi, Prod.map, complexPathOfReIm_apply]
    conv_lhs => rw [← Complex.re_add_im x]
    push_cast
    ring
  have h1 : planarBrownianMotion x =
      ((brownianMotion x.re).prod (brownianMotion x.im)).map complexPathOfReIm :=
    planarBrownianMotion_apply x
  rw [h1, Measure.map_map (measurable_cC x) measurable_complexPathOfReIm, hfun,
    ← Measure.map_map measurable_psi ((measurable_c1 x.re).prodMap (measurable_c1 x.im)),
    ← Measure.map_prod_map (brownianMotion x.re) (brownianMotion x.im) (measurable_c1 x.re)
      (measurable_c1 x.im), map_c1_brownianMotion, map_c1_brownianMotion]
  rfl

/-- The centred law of the planar Brownian motion from `y`, evaluated on `cStart`, is `muPlanar`. -/
lemma planarBrownianMotion_cStart_preimage (y : ℂ) {Γ : Set (ℝ≥0 → ℂ)} (hΓ : MeasurableSet Γ) :
    planarBrownianMotion y (cStart ⁻¹' Γ) = muPlanar Γ := by
  have hae : cStart ⁻¹' Γ =ᵐ[planarBrownianMotion y] cC y ⁻¹' Γ := by
    filter_upwards [ae_planarBrownianMotion_eval_zero y] with η hη
    apply propext
    change (fun t => η t - η 0) ∈ Γ ↔ (fun t => η t - y) ∈ Γ
    rw [hη]
  rw [measure_congr hae, ← Measure.map_apply (measurable_cC y) hΓ, map_cC_planarBrownianMotion]

/-- **Strong Markov restart of planar Brownian motion at a truncated exit time.** For `A` in the
stopped σ-algebra `F_{τ_K}` of the truncated exit time `τ_K = exitTimeTrunc U K`, the event that `A`
occurs and the path after `τ_K`, centred at its value there, lies in `Γ`, has probability
`P(A) · μ(Γ)`. (MarkovProcess, `continuousProcess_restrict_map_shift_stoppingTime`, with the
planar heat semigroup of HarmonicBalls.) -/
lemma restart_exitTimeTrunc {U : Set ℂ} (hU : IsOpen U) (K : NNReal) (x : ℂ)
    {A : Set (ContinuousPath ℂ)}
    (hA : MeasurableSet[(ContinuousPath.isStoppingTime_exitTimeTrunc U hU K).measurableSpace] A)
    {Γ : Set (ℝ≥0 → ℂ)} (hΓ : MeasurableSet Γ) :
    planarBrownianMotion x
        (A ∩ (fun η => ContinuousPath.shift (ContinuousPath.exitTimeTrunc U K η) η) ⁻¹'
          (cStart ⁻¹' Γ))
      = planarBrownianMotion x A * muPlanar Γ := by
  have hT := ContinuousPath.isStoppingTime_exitTimeTrunc U hU K
  have hS : MeasurableSet (cStart ⁻¹' Γ) := measurable_cStart hΓ
  have hfm := ContinuousPath.measurable_shift_stoppingTime
    (fun η : ContinuousPath ℂ => ContinuousPath.exitTimeTrunc U K η) hT
  have hX : MeasurableSet ((fun η : ContinuousPath ℂ =>
      ContinuousPath.shift (ContinuousPath.exitTimeTrunc U K η) η) ⁻¹' (cStart ⁻¹' Γ)) := hfm hS
  have key := isFellerKernelSemigroup_planarHeatSemigroup.continuousProcess_restrict_map_shift_stoppingTime
    (P := planarHeatSemigroup) (hP := isConservative_planarHeatSemigroup)
    (hK := kolmogorovRegular_planarHeatSemigroup) x
    (fun η => ContinuousPath.exitTimeTrunc U K η) hT A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at key
  have h := congrArg (fun μ : Measure (ContinuousPath ℂ) => μ (cStart ⁻¹' Γ)) key
  have hpt : ∀ y : ℂ, planarBrownianMotion y (cStart ⁻¹' Γ) = muPlanar Γ :=
    fun y => planarBrownianMotion_cStart_preimage y hΓ
  simp only [Measure.map_apply hfm hS, Measure.bind_apply hS (Kernel.measurable _).aemeasurable,
    Kernel.comap_apply, hpt, lintegral_const] at h
  rw [Measure.restrict_apply hX, Measure.restrict_apply_univ] at h
  rw [Set.inter_comm, h, mul_comm]

end MatedCRT.ExitRestart
