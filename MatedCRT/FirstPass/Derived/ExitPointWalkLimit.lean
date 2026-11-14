import MatedCRT.FirstPass.Derived.ExitPointTargetLaw
import LatticeProb.Prob.ConvergesWeaklyInCMapping
import LatticeProb.Prob.FiniteMeasureLevyProkhorov

/-!
# Exit points of paths converging weakly to an anisotropic Brownian motion

Condition 1 of Lemma 3.14 of Gwynne-Miller-Sheffield, *An invariance principle for ergodic scale-free
random environments* (arXiv:1807.07515), compares the exit point of the rescaled walk from a square
with the exit point of the limiting Brownian motion.  Its limit step is the continuous mapping theorem
with almost sure continuity: if the laws of random paths `Y ε` converge weakly in `C([0,∞), ℝ²)` (the
convergence mode of GMS Theorem 1.16) to the law of an anisotropic Brownian motion `B` from `0`, and
`U ∋ 0` is a bounded open set with a measurable exterior normal field (in particular an open square),
then the law of the exit point of `Y ε` from `U` converges to the law of the exit point of `B`:

* `tendsto_exitLaw_of_convergesWeaklyInC`: weak convergence of the exit laws as probability measures
  on `ℂ`;
* `tendsto_levyProkhorovDist_exitLaw`: the Lévy-Prokhorov distance between the exit laws tends to `0`;
* `limsup_measure_exitPoint_mem_le`, `le_liminf_measure_exitPoint_mem`: the closed-set and open-set
  halves of the portmanteau theorem for the events `{exit point ∈ F}`;
* the same for an open square containing `0` (`..._openSquare`).

The general statements take the a.s. continuity of the exit-point map under the limit law as a
hypothesis `hc`; it is supplied by `ae_continuousAt_exitPoint_pathLaw` (bounded open set with an exterior
normal field) and `ae_continuousAt_exitPoint_openSquare_pathLaw` (open square).
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

open MatedCRT.TemplateEventCompactOpen MatedCRT.TargetLawTemplateEvent MatedCRT.TargetLawRotation
open ReflectedGMS.GMS ReflectedGMS.StatementIngredients

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2} {target : AnisotropicBrownianTarget}

/-- The exit law of `Y ε` from `U`, read off the image law of `Y ε`, is the law of the exit point of
`Y ε` under `Q`. -/
theorem coe_imageLaw_map_exitPoint (hY : ∀ ε, AEMeasurable (Y ε) Q) {U : Set ℂ} (hU : IsOpen U)
    (ε : ℝ≥0) :
    (((LatticeProb.Portmanteau.imageLaw Q Y hY ε).map
        (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) :
        ProbabilityMeasure ℂ) : Measure ℂ) =
      Q.map (fun x => exitPoint U ⇑(eucPathToComplex (Y ε x))) := by
  rw [ProbabilityMeasure.toMeasure_map, LatticeProb.Portmanteau.coe_imageLaw]
  exact AEMeasurable.map_map_of_aemeasurable
    (measurable_exitPoint_eucPathToComplex hU).aemeasurable (hY ε)

/-- **Convergence of the exit laws.** If the laws of `Y ε` converge weakly to the Brownian law of the
target and the exit-point map from the open set `U` is continuous at almost every path of the limit
law, then the exit laws of `Y ε` from `U` converge weakly to the exit law of the limit. -/
theorem tendsto_exitLaw_of_convergesWeaklyInC (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω) :
    Tendsto (fun ε => (LatticeProb.Portmanteau.imageLaw Q Y hY ε).map
        (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω))) (𝓝[>] 0)
      (𝓝 (target.pathLaw.map
        (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)))) :=
  LatticeProb.Portmanteau.tendsto_map_of_convergesWeaklyInC_of_ae_continuousAt hY h
    (measurable_exitPoint_eucPathToComplex hU) hc

/-- **The Lévy-Prokhorov distance between the exit laws tends to `0`.** -/
theorem tendsto_levyProkhorovDist_exitLaw (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω) :
    Tendsto (fun ε => levyProkhorovDist (Q.map (fun x => exitPoint U ⇑(eucPathToComplex (Y ε x))))
        ((target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
          (fun ω => exitPoint U ⇑(eucPathToComplex ω)))) (𝓝[>] 0) (𝓝 0) := by
  refine (LatticeProb.tendsto_levyProkhorovDist_of_tendsto_probabilityMeasure
    (tendsto_exitLaw_of_convergesWeaklyInC hY h hU hc)).congr fun ε => ?_
  rw [coe_imageLaw_map_exitPoint hY hU ε, ProbabilityMeasure.toMeasure_map]

/-- **Closed-set half for exit points**: `limsup_{ε ↓ 0} Q {exit point of Y ε from U ∈ F}` is at most
the probability that the limit exits `U` in the closed set `F`. -/
theorem limsup_measure_exitPoint_mem_le (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω)
    {F : Set ℂ} (hF : IsClosed F) :
    (𝓝[>] (0 : ℝ≥0)).limsup (fun ε => Q {x | exitPoint U ⇑(eucPathToComplex (Y ε x)) ∈ F}) ≤
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        {ω | exitPoint U ⇑(eucPathToComplex ω) ∈ F} :=
  LatticeProb.Portmanteau.limsup_measure_preimage_le_of_convergesWeaklyInC_of_ae_continuousAt hY h
    (measurable_exitPoint_eucPathToComplex hU) hc hF

/-- **Open-set half for exit points**: the probability that the limit exits `U` in the open set `V`
is at most `liminf_{ε ↓ 0} Q {exit point of Y ε from U ∈ V}`. -/
theorem le_liminf_measure_exitPoint_mem (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω)
    {V : Set ℂ} (hV : IsOpen V) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        {ω | exitPoint U ⇑(eucPathToComplex ω) ∈ V} ≤
      (𝓝[>] (0 : ℝ≥0)).liminf (fun ε => Q {x | exitPoint U ⇑(eucPathToComplex (Y ε x)) ∈ V}) :=
  LatticeProb.Portmanteau.le_liminf_measure_preimage_of_convergesWeaklyInC_of_ae_continuousAt hY h
    (measurable_exitPoint_eucPathToComplex hU) hc hV

/-! ### Open squares containing the origin -/

/-- **Exit laws from an open square converge in the Lévy-Prokhorov distance.** -/
theorem tendsto_levyProkhorovDist_exitLaw_openSquare (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}) :
    Tendsto (fun ε => levyProkhorovDist (Q.map (fun x =>
        exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
          ⇑(eucPathToComplex (Y ε x))))
        ((target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map (fun ω =>
          exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
            ⇑(eucPathToComplex ω)))) (𝓝[>] 0) (𝓝 0) :=
  tendsto_levyProkhorovDist_exitLaw hY h (isOpen_openSquare c a)
    (ae_continuousAt_exitPoint_openSquare_pathLaw target h0)

/-- **Closed-set half for exit points from an open square.** -/
theorem limsup_measure_exitPoint_openSquare_mem_le (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2})
    {F : Set ℂ} (hF : IsClosed F) :
    (𝓝[>] (0 : ℝ≥0)).limsup (fun ε => Q {x |
        exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
          ⇑(eucPathToComplex (Y ε x)) ∈ F}) ≤
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        {ω | exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
          ⇑(eucPathToComplex ω) ∈ F} :=
  limsup_measure_exitPoint_mem_le hY h (isOpen_openSquare c a)
    (ae_continuousAt_exitPoint_openSquare_pathLaw target h0) hF

/-- **Open-set half for exit points from an open square.** -/
theorem le_liminf_measure_exitPoint_openSquare_mem (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (h : ConvergesWeaklyInC Q Y target) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2})
    {V : Set ℂ} (hV : IsOpen V) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
        {ω | exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
          ⇑(eucPathToComplex ω) ∈ V} ≤
      (𝓝[>] (0 : ℝ≥0)).liminf (fun ε => Q {x |
        exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
          ⇑(eucPathToComplex (Y ε x)) ∈ V}) :=
  le_liminf_measure_exitPoint_mem hY h (isOpen_openSquare c a)
    (ae_continuousAt_exitPoint_openSquare_pathLaw target h0) hV

end MatedCRT.StopAtExitCmp

/-! ## Audit -/

#print axioms MatedCRT.StopAtExitCmp.tendsto_levyProkhorovDist_exitLaw
#print axioms MatedCRT.StopAtExitCmp.tendsto_levyProkhorovDist_exitLaw_openSquare
#print axioms MatedCRT.StopAtExitCmp.limsup_measure_exitPoint_openSquare_mem_le
#print axioms MatedCRT.StopAtExitCmp.le_liminf_measure_exitPoint_openSquare_mem
