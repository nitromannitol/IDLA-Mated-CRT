import MatedCRT.FirstPass.Derived.ExitPointWalkLimit
import LatticeProb.Prob.CellConfigWalkMeasurable

/-!
# Exit points of the rescaled random walk on almost every cell configuration

Condition 1 of Lemma 3.14 of Gwynne-Miller-Sheffield, *An invariance principle for ergodic scale-free
random environments* (arXiv:1807.07515), compares the exit point of the rescaled random walk from a
square with the exit point of the limiting Brownian motion.  The continuous mapping step
(`MatedCRT.FirstPass.Derived.ExitPointWalkLimit`) is stated for random paths `Y ε` that are
a.e.-measurable under the walk law.  For the rescaled linearly interpolated simple random walk
`t ↦ ε X̃_{t/ε²}` on a cell configuration `H` (Definition 1.15 of the same paper) this measurability
holds for almost every configuration as soon as the random cell configuration is connected along
lines (hypothesis 3 of GMS Theorem 1.16) and the walk is almost surely recurrent (the second
conclusion of GMS Theorem 1.16): `LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk`.

Here the measurability hypothesis is discharged in this way.  For almost every configuration `H`,
every starting cell `K₀`, every law `Q` of the simple random walk from `K₀`, and every choice `p` of
points of the cells, if the laws of the rescaled walk converge weakly in `C([0,∞), ℂ)` to the law of
an anisotropic Brownian motion `B` from `0` (the first conclusion of GMS Theorem 1.16), then

* `ae_tendsto_exitLaw_of_convergesWeaklyInC`: the rescaled walk is a random path and its exit laws
  from a bounded open set `U ∋ 0` converge weakly to the exit law of `B`;
* `ae_tendsto_levyProkhorovDist_exitLaw`: the Lévy-Prokhorov distance between the exit laws tends to
  `0`;
* `ae_limsup_measure_exitPoint_mem_le`, `ae_le_liminf_measure_exitPoint_mem`: the closed-set and
  open-set halves of the portmanteau theorem for the events `{exit point ∈ F}`;
* the same for an open square containing `0` (`..._openSquare...`), where the almost sure continuity
  of the exit-point map under the limit law is automatic.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

open MatedCRT.TemplateEventCompactOpen MatedCRT.TargetLawTemplateEvent MatedCRT.TargetLawRotation
open ReflectedGMS.GMS ReflectedGMS.StatementIngredients

variable {μ : Measure GMSSpace} {target : AnisotropicBrownianTarget}

/-- **Convergence of the exit laws of the rescaled walk, for almost every configuration.** Under
connectedness along lines and almost sure recurrence, for almost every cell configuration `H`, every
law `Q` of the simple random walk on `H` and every choice `p` of points of the cells: if the laws of
the rescaled interpolated walk converge weakly to the Brownian law of the target and the exit-point
map from the open set `U` is continuous at almost every path of the limit law, then the rescaled walk
is a.e.-measurable at every scale and its exit laws from `U` converge weakly to the exit law of the
limit. -/
theorem ae_tendsto_exitLaw_of_convergesWeaklyInC (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)) (hQ : H.1.IsSRWLaw K₀ Q)
      (p : H.1.cells → ReflectedGMS.Plane),
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      haveI : IsProbabilityMeasure Q := hQ.1
      ∃ hY : ∀ ε, AEMeasurable (H.1.interpolatedWalk p ε) Q,
        Tendsto (fun ε => (LatticeProb.Portmanteau.imageLaw Q (H.1.interpolatedWalk p) hY ε).map
            (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω))) (𝓝[>] 0)
          (𝓝 (target.pathLaw.map
            (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)))) := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact ⟨hY K₀ Q hQ p, tendsto_exitLaw_of_convergesWeaklyInC (hY K₀ Q hQ p) hW hU hc⟩

/-- **The Lévy-Prokhorov distance between the exit laws of the rescaled walk and of the limit tends
to `0`, for almost every configuration.** -/
theorem ae_tendsto_levyProkhorovDist_exitLaw (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      Tendsto (fun ε => levyProkhorovDist
          (Q.map (fun x => exitPoint U ⇑(eucPathToComplex (H.1.interpolatedWalk p ε x))))
          ((target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
            (fun ω => exitPoint U ⇑(eucPathToComplex ω)))) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact tendsto_levyProkhorovDist_exitLaw (hY K₀ Q hQ p) hW hU hc

/-- **Closed-set half for the exit points of the rescaled walk, for almost every configuration**:
`limsup_{ε ↓ 0} Q {exit point of the rescaled walk from U ∈ F}` is at most the probability that the
limit exits `U` in the closed set `F`. -/
theorem ae_limsup_measure_exitPoint_mem_le (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω)
    {F : Set ℂ} (hF : IsClosed F) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      (𝓝[>] (0 : ℝ≥0)).limsup
          (fun ε => Q {x | exitPoint U ⇑(eucPathToComplex (H.1.interpolatedWalk p ε x)) ∈ F}) ≤
        (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
          {ω | exitPoint U ⇑(eucPathToComplex ω) ∈ F} := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact limsup_measure_exitPoint_mem_le (hY K₀ Q hQ p) hW hU hc hF

/-- **Open-set half for the exit points of the rescaled walk, for almost every configuration**: the
probability that the limit exits `U` in the open set `V` is at most
`liminf_{ε ↓ 0} Q {exit point of the rescaled walk from U ∈ V}`. -/
theorem ae_le_liminf_measure_exitPoint_mem (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {U : Set ℂ} (hU : IsOpen U)
    (hc : ∀ᵐ ω ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)),
      ContinuousAt (fun ω : BouRabeeGwynne.BrownianPath 2 => exitPoint U ⇑(eucPathToComplex ω)) ω)
    {V : Set ℂ} (hV : IsOpen V) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
          {ω | exitPoint U ⇑(eucPathToComplex ω) ∈ V} ≤
        (𝓝[>] (0 : ℝ≥0)).liminf
          (fun ε => Q {x | exitPoint U ⇑(eucPathToComplex (H.1.interpolatedWalk p ε x)) ∈ V}) := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact le_liminf_measure_exitPoint_mem (hY K₀ Q hQ p) hW hU hc hV

/-! ### Open squares containing the origin -/

/-- **Exit laws of the rescaled walk from an open square converge in the Lévy-Prokhorov distance,
for almost every configuration.** -/
theorem ae_tendsto_levyProkhorovDist_exitLaw_openSquare (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      Tendsto (fun ε => levyProkhorovDist (Q.map (fun x =>
          exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
            ⇑(eucPathToComplex (H.1.interpolatedWalk p ε x))))
          ((target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map (fun ω =>
            exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
              ⇑(eucPathToComplex ω)))) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact tendsto_levyProkhorovDist_exitLaw_openSquare (hY K₀ Q hQ p) hW h0

/-- **Closed-set half for the exit points of the rescaled walk from an open square, for almost every
configuration.** -/
theorem ae_limsup_measure_exitPoint_openSquare_mem_le (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2})
    {F : Set ℂ} (hF : IsClosed F) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      (𝓝[>] (0 : ℝ≥0)).limsup (fun ε => Q {x |
          exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
            ⇑(eucPathToComplex (H.1.interpolatedWalk p ε x)) ∈ F}) ≤
        (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
          {ω | exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
            ⇑(eucPathToComplex ω) ∈ F} := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact limsup_measure_exitPoint_openSquare_mem_le (hY K₀ Q hQ p) hW h0 hF

/-- **Open-set half for the exit points of the rescaled walk from an open square, for almost every
configuration.** -/
theorem ae_le_liminf_measure_exitPoint_openSquare_mem (h : ConnectedAlongLines μ)
    (hrec : ∀ᵐ H ∂μ, H.1.Recurrent) {c : ℂ} {a : ℝ}
    (h0 : (0 : ℂ) ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2})
    {V : Set ℂ} (hV : IsOpen V) :
    ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
      ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target →
      (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))
          {ω | exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
            ⇑(eucPathToComplex ω) ∈ V} ≤
        (𝓝[>] (0 : ℝ≥0)).liminf (fun ε => Q {x |
          exitPoint {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}
            ⇑(eucPathToComplex (H.1.interpolatedWalk p ε x)) ∈ V}) := by
  filter_upwards [LatticeProb.CellConfigWalk.ae_aemeasurable_interpolatedWalk h hrec]
    with H hY K₀ Q hQ p hW
  have : IsProbabilityMeasure Q := hQ.1
  exact le_liminf_measure_exitPoint_openSquare_mem (hY K₀ Q hQ p) hW h0 hV

end MatedCRT.StopAtExitCmp

/-! ## Audit -/

#print axioms MatedCRT.StopAtExitCmp.ae_tendsto_exitLaw_of_convergesWeaklyInC
#print axioms MatedCRT.StopAtExitCmp.ae_tendsto_levyProkhorovDist_exitLaw
#print axioms MatedCRT.StopAtExitCmp.ae_limsup_measure_exitPoint_mem_le
#print axioms MatedCRT.StopAtExitCmp.ae_le_liminf_measure_exitPoint_mem
#print axioms MatedCRT.StopAtExitCmp.ae_tendsto_levyProkhorovDist_exitLaw_openSquare
#print axioms MatedCRT.StopAtExitCmp.ae_limsup_measure_exitPoint_openSquare_mem_le
#print axioms MatedCRT.StopAtExitCmp.ae_le_liminf_measure_exitPoint_openSquare_mem
