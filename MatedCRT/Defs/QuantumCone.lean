import MatedCRT.Defs.Notation
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The circle average embedding of the `γ`-quantum cone (Definition 2.1, lines 427-439; lines 440-460)

A random generalized function `h` on `ℂ` is represented, as in the harmonic-balls formalization
(`HarmonicBalls.IsWholePlaneGFF`), by its pairings `hC ω φ = (h, φ)` with test functions and its circle averages
`hcirc ω r z = h_r(z)`.

Definition 2.1. Let `B` be a standard linear Brownian motion and `B̂` an independent standard linear Brownian
motion conditioned so that `B̂_t + (Q - γ) t > 0` for all `t > 0`; let `A_t = B_t + γ t` for `t ≥ 0` and
`A_t = B̂_{-t} + γ t` for `t < 0`. Then `h` is such that `t ↦ h_{e^{-t}}(0)` has the law of `A`, and the lateral part
`h - h_{|·|}(0)` is independent of `h_{|·|}(0)` and has the law of the lateral part of the whole-plane GFF `h^ℂ`.

* The conditioning on the null event `{B̂_t + (Q - γ) t > 0 ∀ t > 0}` is the standard one: the law of `B̂` is the weak
  limit as `δ → 0⁺` of the law of a standard Brownian motion conditioned on the event
  `{B̂_t + (Q - γ) t > -δ ∀ t ≥ 0}`, which has positive probability (`IsBMConditionedPositive`).
* The radial process is recorded as the pair of paths `t ↦ h_{e^{-t}}(0)` and `s ↦ h_{e^s}(0)` (`t, s ≥ 0`); the second
  is `A_{-s} = B̂_s - γ s`. The law of `A` is the product law `quantumConeRadialLaw`.
* The lateral part `h - h_{|·|}(0)` is observed through its pairings `(h, φ) - ∫ φ(x) h_{|x|}(0) dx` and circle
  averages `h_r(z) - (average over ∂B_r(z) of x ↦ h_{|x|}(0))` (`lateralEval`).

The cone scale radius `R_b` (eq:cone-scale-radius, line 451) and the circle averages and pairings of the rescaled
field `h(R ·) + Q log R - γ⁻¹ log b` (eq:quantum-cone-scaling, line 455) are also defined here.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The event `{w_t + c t > -δ for all t ≥ 0}` for a real path `w`. -/
def stayAboveEvent (c δ : ℝ) : Set (ContinuousPath ℝ) :=
  {w | ∀ t : ℝ≥0, -δ < w t + c * t}

/-- `ν` is the law of a standard linear Brownian motion `B̂` *conditioned so that `B̂_t + c t > 0` for all `t > 0`*
(Definition 2.1, line 430, with `c = Q - γ > 0`): a probability measure which is the weak limit, as `δ → 0⁺`, of the
law of standard Brownian motion conditioned on `{B̂_t + c t > -δ ∀ t ≥ 0}`, tested against bounded continuous
functionals of paths (compact-open topology on `C(ℝ≥0, ℝ)`). -/
def IsBMConditionedPositive (c : ℝ) (ν : Measure (ContinuousPath ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ f : ContinuousPath ℝ →ᵇ ℝ,
    Tendsto (fun δ => ∫ w, f w ∂((brownianMotion 0)[|stayAboveEvent c δ])) (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))

/-- The radial process of a field with circle averages `hcirc`: the pair of paths `t ↦ h_{e^{-t}}(0)` and
`s ↦ h_{e^s}(0)`, `t, s ≥ 0`. -/
noncomputable def radialProcess (hcirc : ℝ → ℂ → ℝ) : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (fun t => hcirc (Real.exp (-(t : ℝ))) 0, fun s => hcirc (Real.exp s) 0)

/-- The law of the process `A` of Definition 2.1 (line 431), recorded as the pair `((A_t)_{t ≥ 0}, (A_{-s})_{s ≥ 0})`:
`A_t = B_t + γ t` with `B` a standard Brownian motion, `A_{-s} = B̂_s - γ s` with `B̂` independent of `B` and of law
`ν`. -/
noncomputable def quantumConeRadialLaw (γ : ℝ) (ν : Measure (ContinuousPath ℝ)) :
    Measure ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
  ((brownianMotion 0).map fun w (t : ℝ≥0) => w t + γ * t).prod (ν.map fun w (s : ℝ≥0) => w s - γ * s)

/-- The value of an observable on the lateral part `h - h_{|·|}(0)` of the field: the pairing
`(h, φ) - ∫ φ(x) h_{|x|}(0) dx` and the circle average `h_r(z) - (average over ∂B_r(z) of x ↦ h_{|x|}(0))`. -/
noncomputable def lateralEval (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) : GFFObservable → ℝ
  | .pairing φ => hC φ - ∫ x, φ x * hcirc ‖x‖ 0
  | .circle r z => hcirc r z - Real.circleAverage (fun x => hcirc ‖x‖ 0) z r

/-- The family of all admissible lateral observables of a sample. -/
noncomputable def lateralProcess (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) : GFFObservable.Admissible → ℝ :=
  fun o => lateralEval hC hcirc o.1

/-- `IsQuantumCone γ P hC hcirc`: under the probability measure `P`, `(hC, hcirc)` are the pairings and circle
averages of the circle average embedding of the `γ`-quantum cone (Definition 2.1, lines 427-439):
* pairings with test functions and circle averages of positive radius are random variables, and a.s. the circle
  average process is continuous on `(0, ∞) × ℂ`;
* the radial process `t ↦ h_{e^{-t}}(0)` has the law of `A` (`quantumConeRadialLaw`, for some law `ν` of the
  conditioned Brownian motion `B̂`, `IsBMConditionedPositive (Q - γ) ν`);
* the lateral part `h - h_{|·|}(0)` is independent of the radial process;
* the lateral part has the law of the lateral part of a whole-plane GFF (`IsWholePlaneGFF`, normalized so that
  `h^ℂ_1(0) = 0`), as a process indexed by the admissible observables (product σ-algebra: all finite dimensional
  distributions agree). -/
structure IsQuantumCone {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop where
  /-- Each pairing with a test function is a random variable. -/
  measurable_pairing : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ
  /-- Each circle average of positive radius is a random variable. -/
  measurable_circle : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z
  /-- A.s. the circle average process is continuous in `(r, z) ∈ (0, ∞) × ℂ`. -/
  ae_continuousOn_circle :
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)
  /-- The radial process `t ↦ h_{e^{-t}}(0)` has the law of `A`. -/
  radial_law : ∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
    P.map (fun ω => radialProcess (hcirc ω)) = quantumConeRadialLaw γ ν
  /-- The lateral part is independent of the radial process. -/
  indep : IndepFun (fun ω => radialProcess (hcirc ω)) (fun ω => lateralProcess (hC ω) (hcirc ω)) P
  /-- The lateral part has the law of the lateral part of the whole-plane GFF. -/
  lateral_law : ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
    P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) = P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))

/-- The *cone scale radius* `R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}` (eq:cone-scale-radius, line 451). -/
noncomputable def coneScaleRadius (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (b : ℝ) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ hcirc r 0 + lqgQ γ * Real.log r = γ⁻¹ * Real.log b}

/-- The circle averages `(r, z) ↦ h_{Rr}(Rz) + Q log R - γ⁻¹ log b` of the field `h(R ·) + Q log R - γ⁻¹ log b`
(eq:quantum-cone-scaling, line 455). -/
noncomputable def rescaledCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (R b : ℝ) : ℝ → ℂ → ℝ :=
  fun r z => hcirc (R * r) (R * z) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b

/-- The pairings `φ ↦ R⁻² (h, φ(R⁻¹ ·)) + (Q log R - γ⁻¹ log b) ∫ φ` of the field `h(R ·) + Q log R - γ⁻¹ log b`
(eq:quantum-cone-scaling, line 455; change of variables `y = R x`). -/
noncomputable def rescaledPairing (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (R b : ℝ) : (ℂ → ℝ) → ℝ :=
  fun φ => (R⁻¹) ^ 2 * hC (fun x => φ ((R⁻¹ : ℂ) * x)) +
    (lqgQ γ * Real.log R - γ⁻¹ * Real.log b) * ∫ x, φ x

/-- The family of all admissible observables (pairings with test functions, circle averages of positive radius) of a
sample `(hC, hcirc)` of a random generalized function: its law is the law of the field. -/
noncomputable def fieldProcess (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) : GFFObservable.Admissible → ℝ :=
  fun o => o.1.eval hC hcirc

/-- The *circle average process* `(r, z) ↦ h_r(z)`, `r > 0`, of a sample. It is a.s. continuous (`IsQuantumCone`), so
it is a pathwise object: two versions of it which are a.s. continuous agree a.s. at all `(r, z)` at once, and its
evaluation at random points (such as `(R_b r, R_b z)` for the rescaled field of Lemmas 2.5, 2.6) does not depend on
the version. It determines the field, `(h, φ) = lim_{r → 0} ∫ φ(z) h_r(z) dz`, and its law (product σ-algebra on
`(0, ∞) × ℂ → ℝ`) is the law of the field. -/
def circleProcess (hcirc : ℝ → ℂ → ℝ) : Set.Ioi (0 : ℝ) × ℂ → ℝ :=
  fun p => hcirc p.1 p.2

end MatedCRT
