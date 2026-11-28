import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import HarmonicBalls.Defs.LQG

/-!
# Smooth approximations of the LQG measure on a disc and their transport by conformal maps

Definitions for the coordinate change of the LQG measure for all inverse charts (`LQGMeasureChartStmt`), following
Sheffield–Wang, *Field-measure correspondence in Liouville quantum gravity almost surely commutes with all conformal
maps simultaneously* (arXiv:1605.06171v2), §1 and §3.2:

* `pairFun`: the pairing of a distribution on an open set with a smooth function compactly supported in it;
* `IsMollifier`, `mollScale`, `mollConst`: a radially symmetric bump function `f`, `f_ε(z) = ε⁻² f(z/ε)` ((3.3)) and the
  constant `C` of (3.4);
* `smoothApprox`: the smooth approximation `e^{γ h ∗ f_ε(z) + (γ²/2)(log ε + C)} dz` (§3.2, after (3.4)); with the
  variance formula before (3.4) it is the measure (1.2) with the reference measure of Remark 2.5;
* `envSup`, `envInf`: the upper and lower envelopes of the smooth approximations over a scale interval
  `[2^{-(k+1)/N}, 2^{-k/N}]` (end of the proof of Theorem 1.2, p. 11);
* `pullbackPairing`: the pairings of `h ∘ φ + Q log |φ'|` for a conformal map `ψ` with inverse `φ` ((1.6),
  Proposition 2.3, Remark 3.3);
* `IsCircleProcess`: a process continuous in the radius and the centre whose radial integrals are the radial
  averages of the field (p. 10, `h ∗ f_ε(z) = 2π ∫_0^ε h_r(z) f_ε(r) r dr`), i.e. the continuous circle-average process
  of Proposition 2.4;
* `SheffieldWangDiscConformal`: the conclusion of Theorems 1.1, 1.2 and 1.4 on a disc, at the scales `2^{-k}`.
-/

set_option autoImplicit false

noncomputable section

open scoped Classical

open MeasureTheory Filter Topology Set Metric
open scoped Distributions

namespace MatedCRT

namespace LQGMeasureChart

/-- The open disc `B(c, r)`. -/
def disc (c : ℂ) (r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨ball c r, isOpen_ball⟩

/-- The pairing `⟨g, u⟩` of a distribution `g` on the open set `V` with a function `u`, when `u` is smooth with
compact support in `V`; `0` otherwise. -/
def pairFun {V : TopologicalSpace.Opens ℂ} (g : LQGMetric.DistOn V) (u : ℂ → ℝ) : ℝ :=
  if hu : ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ V then
    g ⟨u, hu.1, hu.2.1, hu.2.2⟩
  else 0

/-- **A bump function of Sheffield–Wang (2016)** (p. 2 and §3.2): smooth, nonnegative, radially symmetric, with
compact support in the unit disc and integral `1`. -/
structure IsMollifier (f : ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) f
  nonneg : ∀ z, 0 ≤ f z
  radial : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w
  hasCompactSupport : HasCompactSupport f
  tsupport_subset : tsupport f ⊆ ball 0 1
  integral_eq_one : ∫ z, f z = 1

/-- `f_ε(z) = ε⁻² f(z/ε)` (Sheffield–Wang (2016), (3.3)). -/
def mollScale (f : ℂ → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  (ε ^ 2)⁻¹ * f (z / (ε : ℂ))

/-- The constant `C = 4π² ∬_{[0,1]²} log (x ∨ y) f(x) f(y) x y dx dy` of Sheffield–Wang (2016), (3.4), with
`f(x) = f((x, 0))`. -/
def mollConst (f : ℂ → ℝ) : ℝ :=
  4 * Real.pi ^ 2 * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.log (max x y) * f x * f y * x * y

/-- The exponent `h̃_ε(z) = γ (h ∗ f_ε)(z) + (γ²/2)(log ε + C)` (Sheffield–Wang (2016), §3.2, after (3.4)), for the field
given by its pairings `G`, with `(h ∗ f_ε)(z) = G(f_ε(z − ·))`. -/
def smoothExponent (γ : ℝ) (f : ℂ → ℝ) (G : (ℂ → ℝ) → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  γ * G (fun w => mollScale f ε (z - w)) + γ ^ 2 / 2 * (Real.log ε + mollConst f)

/-- **The smooth approximation of the LQG measure** (Sheffield–Wang (2016), §3.2, after (3.4)): `μ̃_ε = e^{h̃_ε(z)} dz`
on the points `z` with `B̄_ε(z) ⊆ V`, density `0` elsewhere. -/
def smoothApprox (γ : ℝ) (f : ℂ → ℝ) (V : Set ℂ) (G : (ℂ → ℝ) → ℝ) (ε : ℝ) : Measure ℂ :=
  volume.withDensity fun z =>
    if closedBall z ε ⊆ V then ENNReal.ofReal (Real.exp (smoothExponent γ f G ε z)) else 0

/-- **The upper envelope** of the smooth approximations over the scales `ε ∈ [2^{-(k+1)/N}, 2^{-k/N}]`
(Sheffield–Wang (2016), end of the proof of Theorem 1.2, p. 11), on the points `z` with `B̄_{2^{-k/N}}(z) ⊆ V`. -/
def envSup (γ : ℝ) (f : ℂ → ℝ) (V : Set ℂ) (G : (ℂ → ℝ) → ℝ) (N k : ℕ) : Measure ℂ :=
  volume.withDensity fun z =>
    if closedBall z ((2 : ℝ) ^ (-(k : ℝ) / N)) ⊆ V then
      ⨆ ε ∈ Icc ((2 : ℝ) ^ (-((k : ℝ) + 1) / N)) ((2 : ℝ) ^ (-(k : ℝ) / N)),
        ENNReal.ofReal (Real.exp (smoothExponent γ f G ε z))
    else 0

/-- **The lower envelope** of the smooth approximations over the scales `ε ∈ [2^{-(k+1)/N}, 2^{-k/N}]`
(Sheffield–Wang (2016), end of the proof of Theorem 1.2, p. 11), on the points `z` with `B̄_{2^{-k/N}}(z) ⊆ V`. -/
def envInf (γ : ℝ) (f : ℂ → ℝ) (V : Set ℂ) (G : (ℂ → ℝ) → ℝ) (N k : ℕ) : Measure ℂ :=
  volume.withDensity fun z =>
    if closedBall z ((2 : ℝ) ^ (-(k : ℝ) / N)) ⊆ V then
      ⨅ ε ∈ Icc ((2 : ℝ) ^ (-((k : ℝ) + 1) / N)) ((2 : ℝ) ^ (-(k : ℝ) / N)),
        ENNReal.ofReal (Real.exp (smoothExponent γ f G ε z))
    else 0

/-- **The pairings of `h ∘ φ + Q log |φ'|`** on `ψ(D)`, for a conformal map `ψ : D → ψ(D)` with inverse
`φ = ψ⁻¹` (Sheffield–Wang (2016), (1.6)): `(h ∘ φ, u) = (h, |ψ'|² u ∘ ψ)` (Proposition 2.3, Remark 3.3) plus
`Q ∫ log |φ'| u`, `Q = 2/γ + γ/2`. -/
def pullbackPairing (γ : ℝ) {D : TopologicalSpace.Opens ℂ} (g : LQGMetric.DistOn D) (ψ : ℂ → ℂ)
    (u : ℂ → ℝ) : ℝ :=
  pairFun g ((D : Set ℂ).indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) +
    (2 / γ + γ / 2) * ∫ w, Real.log ‖deriv (Function.invFunOn ψ D) w‖ * u w

/-- **A continuous circle-average process of a distribution on the disc `B(c, r)`** (Sheffield–Wang (2016),
Proposition 2.4 and p. 10): `hc` is continuous in the radius and the centre on the pairs `(s, z)` with
`B̄_s(z) ⊆ B(c, r)`, and the pairing of `g` with every smooth radial function `u` supported in `B_ε(0)`, centred at `z`,
is `2π ∫_0^ε hc(s, z) u(s) s ds`. -/
def IsCircleProcess (c : ℂ) (r : ℝ) (g : LQGMetric.DistOn (disc c r)) (hc : ℝ → ℂ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) {p | 0 < p.1 ∧ closedBall p.2 p.1 ⊆ ball c r} ∧
    ∀ (z : ℂ) (ε : ℝ), 0 < ε → closedBall z ε ⊆ ball c r → ∀ u : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      (∀ w w' : ℂ, ‖w‖ = ‖w'‖ → u w = u w') → tsupport u ⊆ ball 0 ε →
      pairFun g (fun w => u (z - w)) = 2 * Real.pi * ∫ s in (0 : ℝ)..ε, hc s z * u s * s

end LQGMeasureChart

open LQGMeasureChart in
/-- **The LQG measure of the zero-boundary GFF on a disc commutes with all conformal maps simultaneously, at fixed
scale** (the conclusion of Sheffield–Wang (2016), Theorems 1.1, 1.2 and 1.4, on a disc, at the scales `2^{-k}`): for
`0 < γ < 2`, a bump function `f`, a disc `D = B(c, r)`, a zero-boundary GFF `h` on `D` and its continuous circle-average
process `hcirc`, almost surely there is a measure `μ` such that the circle approximations converge weakly in `D` to
`μ` along `2^{-k}`, and for every conformal map `ψ` from `D` onto a bounded open set the smooth approximations of
`h ∘ φ + Q log |φ'|`, `φ = ψ⁻¹`, converge weakly in `ψ(D)` along `2^{-k}` to the measure `ν` with `ν(A) = μ(φ(A))`. -/
def SheffieldWangDiscConformal : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ f : ℂ → ℝ, IsMollifier f → ∀ (c : ℂ) (r : ℝ), 0 < r →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
  ∀ h : Ω → LQGMetric.DistOn (disc c r), LQGMetric.IsZeroBoundaryGFF (disc c r) h P →
  ∀ hcirc : Ω → ℝ → ℂ → ℝ, (∀ᵐ ω ∂P, IsCircleProcess c r (h ω) (hcirc ω)) →
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ,
      QuantumZipper.IsVagueLimitOn (ball c r)
        (fun k => HarmonicBalls.lqgApprox γ (hcirc ω) (HarmonicBalls.dyadicScale k)) μ ∧
      ∀ ψ : ℂ → ℂ, InjOn ψ (ball c r) → DifferentiableOn ℂ ψ (ball c r) →
        Bornology.IsBounded (ψ '' ball c r) →
        ∃ ν : Measure ℂ,
          QuantumZipper.IsVagueLimitOn (ψ '' ball c r)
            (fun k => smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ (h ω) ψ)
              (HarmonicBalls.dyadicScale k)) ν ∧
          ∀ A : Set ℂ, MeasurableSet A → A ⊆ ψ '' ball c r → ν A = μ (ball c r ∩ ψ ⁻¹' A)

end MatedCRT
