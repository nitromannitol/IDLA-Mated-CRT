import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterNull
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TransienceCanon

/-!
# The outer radial window of the cone: measurability and absolute continuity of the laws

The two statements of `ConeAnnulusAreaLawEquivalenceSteps.lean` about the outer window
`coneOuterWindow v S b'` of a quantum cone: the post-last-zero window of Brownian motion with drift
`v > 0`, that is the path `s ↦ c (ℓ + min s S)` with `c u = b'_u + v u` and `ℓ` the last zero of `c`,
read on `[0, S]`.

* `coneOuterWindowMeasurable`: the window is almost surely a measurable functional of the Brownian
  path. The last zero is a measurable functional on the space of continuous paths, and a measurable
  map on continuous paths extends to all paths, since restriction to a countable dense set of times is
  a measurable embedding by the Lusin–Souslin theorem (`ConeAnnulusAreaLawEquivalenceOuterBase.lean`).
* `coneOuterWindowLaw`: for Brownian motions `B', B₀'` and drifts `v₁, v₂ > 0` the law of the window
  with drift `v₁` is absolutely continuous with respect to the law of the window with drift `v₂`.
  The two Brownian motions have the same law on path space, so this is a statement about one
  Brownian motion (`measure_window_eq_zero_of_drift`,
  `ConeAnnulusAreaLawEquivalenceOuterNull.lean`). Fix a time `N`. On the event that the drifted path
  stays positive after `N`, a window ending before `N` is a function of the path stopped at `N`
  (`ConeAnnulusAreaLawEquivalenceOuterStop.lean`). For the drift `v₂`, the Markov property at the fixed
  time `N` and the survival probability `1 - exp(-2 v x)` of Brownian motion with drift `v` started at
  `x > 0` show that the corresponding event of the stopped path is null
  (`ConeAnnulusAreaLawEquivalenceOuterMarkov.lean`). Cameron–Martin on `[0, N]` transfers the null set
  to the drift `v₁` (`ConeAnnulusAreaLawEquivalenceOuterCM.lean`), and the remaining probability that the
  last zero is not below `N - S` tends to `0` as `N → ∞`.

The written argument compares the post-last-zero process with a
three-dimensional Bessel process; this formalization instead uses the Markov property at a fixed time
and Cameron–Martin.

Sources: Duplantier–Miller–Sheffield, arXiv:1409.7055, Definition 4.10 for the outer radial part of the
cone; Cameron–Martin (Bogachev, *Gaussian Measures*, AMS 1998, Chapter 2); the survival probability of
Brownian motion with drift (`LatticeProb.measure_forall_drift_gt`); Kechris, *Classical Descriptive Set
Theory*, Theorem 15.1 (Lusin–Souslin).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

open LatticeProb

/-- **Step 3, a measurable version of the outer window.** -/
theorem coneOuterWindowMeasurable : ConeOuterWindowMeasurable := by
  intro v S _ hS
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_measurable_extension
    (G := fun w : C(ℝ≥0, ℝ) => outerWindowOfPath S fun t => driftMap v w t)
    ((measurable_outerWindowOfPath S).comp (measurable_driftMap v))
  refine ⟨Φ, hΦ, ?_⟩
  intro Ω _ P _ B' hB'
  obtain ⟨Bc, _, hBc⟩ := MatedCRTHarmonic.ConeScaling.exists_continuousMap_version hB'
  filter_upwards [hBc] with ω h
  have e : (fun t => B' t ω) = fun t => Bc ω t := funext fun t => (h t).symm
  rw [e, hΦeq, coneOuterWindow_eq hS]
  rfl

/-- **Step 3, the outer radial windows.** The laws of the post-last-zero windows of Brownian motion with
positive drifts `v₁, v₂` read on `[0, S]` are absolutely continuous (Markov property at a fixed time and
Cameron–Martin on a bounded interval). -/
theorem coneOuterWindowLaw : ConeOuterWindowLaw := by
  intro v₁ v₂ S hv₁ hv₂ hS Ω _ P _ B' B₀' hB' hB₀'
  obtain ⟨b, hbm, hbc, -, hb, hbB⟩ := QuantumZipper.RS.exists_good_version0 hB'
  obtain ⟨b₀, hb₀m, hb₀c, -, hb₀, hb₀B⟩ := QuantumZipper.RS.exists_good_version0 hB₀'
  set W : ℝ → C(ℝ≥0, ℝ) → ℝ≥0 → ℝ := fun v w => outerWindowOfPath S fun t => driftMap v w t
    with hW
  have hWm : ∀ v, Measurable (W v) := fun v =>
    (measurable_outerWindowOfPath S).comp (measurable_driftMap v)
  have hae : ∀ (v : ℝ) (B bb : ℝ≥0 → Ω → ℝ) (hcc : ∀ ω, Continuous fun t => bb t ω),
      (∀ᵐ ω ∂P, ∀ t, bb t ω = B t ω) →
        (fun ω => coneOuterWindow v S fun t => B t ω) =ᵐ[P] fun ω => W v (pathMap bb hcc ω) := by
    intro v B bb hcc hbB
    filter_upwards [hbB] with ω h
    have e : (fun t => B t ω) = fun t => bb t ω := funext fun t => (h t).symm
    rw [e, coneOuterWindow_eq hS]
    rfl
  have hmeas1 : Measurable fun ω => W v₁ (pathMap b hbc ω) :=
    (hWm v₁).comp (measurable_pathMap b hbm hbc)
  have hlaw := map_pathMap_eq_of_isBrownianReal hb hbm hbc hb₀ hb₀m hb₀c
  have e2 : P.map (fun ω => W v₂ (pathMap b₀ hb₀c ω)) = P.map (fun ω => W v₂ (pathMap b hbc ω)) := by
    have h1 : P.map (fun ω => W v₂ (pathMap b₀ hb₀c ω)) = (P.map (pathMap b₀ hb₀c)).map (W v₂) :=
      (Measure.map_map (hWm v₂) (measurable_pathMap b₀ hb₀m hb₀c)).symm
    have h2 : P.map (fun ω => W v₂ (pathMap b hbc ω)) = (P.map (pathMap b hbc)).map (W v₂) :=
      (Measure.map_map (hWm v₂) (measurable_pathMap b hbm hbc)).symm
    rw [h1, h2, hlaw]
  refine ⟨hmeas1.aemeasurable.congr (hae v₁ B' b hbc hbB).symm, ?_⟩
  rw [Measure.map_congr (hae v₁ B' b hbc hbB), Measure.map_congr (hae v₂ B₀' b₀ hb₀c hb₀B), e2]
  refine Measure.AbsolutelyContinuous.mk fun A hA h2 => ?_
  rw [Measure.map_apply hmeas1 hA] at ⊢
  have hmeas2 : Measurable fun ω => W v₂ (pathMap b hbc ω) :=
    (hWm v₂).comp (measurable_pathMap b hbm hbc)
  rw [Measure.map_apply hmeas2 hA] at h2
  exact measure_window_eq_zero_of_drift hb hbm hbc hv₁ hv₂ hS hA h2

end MatedCRT
