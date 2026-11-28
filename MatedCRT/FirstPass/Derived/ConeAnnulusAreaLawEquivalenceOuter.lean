import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuterNull
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TransienceCanon

/-!
# The outer radial window of the cone: measurability and absolute continuity of the laws

The two statements of `ConeAnnulusAreaLawEquivalenceSteps.lean` about the outer window
`coneOuterWindow v S b'` of a quantum cone (the path after the last zero of `b'_u + v u`, read on
`[0, S]`):

* `coneOuterWindowMeasurable`: the window is almost surely a measurable functional of the Brownian
  path. The last zero is a measurable functional on the space of continuous paths, and a measurable
  map on continuous paths extends to all paths (`ConeAnnulusAreaLawEquivalenceOuterBase.lean`).
* `coneOuterWindowLaw`: for Brownian motions `B', B₀'` and positive drifts `v₁, v₂` the law of the
  window with drift `v₁` is absolutely continuous with respect to the law of the window with drift
  `v₂`. The two Brownian motions have the same law on path space, so this is a statement about one
  Brownian motion, `measure_window_eq_zero_of_drift`
  (`ConeAnnulusAreaLawEquivalenceOuterNull.lean`): Markov property at a fixed time `N` and
  Cameron–Martin on `[0, N]` (`ConeAnnulusAreaLawEquivalenceOuterMarkov.lean`,
  `ConeAnnulusAreaLawEquivalenceOuterCM.lean`).

Sources: D. Williams, *Path decomposition and continuity of local time for one-dimensional diffusions
I*, Proc. LMS 28 (1974); Rogers–Pitman, *Markov functions*, Ann. Probab. 9 (1981), Theorem 1;
Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII.4; Cameron–Martin (Bogachev, *Gaussian
Measures*, Chapter 2); Duplantier–Miller–Sheffield, arXiv:1409.7055, Definition 4.10 for the outer
radial part of the cone.
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

/-- **Step 3, the outer radial windows (Williams' path decomposition and Cameron–Martin).** -/
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
