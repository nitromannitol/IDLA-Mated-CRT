import MatedCRT.FirstPass.Derived.StopAtExitWalkBound
import MatedCRT.FirstPass.Derived.UniformStartStoppedLaw

/-!
# Moving the Brownian starting point of the stopped comparison

The area-cell comparison puts the Brownian motion at the centre of the starting cell, whereas the
embedded walk starts at the embedded vertex. By the uniform continuity of the stopped Brownian laws
in the starting point, an all-set bound for the stopped walk against planar Brownian motion started
at a point `z` gives, at the price of an extra slack in the `cmpEDist`-neighborhood and in the
additive term, the same bound for Brownian motion started at any point `y` of `closedBall 0 ρ`
with `dist z y < s`, where `s` depends only on `ρ < R` and the slacks.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitStartTransfer

open LatticeProb LatticeProb.ReparamDistanceIsometry LatticeProb.CurveSpaceComparison
open MatedCRT.TargetLawTemplateEvent MatedCRT.StopAtExitCmp MatedCRT.StopAtExitCurveClass
  MatedCRT.StopAtExitLevyProkhorov

/-- **Start-point shift for an all-set bound.** Let `0 < ρ < R`. For positive slacks `κ, θ` there is
`s > 0` such that for every set function `L` on sets of paths (e.g. the law of the stopped walk),
every `y ∈ closedBall 0 ρ` and every `z` with `dist z y < s`, an all-set bound of `L` against planar
Brownian motion started at `z` and stopped at its exit time from `B_R(0)` gives the all-set bound
against planar Brownian motion started at `y`, with `κ` added to the `cmpEDist`-neighborhood and
`θ` to the additive term. -/
theorem exists_forall_start_shift {ρ R : ℝ} (hρR : ρ < R) {κ θ : ℝ≥0∞} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ s > 0, ∀ (L : Set (ℝ≥0 → ℂ) → ℝ≥0∞) (κ₁ a : ℝ≥0∞) (y z : ℂ), y ∈ closedBall (0 : ℂ) ρ →
      dist z y < s →
      (∀ A : Set (ℝ≥0 → ℂ), L A ≤ planarBrownianMotion z
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁} + a) →
      ∀ A : Set (ℝ≥0 → ℂ), L A ≤ planarBrownianMotion y
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁ + κ} + (θ + a) := by
  obtain ⟨s, hs, hcont⟩ := exists_forall_planarBrownianMotion_stopAtExit_le hρR hκ hθ
  refine ⟨s, hs, fun L κ₁ a y z hy hz hL A => ?_⟩
  calc L A ≤ planarBrownianMotion z
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁} + a := hL A
    _ ≤ (planarBrownianMotion y
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁ + κ} + θ) + a :=
      add_le_add (hcont y hy z hz κ₁ A).1 le_rfl
    _ = _ := add_assoc _ _ _

/-- **All-set bound for the walk stopped at its exit time from `B_R(0)`, Brownian motion started at
the embedded vertex.** For `0 < ρ < R` and `κ > 0` there is `s > 0` such that: if the embedded vertex
`x` lies in `closedBall 0 ρ`, the walk exits `B_R(0)` in finite time almost surely, and the
Lévy–Prokhorov bound `< δ ≤ κ / 3` of the area-cell package holds against the stopped Brownian law
started at a point of `ℂ` within `s` of the embedded vertex, then every set `A` of stopped walk paths
has `srwLaw`-probability at most the planar Brownian probability, from the embedded vertex, of the
`cmpEDist`-neighborhood of radius `κ` of `A`, plus `κ`. -/
theorem exists_forall_walk_allSet_le {ρ R : ℝ} (hρR : ρ < R) {κ : ℝ} (hκ : 0 < κ) :
    ∃ s > 0, ∀ {α m₀ : ℝ≥0} (_hα : α = 1) (hm₀ : 0 < m₀) (_hm₁ : m₀ = 1) (ε : ℝ) (η : ℝ → ℂ)
      (m : ℤ → ℤ → ℕ) (x : ℤ), vertexPoint ε η x ∈ closedBall (0 : ℂ) ρ →
      (∀ᵐ ξ ∂(srwLaw m x), pathExitTime (ball (0 : ℂ) R) (interpolatedWalk ε η 1 ξ) ≠ ⊤) →
      ∀ (y : LatticeProb.Euc 2) (U : Set (LatticeProb.Euc 2)),
      U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' ball (0 : ℂ) R →
      dist (Complex.orthonormalBasisOneI.repr.symm y) (vertexPoint ε η x) < s →
      ∀ (μ : Measure (LatticeProb.BrownianPath 2)), LatticeProb.IsStandardBrownianLaw μ →
      ∀ δ : ℝ, 0 < δ → δ ≤ κ / 3 →
      levyProkhorovEDist
        ((srwLaw m x).map (fun w : ℕ → ℤ => isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le w))
            (pathExitTime (ball (0 : ℂ) R)
              ⇑((α : ℝ) • interpPathCM (vertexPoint ε η) hm₀.le w)).toNNReal)))
        (BouRabeeGwynne.stoppedBrownianLaw U y μ) < ENNReal.ofReal δ →
      ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw m x {ξ | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 ξ) ∈ A} ≤
        planarBrownianMotion (vertexPoint ε η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ := by
  obtain ⟨s, hs, hshift⟩ := exists_forall_start_shift hρR (κ := ENNReal.ofReal (κ / 3))
    (θ := ENNReal.ofReal (κ / 3)) (ENNReal.ofReal_pos.2 (by linarith))
    (ENNReal.ofReal_pos.2 (by linarith))
  refine ⟨s, hs, ?_⟩
  intro α m₀ hα hm₀ hm₁ ε η m x hx hfin y U hUc hy μ hμ δ hδ hδκ h A
  have h1 := StopAtExitWalkBound.srwLaw_allSet_le_of_levyProkhorovEDist hα hm₀ hm₁ ε η m x
    (ball (0 : ℂ) R) isOpen_ball Metric.isBounded_ball hfin y U hUc μ hμ hδ
    (κ := κ / 3) (by linarith) h
  have h2 := hshift
    (fun A => srwLaw m x {ξ | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 ξ) ∈ A})
    (ENNReal.ofReal (δ + κ / 3)) (ENNReal.ofReal δ) (vertexPoint ε η x)
    (Complex.orthonormalBasisOneI.repr.symm y) hx hy h1 A
  refine h2.trans (add_le_add (measure_mono ?_) ?_)
  · rintro b ⟨f, hf, hb⟩
    refine ⟨f, hf, hb.trans_le ?_⟩
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [← ENNReal.ofReal_add (by linarith) hδ.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end MatedCRT.StopAtExitStartTransfer
