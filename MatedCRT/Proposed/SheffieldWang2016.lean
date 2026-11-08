import MatedCRT.Defs.DirichletGFF
import HarmonicBalls.Defs.LQG

/-!
# All-scale circle-average convergence on a bounded domain

Staged literature input for source audit; the proposition is not an axiom.
-/

namespace MatedCRT

open HarmonicBalls MeasureTheory Filter Set
open scoped Topology

/-- Sheffield--Wang, *Field-measure correspondence in Liouville quantum gravity
almost surely commutes with all conformal maps simultaneously*,
arXiv:1605.06171v2, Theorem 1.1, p. 3, with its domain and field specified
on p. 2. This is its compactly supported test-function consequence for a
bounded simply connected domain and a zero-boundary GFF. The supplied measure
is assumed to be the dyadic limit on the domain; the conclusion concerns all
positive scales on one event. Circle averages outside the admissible circles
are set to zero to specify a total representative; compactly supported tests
are insensitive to this extension for sufficiently small scales. No cone,
random-radius or nonzero-boundary conclusion is asserted here. -/
def SheffieldWangCircleAverageAllScaleStmt : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (γ : ℝ),
    IsOpen D → D ≠ univ → SimplyConnectedSpace D → Bornology.IsBounded D →
    IsDirichletGFF P D h hcirc → 0 ≤ γ → γ < 2 →
    (∀ ω r z, ¬ Metric.closedBall z r ⊆ D → hcirc ω r z = 0) →
    (∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
        Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hcirc ω) (dyadicScale n)))
          atTop (𝓝 (∫ z, f z ∂(μ ω)))) →
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (hcirc ω) ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂(μ ω)))

/-- Sheffield--Wang, *Field-measure correspondence in Liouville quantum gravity almost surely commutes with all
conformal maps simultaneously*, arXiv:1605.06171v2, Theorem 1.1, p. 3, with domain and field as on p. 2.
Compact-interior form of `SheffieldWangCircleAverageAllScaleStmt`: the same zero-boundary GFF, dyadic limit
hypothesis, admissible-circle convention, `0 ≤ γ < 2` scope and conclusion, but the supplied limit is required only
to be finite on compact subsets of `D` (`μ ω K < ⊤` for compact `K ⊆ D`), not locally finite on all of `ℂ`.
Weak convergence in `D` gives no finiteness of the limit at boundary points of `D`, and no total mass on `D` is
asserted. Staged literature input; not an axiom. -/
def SheffieldWangCircleAverageAllScaleInteriorStmt : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (γ : ℝ),
    IsOpen D → D ≠ univ → SimplyConnectedSpace D → Bornology.IsBounded D →
    IsDirichletGFF P D h hcirc → 0 ≤ γ → γ < 2 →
    (∀ ω r z, ¬ Metric.closedBall z r ⊆ D → hcirc ω r z = 0) →
    (∀ᵐ ω ∂P, (∀ K : Set ℂ, IsCompact K → K ⊆ D → μ ω K < ⊤) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
        Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (hcirc ω) (dyadicScale n)))
          atTop (𝓝 (∫ z, f z ∂(μ ω)))) →
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (hcirc ω) ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂(μ ω)))

/-- Backward compatibility: the compact-interior statement implies the staged global-finiteness statement
`SheffieldWangCircleAverageAllScaleStmt`, because local finiteness of `μ ω` on `ℂ` gives finiteness on compact sets. -/
theorem sheffieldWangCircleAverageAllScaleStmt_of_interior
    (h : SheffieldWangCircleAverageAllScaleInteriorStmt.{0}) :
    SheffieldWangCircleAverageAllScaleStmt.{0} := by
  intro Ω _ P _ D h' hcirc μ γ hD hDne hsc hbd hdir hγ0 hγ2 hzero hfin
  refine h Ω P D h' hcirc μ γ hD hDne hsc hbd hdir hγ0 hγ2 hzero ?_
  filter_upwards [hfin] with ω hω
  have : IsLocallyFiniteMeasure (μ ω) := hω.1
  have : IsFiniteMeasureOnCompacts (μ ω) := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  exact ⟨fun K hK _ => hK.measure_lt_top, hω.2⟩

end MatedCRT
