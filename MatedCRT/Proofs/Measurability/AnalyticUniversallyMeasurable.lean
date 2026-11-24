import MatedCRT.Proposed.PrestonAnalytic2008
import LatticeProb.Prob.AnalyticUniversalMeasurable

/-!
# Analytic subsets of Polish spaces are universally measurable

`PrestonAnalyticUniversallyMeasurableStmt` holds: every analytic subset of a Polish space with its Borel σ-algebra is
null-measurable for every finite measure. This is `LatticeProb.AnalyticSet.nullMeasurableSet` of Lattice-Probability
(Lusin; Kechris, *Classical Descriptive Set Theory*, Theorem 21.10, through the capacitability of analytic sets,
Theorem 30.13), applied with the metrizability of a Polish space.

## Main statements

* `prestonAnalyticUniversallyMeasurableStmt_holds`.
-/

namespace MatedCRT

/-- **Analytic subsets of a Polish space are universally measurable**: for every finite Borel measure `μ`, every
analytic set is `μ`-null-measurable. -/
theorem prestonAnalyticUniversallyMeasurableStmt_holds : PrestonAnalyticUniversallyMeasurableStmt := by
  intro X _ _ _ _ S hS μ _
  exact LatticeProb.AnalyticSet.nullMeasurableSet μ hS

end MatedCRT
