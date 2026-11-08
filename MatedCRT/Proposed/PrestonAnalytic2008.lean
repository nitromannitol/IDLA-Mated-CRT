import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Staged literature input: analytic sets are universally measurable (Preston 2008)

Staged for independent source audit; the operator source-checks this file before any promotion to
`MatedCRT/External`. This file states one proposition. It is not an axiom and not a proof of the cited theorem.
It is used by `MatedCRT/Proofs/Sec1/EnvironmentScaling/AllStartsClock.lean` only as an explicit hypothesis.
-/

namespace MatedCRT

open MeasureTheory

/-- Preston, *Some Notes on Standard Borel and Related Spaces*, arXiv:0809.3066v1 (2008).
Printed p. 4 (Section 1): a subset `A` of `M` is analytic if it is empty or `A = τ(ℕ^ℕ)` for a continuous
`τ : ℕ^ℕ → M`; Mathlib's `AnalyticSet` is the same notion (continuous image of a Polish space).
Printed p. 39, Theorem 7.1 (PDF p. 40), `A ⊂ B*`: every analytic set is universally measurable, that is,
null-measurable for every finite Borel measure. The Lean statement specialises to Polish spaces, the only case
used (`C(E,ℝ)` with the compact-open topology and products with `ℂ`). The printed hypotheses on the ambient space
in Section 7 were not checked in this staging; the source-check must confirm that Section 7 covers Polish spaces. -/
def PrestonAnalyticUniversallyMeasurableStmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
    AnalyticSet S → ∀ μ : Measure X, IsFiniteMeasure μ → NullMeasurableSet S μ

end MatedCRT
