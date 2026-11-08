import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Staged literature inputs: analytic sets are universally measurable (Preston 2008)

Staged for independent source audit; the operator source-checks this file before any promotion to
`MatedCRT/External`. This file states two propositions. Each is an explicit hypothesis, not a proof of the cited statement.

* `PrestonAnalyticCantorStmt` is the printed statement: Preston, arXiv:0809.3066v1, Theorem 7.1 (printed p. 39, PDF p. 40),
  `A ⊂ B*`. The ambient space is the Cantor space `M = {0,1}^ℕ` of the introduction ("The space involved here is
  M = {0,1}^ℕ"). Section 5 defines `A`, the analytic subsets of `M` (empty, or `τ(ℕ^ℕ)` for a continuous `τ`), and `B`,
  the Borel subsets of `M`, with `B ⊂ A` (Proposition 5.1). Section 7 takes finite measures on `B`, and `B*` is the
  intersection of the completions of those measures. Checked on the arXiv text (z1, 2026-11-08): Theorem 7.1 is stated
  for `M`, and the text after it contains no statement for a general Polish space.
* `PrestonAnalyticUniversallyMeasurableStmt` is the Polish version consumed by `AllStartsClock.lean`. It is NOT the printed
  statement. It is standard for every Polish space, but the notes print no transfer from `M` to a general Polish space, so it
  is not source-ready as a Preston citation. The operator must supply a locator or a transfer argument.

Mathlib's `AnalyticSet` is the range of a continuous map from a Polish space (`analyticSet_iff_exists_polishSpace_range`,
MeasureTheory/Constructions/Polish/Basic.lean:212). For nonempty sets this agrees with Preston's definition, since every
nonempty Polish space is a continuous image of `ℕ → ℕ` (`PolishSpace.exists_nat_nat_continuous_surjective`).
-/

namespace MatedCRT

open MeasureTheory

/-- Preston, Theorem 7.1 (printed p. 39, PDF p. 40): every analytic subset of the Cantor space `M = {0,1}^ℕ` is universally
measurable, that is, null-measurable for every finite Borel measure on `M`. `M` is `ℕ → Bool` with the product topology;
the product σ-algebra is its Borel σ-algebra (countable product of second countable spaces). -/
def PrestonAnalyticCantorStmt : Prop :=
  ∀ S : Set (ℕ → Bool), AnalyticSet S → ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → NullMeasurableSet S μ

/-- Every analytic subset of a Polish space `X` (with its Borel σ-algebra) is universally measurable. This is the hypothesis
used by `AllStartsClock.lean` (`allStartsSet_isUniversallyMeasurable`, `ae_allStarts_of_map_eq`, and
`rescaledConeClockStep_of_inputs`). It is NOT the printed Theorem 7.1: see the module docstring. -/
def PrestonAnalyticUniversallyMeasurableStmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
    AnalyticSet S → ∀ μ : Measure X, IsFiniteMeasure μ → NullMeasurableSet S μ

end MatedCRT
