import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Staged literature inputs: analytic sets are universally measurable (Preston 2008)

Staged for independent source audit; this file is source-checked before any promotion to
`MatedCRT/External`. This file states three propositions. Each is an explicit hypothesis, not a proof of the cited statement.

* `PrestonAnalyticCantorStmt` is the printed statement: Preston, arXiv:0809.3066v1, Theorem 7.1 (printed p. 39, PDF p. 40),
  `A ⊂ B*`. The ambient space is the Cantor space `M = {0,1}^ℕ` ("The space involved here is M = {0,1}^ℕ"). Section 5 defines
  `A`, the analytic subsets of `M`, and `B`, the Borel subsets of `M`. Section 7 takes finite measures on `B`, and `B*` is the
  intersection of the completions of those measures. Theorem 7.1 is stated for `M` only.
* `PrestonTheorem61Stmt` is the printed Theorem 6.1(1) (printed p. 35, PDF p. 36) for a complete separable metric space with its
  Borel σ-algebra, with Preston's notion of type `B` (introduction, printed p. 3; Section 6, printed p. 35). Exact
  measurability is Section 2 (printed p. 5): `f : (X, E) → (Y, F)` is exactly measurable if `f⁻¹(F) = E`, stated here as
  `MeasurableSpace.comap f F = E`. Part (2) of the printed theorem is not staged.
* `PrestonAnalyticUniversallyMeasurableStmt` is the Polish version consumed by `AllStartsClock.lean`. Preston does not print it
  for a general Polish space. It is derived from the two inputs above in
  `MatedCRT/Proofs/Sec1/EnvironmentScaling/PrestonPolishTransfer.lean` (`prestonAnalyticUniversallyMeasurable_of_cantor`), by the
  injectivity of an exactly measurable map on a separated space (Preston, Proposition 2.4, printed p. 8).

Mathlib's `AnalyticSet` is the range of a continuous map from a Polish space (`analyticSet_iff_exists_polishSpace_range`,
MeasureTheory/Constructions/Polish/Basic.lean). For nonempty sets this agrees with Preston's definition, since every nonempty
Polish space is a continuous image of `ℕ → ℕ` (`PolishSpace.exists_nat_nat_continuous_surjective`).
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
`rescaledConeClockStep_of_inputs`). Preston does not print this statement for a general Polish space;
`prestonAnalyticUniversallyMeasurable_of_cantor` (`PrestonPolishTransfer.lean`) derives it from
`PrestonAnalyticCantorStmt` and `PrestonTheorem61Stmt`. -/
def PrestonAnalyticUniversallyMeasurableStmt : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
    AnalyticSet S → ∀ μ : Measure X, IsFiniteMeasure μ → NullMeasurableSet S μ

/-- A type `B` space in the sense of Preston (introduction, printed p. 3; Section 6, printed p. 35): a countably generated
measurable space `(X, E)` is type `B` if there is an exactly measurable `f : (X, E) → (M, 𝓑)` with `f(X) ∈ 𝓑`, where
`M = {0,1}^ℕ` is `ℕ → Bool`, and `𝓑` is its Borel σ-algebra, which is the product σ-algebra `MeasurableSpace.pi`
(`Pi.borelSpace`). Countably generated means `E = σ(C)` for a countable `C`. Exact measurability means `f⁻¹(𝓑) = E`
(Section 2, printed p. 5), stated as `MeasurableSpace.comap f 𝓑 = E`. -/
def IsTypeBSpace (X : Type) [MeasurableSpace X] : Prop :=
  (∃ C : Set (Set X), C.Countable ∧ (inferInstance : MeasurableSpace X) = MeasurableSpace.generateFrom C) ∧
    ∃ f : X → (ℕ → Bool),
      MeasurableSpace.comap f (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)) = (inferInstance : MeasurableSpace X) ∧
      MeasurableSet (Set.range f)

/-- Preston, Theorem 6.1(1) (printed p. 35, PDF p. 36): "Let X be a complete separable metric space and B_X be the σ-algebra of
Borel subsets of X. Then (X, B_X) is a type B space." Part (2) of the printed theorem is not staged. -/
def PrestonTheorem61Stmt : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    [BorelSpace X],
    IsTypeBSpace X

end MatedCRT
