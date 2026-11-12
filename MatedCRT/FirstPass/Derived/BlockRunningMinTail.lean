import MatedCRT.FirstPass.Derived.BlockDegreeRunningMin

/-!
# Tail of the running-minimum count of a block, from the law of the boundary-length paths

Berestycki–Gwynne (2020), Appendix A, Lemma A.9 bounds the tail of the number of cells of a block of `N`
cells which contain a running minimum of a standard Brownian motion. The count of (A.34) entering the
degree estimate of a block, `blockRunningMinCount`, has four terms: running minima of `L`, of `R` and of
their time reversals on the block. This file transfers tail bounds for the four terms, stated for a law
`μ` on `Path2 = C(ℝ, ℝ × ℝ)`, to the probability measure of a random variable with law `μ` (in particular
to the boundary-length pair `(L, R) = S.bm` of a valid mated-CRT environment), by a union bound.

## Main results

* `measure_lt_blockRunningMinCount_le_of_map`: if each of the four counts exceeds `m` with `μ`-probability at
  most `b` under the law `μ = P.map f`, then `P {4 m < blockRunningMinCount} ≤ 4 b`;
* `MatedCRTEnv.IsValid.isCorrelatedBM2_map_bm`: the law of `S.bm` is the correlated Brownian law and
  `S.bm` is measurable, for a valid environment;
* `MatedCRTEnv.IsValid.measure_lt_blockRunningMinCount_le`: the bound for `(L, R) = S.bm`.
-/

open Finset MeasureTheory MatedCRTHarmonic.MatedCRT

namespace MatedCRT

theorem lrCoord_zero_apply (t : ℝ) (p : Path2) : lrCoord 0 t p = (p t).1 := by
  simp [lrCoord]

theorem lrCoord_one_apply (t : ℝ) (p : Path2) : lrCoord 1 t p = (p t).2 := by
  simp [lrCoord]

/-- **Union bound for the running-minimum count of a block.** If, under the law `μ = P.map f` of a random
path `f`, each coordinate path and its time reversal on the block `[lo, hi]` has more than `m` cells
containing a running minimum with probability at most `b`, then the four-term count
`blockRunningMinCount` exceeds `4 m` with `P`-probability at most `4 b`. -/
theorem measure_lt_blockRunningMinCount_le_of_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → Path2} (hf : AEMeasurable f P) {ε m : ℝ} {lo hi : ℤ} {b : ENNReal}
    (h : ∀ i : Fin 2,
      P.map f {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) lo hi) : ℝ)} ≤ b ∧
      P.map f {p | m < (#(blockRunningMinCells ε
        (blockReversal ε (fun t => lrCoord i t p) lo hi) lo hi) : ℝ)} ≤ b) :
    P {ω | 4 * m < (blockRunningMinCount ε (fun t => (f ω t).1) (fun t => (f ω t).2) lo hi : ℝ)} ≤
      4 * b := by
  set A : Fin 2 → Set Path2 := fun i =>
    {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) lo hi) : ℝ)}
  set A' : Fin 2 → Set Path2 := fun i =>
    {p | m < (#(blockRunningMinCells ε (blockReversal ε (fun t => lrCoord i t p) lo hi) lo hi) : ℝ)}
  have hsub : {ω | 4 * m < (blockRunningMinCount ε (fun t => (f ω t).1) (fun t => (f ω t).2) lo hi : ℝ)}
      ⊆ ((f ⁻¹' A 0 ∪ f ⁻¹' A' 0) ∪ f ⁻¹' A 1) ∪ f ⁻¹' A' 1 := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_preimage, A, A', Set.mem_ofPred_eq, not_or, not_lt,
      lrCoord_zero_apply, lrCoord_one_apply] at hnot
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnot
    simp only [blockRunningMinCount, Nat.cast_add] at hω
    linarith
  calc P {ω | 4 * m < (blockRunningMinCount ε (fun t => (f ω t).1) (fun t => (f ω t).2) lo hi : ℝ)}
      ≤ P (((f ⁻¹' A 0 ∪ f ⁻¹' A' 0) ∪ f ⁻¹' A 1) ∪ f ⁻¹' A' 1) := measure_mono hsub
    _ ≤ P (f ⁻¹' A 0) + P (f ⁻¹' A' 0) + P (f ⁻¹' A 1) + P (f ⁻¹' A' 1) := by
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      exact measure_union_le _ _
    _ ≤ P.map f (A 0) + P.map f (A' 0) + P.map f (A 1) + P.map f (A' 1) := by
      gcongr <;> exact Measure.le_map_apply hf _
    _ ≤ b + b + b + b := by
      gcongr
      exacts [(h 0).1, (h 0).2, (h 1).1, (h 1).2]
    _ = 4 * b := by ring

/-- For a valid environment, the boundary-length pair `S.bm` is measurable and its law is the correlated
two-sided Brownian law of the mating-of-trees coupling (DMS14). -/
theorem MatedCRTEnv.IsValid.isCorrelatedBM2_map_bm {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    IsCorrelatedBM2 γ (S.P.map S.bm) ∧ Measurable S.bm := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, -⟩ := hS.matingOfTrees
  exact ⟨hMoT.boundaryLawBM, hMoT.measurable_curves.2.2.2⟩

/-- **The running-minimum count of a block of a valid environment.** If, under the correlated Brownian
law, each coordinate path and its time reversal on the block `[lo, hi]` has more than `m` cells containing
a running minimum with probability at most `b`, then for the boundary-length pair `(L, R) = S.bm` the
four-term count of (A.34) exceeds `4 m` with probability at most `4 b`. -/
theorem MatedCRTEnv.IsValid.measure_lt_blockRunningMinCount_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε m : ℝ} {lo hi : ℤ}
    {b : ENNReal}
    (h : ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ i : Fin 2,
      μ {p | m < (#(blockRunningMinCells ε (fun t => lrCoord i t p) lo hi) : ℝ)} ≤ b ∧
      μ {p | m < (#(blockRunningMinCells ε
        (blockReversal ε (fun t => lrCoord i t p) lo hi) lo hi) : ℝ)} ≤ b) :
    S.P {ω | 4 * m <
      (blockRunningMinCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2) lo hi : ℝ)} ≤ 4 * b :=
  measure_lt_blockRunningMinCount_le_of_map hS.isCorrelatedBM2_map_bm.2.aemeasurable
    (h _ hS.isCorrelatedBM2_map_bm.1)

end MatedCRT
