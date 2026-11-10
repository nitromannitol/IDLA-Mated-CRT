import MatedCRT.FirstPass.S4S6c.OpenAnnulus68

/-!
# Finiteness and sparsity inputs of the local test `hloc` (q2, task fp-S4S6c-envscaling-6-7-6-8)

* `ncard_inter_lt_of_ncard_lt`: the sparsity input `hsp` of `Uniform68Events.hloc_point`,
  `(A ∩ X).ncard < s₁ r^(2β)/ε`, follows from the configuration sparsity `(A).ncard < s₁ r^(2β)/ε` of the
  target statement `UniformConstantOrderLowerBoundStmt` (FirstPass/S6d.lean:90, with `A = S' \ Θ`), for finite `A`.
* `measure_closedBall_ne_top`, `measure_openAnnulus_ne_top`: the finiteness inputs `hmfin` and `hμA` of the local test,
  from finiteness of `μ` on compact sets (the local finiteness part of `LQGMeasurePropertiesStmt`, Draft/Section2.lean:39,
  item 1: `IsLocallyFiniteMeasure (μ ω)` almost surely).

Terminology: LQG measure `μ` (Duplantier-Sheffield, Berestycki-Powell); Armitage-Gardiner annulus `A_{R,2R}(z)`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- Sparsity passes to the intersection with any set: `(A ∩ X).ncard ≤ A.ncard` for finite `A`. -/
theorem ncard_inter_lt_of_ncard_lt {α : Type*} {A X : Set α} (hA : A.Finite) {s : ℝ}
    (h : (A.ncard : ℝ) < s) : ((A ∩ X).ncard : ℝ) < s := by
  have hle : (A ∩ X).ncard ≤ A.ncard := Set.ncard_le_ncard Set.inter_subset_left hA
  exact lt_of_le_of_lt (by exact_mod_cast hle) h

/-- Finiteness of `μ` on closed balls, for a locally finite measure. -/
theorem measure_closedBall_ne_top {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (x : ℂ) (r : ℝ) :
    μ (closedBall x r) ≠ ⊤ :=
  (measure_closedBall_lt_top (μ := μ) (x := x) (r := r)).ne

/-- Finiteness of `μ` on the open annulus `A_{R,2R}(z)` (contained in `closedBall z (2R)`). -/
theorem measure_openAnnulus_ne_top {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (z : ℂ) (R : ℝ) :
    μ (openAnnulus z R) ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_closedBall_ne_top (μ := μ) z (2 * R))
    (measure_mono (openAnnulus_subset_closedBall z R))

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.ncard_inter_lt_of_ncard_lt
#print axioms MatedCRT.measure_openAnnulus_ne_top
