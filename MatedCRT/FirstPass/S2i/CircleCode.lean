import MatedCRT.FirstPass.S2i.BorelFactor
import MatedCRT.Defs.QuantumCone

/-! # Dense evaluation code of circle average processes

The circle average process lives in the uncountable product `Set.Ioi (0 : ℝ) × ℂ → ℝ`. A fixed dense sequence `D` of
positive-radius points turns it into a countable real code, which is measurable (`measurable_circleCode`). A continuous
circle average process is determined by its code (`eq_of_circleCode_eq`): this is the mechanism making the canonical
factorization of `ConeCanonicalFactorStep` a function of the code. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The positive-radius circle domain `(0, ∞) × ℂ` (the index set of `circleProcess`). -/
abbrev CirclePt : Type := Set.Ioi (0 : ℝ) × ℂ

/-- A fixed dense sequence of positive-radius circle points (the separability of `(0, ∞) × ℂ`). -/
theorem exists_dense_circlePt : ∃ D : ℕ → CirclePt, DenseRange D :=
  TopologicalSpace.exists_dense_seq CirclePt

/-- The countable evaluation code of a process `p : (0, ∞) × ℂ → ℝ` along the sequence `D`. -/
def circleCode (D : ℕ → CirclePt) (p : CirclePt → ℝ) : ℕ → ℝ :=
  fun k => p (D k)

/-- The evaluation code is measurable in the product σ-algebra of the process. -/
theorem measurable_circleCode (D : ℕ → CirclePt) : Measurable (circleCode D) :=
  measurable_pi_iff.mpr fun k => measurable_pi_apply (D k)

/-- The circle average process of a function continuous on `(0, ∞) × ℂ` is continuous as a function on `CirclePt`. -/
theorem continuous_circleProcess_of_continuousOn {c : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Continuous fun p : CirclePt => circleProcess c p := by
  have hf : Continuous fun p : CirclePt => ((p.1 : ℝ), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ p : CirclePt, ((p.1 : ℝ), p.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := fun p =>
    ⟨p.1.2, mem_univ _⟩
  exact hc.comp_continuous hf hmem

/-- Two continuous positive-radius circle average processes with the same evaluation code agree everywhere. -/
theorem eq_of_circleCode_eq {D : ℕ → CirclePt} (hD : DenseRange D) {p q : CirclePt → ℝ}
    (hp : Continuous p) (hq : Continuous q) (h : circleCode D p = circleCode D q) : p = q := by
  refine Continuous.ext_on hD hp hq ?_
  rintro _ ⟨k, rfl⟩
  exact congrFun h k

end MatedCRT
