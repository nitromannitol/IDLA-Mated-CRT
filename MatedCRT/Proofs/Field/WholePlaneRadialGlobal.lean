import MatedCRT.Proofs.Field.WholePlaneLateralGauss

/-!
# A global Gaussian space for the radial level integrals, and a measurable path functional (eq:gff)

For a radial process `W` (`IsRadialLevelData`) and an indexed family of region circles `(r i, z i)`:

* `radial_global_space`: the radial circle averages are a.s. equal to random variables `Y i` lying in one centred Gaussian
  space containing `M₀`;
* `levelRiemannLim`: the iterated limit of the level-integral Riemann sums is a measurable function of the path, equal
  to the level integral on continuous paths (`levelRiemannLim_eq_levelIntegral`). It is the measurable functional of
  the radial path through which the radial circle averages are independent of the lateral part.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

section Global

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ → Ω → ℝ} {M₀ : Submodule ℝ (Ω → ℝ)}

/-- **One centred Gaussian space for all radial circle averages.** -/
theorem radial_global_space {ι : Type*} (r : ι → ℝ) (z : ι → ℂ) (hreg : ∀ i, InLevelRegion (r i) (z i))
    (hW : IsRadialLevelData P W M₀) (hM₀ : IsCentredGaussianSpace P M₀) :
    ∃ (Y : ι → Ω → ℝ) (M : Submodule ℝ (Ω → ℝ)), IsCentredGaussianSpace P M ∧ M₀ ≤ M ∧
      (∀ i, Measurable (Y i)) ∧ (∀ i, Y i ∈ M) ∧
      (∀ i, ∀ᵐ ω ∂P, Real.circleAverage (fun x => W (-Real.log ‖x‖) ω) (z i) (r i) = Y i ω) := by
  choose T Yv hspec using fun i => radial_level_rep hW hM₀ (hreg i)
  have hTm : ∀ i k, Measurable (T i k) := fun i k => (hspec i).1 k
  have hTlim : ∀ i k, IsAeLimitOf P M₀ (T i k) := fun i k => (hspec i).2.1 k
  have hYm : ∀ i, Measurable (Yv i) := fun i => (hspec i).2.2.1
  have hconv : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun k => T i k ω) atTop (𝓝 (Yv i ω)) := fun i => (hspec i).2.2.2.1
  have havg : ∀ i, ∀ᵐ ω ∂P, Real.circleAverage (fun x => W (-Real.log ‖x‖) ω) (z i) (r i) = Yv i ω :=
    fun i => (hspec i).2.2.2.2.1
  let Z : ι × ℕ → Ω → ℝ := fun x => T x.1 x.2
  have hZm : ∀ x, Measurable (Z x) := fun x => hTm x.1 x.2
  have hZl : ∀ x, IsAeLimitOf P M₀ (Z x) := fun x => hTlim x.1 x.2
  have hM1 := isCentredGaussianSpace_sup_span_range hM₀ Z hZm hZl
  have hmem1 : ∀ i k, T i k ∈ (M₀ ⊔ Submodule.span ℝ (Set.range Z) : Submodule ℝ (Ω → ℝ)) :=
    fun i k => Submodule.mem_sup_right (Submodule.subset_span ⟨(i, k), rfl⟩)
  have hY1 : ∀ i, IsAeLimitOf P (M₀ ⊔ Submodule.span ℝ (Set.range Z) : Submodule ℝ (Ω → ℝ)) (Yv i) :=
    fun i => ⟨T i, fun k => hmem1 i k, hconv i⟩
  have hM2 := isCentredGaussianSpace_sup_span_range hM1 Yv hYm hY1
  refine ⟨Yv, _, hM2, le_trans le_sup_left le_sup_left, hYm, fun i => ?_, havg⟩
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)

/-- The iterated limit of the level-integral Riemann sums of a path (a measurable functional of the path). -/
noncomputable def levelRiemannLim {α : Type*} [MeasurableSpace α] (ν : Measure α) (g s : α → ℝ)
    (w : ℝ → ℝ) : ℝ :=
  limsup (fun k : ℕ => limsup (fun n : ℕ => levelRiemann ν g s n k w) atTop) atTop

omit [IsProbabilityMeasure P] in
/-- The iterated Riemann limit is measurable in the path. -/
theorem measurable_levelRiemannLim {α : Type*} [MeasurableSpace α] (ν : Measure α) (g s : α → ℝ) :
    Measurable (levelRiemannLim ν g s) := by
  unfold levelRiemannLim
  refine Measurable.limsup fun k => Measurable.limsup fun n => measurable_levelRiemann ν g s n k
  
/-- On a continuous path with integrable level integrand, the iterated Riemann limit is the level integral. -/
theorem levelRiemannLim_eq_levelIntegral {α : Type*} [MeasurableSpace α] {ν : Measure α} {g s : α → ℝ}
    (hs : Measurable s) (hg : Integrable g ν) {w : ℝ → ℝ} (hw : Continuous w)
    (hint : Integrable (fun x => g x * w (s x)) ν) :
    levelRiemannLim ν g s w = levelIntegral ν g s w := by
  unfold levelRiemannLim
  have h1 : ∀ k : ℕ, limsup (fun n : ℕ => levelRiemann ν g s n k w) atTop = levelTrunc ν g s k w :=
    fun k => (tendsto_levelRiemann hs hg k hw).limsup_eq
  simp only [h1]
  exact (tendsto_levelTrunc hs hint).limsup_eq

end Global

end MatedCRT.Field
