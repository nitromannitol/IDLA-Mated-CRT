import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuumCandidateMeasurable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Countable determining families of tests -/

namespace MatedCRT

open Set TopologicalSpace

/-- A second-countable space admits a countable determining subfamily for every
family of tests. It determines all inequalities given by continuous functionals
simultaneously. -/
theorem exists_countable_tests_determining_continuous_inequalities
    {A X : Type} [TopologicalSpace X] [SecondCountableTopology X]
    (V : Set A) (f : A → X) :
    ∃ C : Set A, C.Countable ∧ C ⊆ V ∧
      ∀ F : X → ℝ, Continuous F →
        ((∀ a ∈ C, 0 ≤ F (f a)) ↔ ∀ a ∈ V, 0 ≤ F (f a)) := by
  classical
  obtain ⟨T, hTc, hTV, hTd⟩ := exists_countable_dense_subset (f '' V)
  let g : T → A := fun y => Classical.choose (hTV y.property)
  have hg (y : T) : g y ∈ V ∧ f (g y) = y :=
    Classical.choose_spec (hTV y.property)
  have : Countable T := hTc.to_subtype
  have hcount : (range g).Countable := Set.countable_range g
  have hsubset : range g ⊆ V := by
    rintro a ⟨y, rfl⟩
    exact (hg y).1
  refine ⟨range g, hcount, hsubset, ?_⟩
  intro F hF
  constructor
  · intro hC a ha
    have hT : T ⊆ {x | 0 ≤ F x} := by
      intro y hy
      let yy : T := ⟨y, hy⟩
      have h := hC (g yy) ⟨yy, rfl⟩
      simpa only [(hg yy).2, yy, Subtype.coe_mk, mem_ofPred_eq] using h
    have hclosed : IsClosed {x | 0 ≤ F x} := isClosed_le continuous_const hF
    exact closure_minimal hT hclosed (hTd ⟨a, ha, rfl⟩)
  · intro hV a ha
    exact hV a (hsubset ha)

/-- Tests whose values and Laplacians are continuous on a fixed compact space
admit a countable family determining every pair of continuous integral
functionals. The family depends only on the tests, not on the functionals. -/
theorem exists_countable_tests_determining_pairings
    {A K : Type} [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K] [SecondCountableTopology K]
    (V : Set A) (φ ψ : A → C(K, ℝ)) :
    ∃ C : Set A, C.Countable ∧ C ⊆ V ∧
      ∀ F G : C(K, ℝ) → ℝ, Continuous F → Continuous G →
        ((∀ a ∈ C, F (ψ a) ≤ G (φ a)) ↔ ∀ a ∈ V, F (ψ a) ≤ G (φ a)) := by
  obtain ⟨C, hCc, hCV, hC⟩ :=
    exists_countable_tests_determining_continuous_inequalities V (fun a => (φ a, ψ a))
  refine ⟨C, hCc, hCV, ?_⟩
  intro F G hF hG
  simpa only [sub_nonneg] using
    hC (fun p => G p.1 - F p.2)
      ((hG.comp continuous_fst).sub (hF.comp continuous_snd))

/-- Integration against a finite measure is continuous in the uniform topology
on continuous functions over a compact space. -/
theorem continuous_integral_on_continuousMap
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K)
    [MeasureTheory.IsFiniteMeasure μ] :
    Continuous (fun f : C(K, ℝ) => ∫ x, f x ∂μ) := by
  have h := (MeasureTheory.continuous_integral (μ := μ) (G := ℝ)).comp
    (ContinuousMap.toLp 1 μ ℝ).continuous
  convert h using 1
  funext f
  exact (MeasureTheory.integral_congr_ae (ContinuousMap.coeFn_toLp μ f)).symm

/-- A single countable subfamily determines all distributional inequalities
against pairs of finite measures on the compact space. -/
theorem exists_countable_tests_determining_integrals
    {A K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (V : Set A) (φ ψ : A → C(K, ℝ)) :
    ∃ C : Set A, C.Countable ∧ C ⊆ V ∧
      ∀ (μ ν : MeasureTheory.Measure K),
        ∀ (_ : MeasureTheory.IsFiniteMeasure μ) (_ : MeasureTheory.IsFiniteMeasure ν),
        ((∀ a ∈ C, (∫ x, ψ a x ∂μ) ≤ ∫ x, φ a x ∂ν) ↔
          ∀ a ∈ V, (∫ x, ψ a x ∂μ) ≤ ∫ x, φ a x ∂ν) := by
  obtain ⟨C, hCc, hCV, hC⟩ := exists_countable_tests_determining_pairings V φ ψ
  refine ⟨C, hCc, hCV, ?_⟩
  intro μ ν hμ hν
  exact hC _ _ (continuous_integral_on_continuousMap μ)
    (continuous_integral_on_continuousMap ν)

/-- The same determining family works for all continuous weights in the
Laplacian integral and all pairs of finite measures. -/
theorem exists_countable_tests_determining_weighted_integrals
    {A K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (V : Set A) (φ ψ : A → C(K, ℝ)) :
    ∃ C : Set A, C.Countable ∧ C ⊆ V ∧
      ∀ (μ ν : MeasureTheory.Measure K),
        ∀ (_ : MeasureTheory.IsFiniteMeasure μ) (_ : MeasureTheory.IsFiniteMeasure ν),
        ∀ w : C(K, ℝ),
        ((∀ a ∈ C, (∫ x, w x * ψ a x ∂μ) ≤ ∫ x, φ a x ∂ν) ↔
          ∀ a ∈ V, (∫ x, w x * ψ a x ∂μ) ≤ ∫ x, φ a x ∂ν) := by
  obtain ⟨C, hCc, hCV, hC⟩ := exists_countable_tests_determining_pairings V φ ψ
  refine ⟨C, hCc, hCV, ?_⟩
  intro μ ν hμ hν w
  have hweighted : Continuous (fun f : C(K, ℝ) => ∫ x, w x * f x ∂μ) := by
    convert (continuous_integral_on_continuousMap μ).comp
      (continuous_const.mul (continuous_id : Continuous (fun f : C(K, ℝ) => f))) using 1
    rfl
  exact hC _ _ hweighted (continuous_integral_on_continuousMap ν)

end MatedCRT
