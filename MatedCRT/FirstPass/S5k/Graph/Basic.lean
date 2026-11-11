import MatedCRT.FirstPass.S5k.Uniqueness

/-!
# First pass: basic objects of the Borel graph of (6)

The conditions (6) are presented as a Borel subset of `M_f(K) × C(K)`,
with `K = B̄_ρ`. This file fixes the spaces: `DiskFun ρ = C(B̄_ρ, ℝ)`, its extension by zero `extDisk`, the space
`FinMeasDisk ρ` of finite measures concentrated on `B̄_ρ`, and generic facts: a countable dense family for a separable
image (used for the countable presentations), and measurability of `ν ↦ ∫ a dν` on finite measures.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology

/-- The continuous functions on the closed disk `B̄_ρ`: the space `C(K)` of Step 4.1. -/
abbrev DiskFun (ρ : ℝ) := C(closedBall (0 : ℂ) ρ, ℝ)

/-- The finite measures on `ℂ` concentrated on `B̄_ρ`: the space `M_f(K)` of Step 4.1. -/
abbrev FinMeasDisk (ρ : ℝ) := {ν : Measure ℂ // IsFiniteMeasure ν ∧ ν.restrict (closedBall (0 : ℂ) ρ) = ν}

open scoped Classical in
/-- Extension by zero of `f ∈ C(B̄_ρ)` to `ℂ`. -/
noncomputable def extDisk (ρ : ℝ) (f : DiskFun ρ) : ℂ → ℝ :=
  fun x => if h : x ∈ closedBall (0 : ℂ) ρ then f ⟨x, h⟩ else 0

theorem extDisk_apply_of_mem {ρ : ℝ} (f : DiskFun ρ) {x : ℂ} (h : x ∈ closedBall (0 : ℂ) ρ) :
    extDisk ρ f x = f ⟨x, h⟩ := by
  simp [extDisk, h]

theorem extDisk_apply_of_notMem {ρ : ℝ} (f : DiskFun ρ) {x : ℂ} (h : x ∉ closedBall (0 : ℂ) ρ) :
    extDisk ρ f x = 0 := by
  simp [extDisk, h]

theorem continuousOn_extDisk {ρ : ℝ} (f : DiskFun ρ) : ContinuousOn (extDisk ρ f) (closedBall (0 : ℂ) ρ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hr : (closedBall (0 : ℂ) ρ).domRestrict (extDisk ρ f) = f :=
    funext fun x => extDisk_apply_of_mem f x.2
  rw [hr]
  exact f.continuous

/-- **Countable dense family.** For a set `A` and a map `ψ` into a separable space, there is a countable `Φ ⊆ A` with
`ψ a ∈ closure (ψ '' Φ)` for every `a ∈ A`. Used to replace a family of test functions by a countable one. -/
theorem exists_countable_dense_family {α Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    (A : Set α) (ψ : α → Y) : ∃ Φ ⊆ A, Φ.Countable ∧ ∀ a ∈ A, ψ a ∈ closure (ψ '' Φ) := by
  obtain ⟨t, htc, hts, hsc⟩ := TopologicalSpace.exists_countable_dense_subset (ψ '' A)
  have : Countable t := htc.to_subtype
  have hy : ∀ y : t, ∃ a ∈ A, ψ a = y.1 := fun y => by
    obtain ⟨a, ha, h⟩ := hts y.2
    exact ⟨a, ha, h⟩
  choose g hgA hgψ using hy
  refine ⟨Set.range g, ?_, Set.countable_range g, fun a ha => ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hgA y
  · have himg : ψ '' Set.range g = t := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [hgψ z]
        exact z.2
      · intro hyt
        exact ⟨g ⟨y, hyt⟩, ⟨⟨y, hyt⟩, rfl⟩, hgψ ⟨y, hyt⟩⟩
    rw [himg]
    exact hsc ⟨a, ha, rfl⟩

/-- Evaluation at a point of `B̄_ρ` is measurable on `C(B̄_ρ, ℝ)`. -/
theorem measurable_diskFun_eval {ρ : ℝ} (x : closedBall (0 : ℂ) ρ) :
    Measurable fun f : DiskFun ρ => f x :=
  (continuous_eval_const x).measurable

/-- A bounded measurable function integrates measurably against the finite measures on `B̄_ρ`. -/
theorem measurable_integral_finMeasDisk {ρ : ℝ} {a : ℂ → ℝ} (ha : Measurable a) {C : ℝ}
    (hC : ∀ x, |a x| ≤ C) :
    Measurable fun ν : FinMeasDisk ρ => ∫ x, a x ∂(ν : Measure ℂ) := by
  have hfin : ∀ ν : FinMeasDisk ρ, Integrable a (ν : Measure ℂ) := fun ν => by
    have : IsFiniteMeasure (ν : Measure ℂ) := ν.2.1
    exact Integrable.of_bound ha.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hm1 : Measurable fun ν : FinMeasDisk ρ => ∫⁻ x, ENNReal.ofReal (a x) ∂(ν : Measure ℂ) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp ha)).comp measurable_subtype_coe
  have hm2 : Measurable fun ν : FinMeasDisk ρ => ∫⁻ x, ENNReal.ofReal (-a x) ∂(ν : Measure ℂ) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp ha.neg)).comp measurable_subtype_coe
  have hform : (fun ν : FinMeasDisk ρ => ∫ x, a x ∂(ν : Measure ℂ)) = fun ν : FinMeasDisk ρ =>
      (∫⁻ x, ENNReal.ofReal (a x) ∂(ν : Measure ℂ)).toReal -
        (∫⁻ x, ENNReal.ofReal (-a x) ∂(ν : Measure ℂ)).toReal := by
    funext ν
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfin ν)
  rw [hform]
  exact (ENNReal.measurable_toReal.comp hm1).sub (ENNReal.measurable_toReal.comp hm2)

end MatedCRT
