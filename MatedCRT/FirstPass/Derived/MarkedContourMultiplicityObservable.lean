import MatedCRT.FirstPass.Derived.MarkedContourMultiplicityTransfer
import MatedCRT.FirstPass.Derived.JointShiftedMeshMultiplicity

/-! # Measurability of multiplicities from a marked contour law -/

set_option autoImplicit false

open Function MeasureTheory Set

namespace MatedCRT

/-- Transfer the full multiplicity array from an almost-sure source property. -/
theorem ae_cellMult_eq_shifted_bmEdgeCount_of_ae_marked_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ((C(ℝ, ℝ × ℝ) × ℝ) × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (mark : Ω → C(ℝ, ℝ × ℝ) × ℝ) (g : Ω → ℝ → ℂ)
    (hmark : Measurable mark) (hlaw : P.map mark = μ.map Prod.fst)
    (ε : ℝ) (R : C(ℝ, ℝ × ℝ) × ℝ → ℝ → ℝ → Prop)
    (hsource : ∀ᵐ p ∂μ, IsProperMap p.2 ∧ Surjective p.2 ∧
      (∀ s t, p.2 s = p.2 t ↔ R p.1 s t) ∧
      ∀ j k, cellMult ε p.2 j k =
        bmEdgeCount ε (fun t => (p.1.1 (t + p.1.2)).1)
          (fun t => (p.1.1 (t + p.1.2)).2) j k)
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, g ω s = g ω t ↔ R (mark ω) s t) :
    ∀ᵐ ω ∂P, cellMult ε (g ω) =
      bmEdgeCount ε (fun t => ((mark ω).1 (t + (mark ω).2)).1)
        (fun t => ((mark ω).1 (t + (mark ω).2)).2) := by
  let A := {p : (C(ℝ, ℝ × ℝ) × ℝ) × C(ℝ, ℂ) |
    IsProperMap p.2 ∧ Surjective p.2 ∧
      (∀ s t, p.2 s = p.2 t ↔ R p.1 s t) ∧
      ∀ j k, cellMult ε p.2 j k =
        bmEdgeCount ε (fun t => (p.1.1 (t + p.1.2)).1)
          (fun t => (p.1.1 (t + p.1.2)).2) j k}
  have hA : NullMeasurableSet A μ := by
    simpa only [compl_compl] using
      (NullMeasurableSet.of_null (show μ Aᶜ = 0 from ae_iff.1 hsource)).compl
  exact ae_cellMult_eq_shifted_bmEdgeCount_of_marked_marginal μ P mark g hmark hlaw ε R
    hA hsource (fun _ hp => hp) htarget

/-- Under the same source and fiber assumptions, the target multiplicity array
is almost everywhere measurable for a positive mesh. -/
theorem aemeasurable_cellMult_of_ae_marked_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ((C(ℝ, ℝ × ℝ) × ℝ) × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (mark : Ω → C(ℝ, ℝ × ℝ) × ℝ) (g : Ω → ℝ → ℂ)
    (hmark : Measurable mark) (hlaw : P.map mark = μ.map Prod.fst)
    (ε : ℝ) (hε : 0 < ε) (R : C(ℝ, ℝ × ℝ) × ℝ → ℝ → ℝ → Prop)
    (hsource : ∀ᵐ p ∂μ, IsProperMap p.2 ∧ Surjective p.2 ∧
      (∀ s t, p.2 s = p.2 t ↔ R p.1 s t) ∧
      ∀ j k, cellMult ε p.2 j k =
        bmEdgeCount ε (fun t => (p.1.1 (t + p.1.2)).1)
          (fun t => (p.1.1 (t + p.1.2)).2) j k)
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, g ω s = g ω t ↔ R (mark ω) s t) :
    AEMeasurable (fun ω => cellMult ε (g ω)) P := by
  have harg : Measurable (fun ω => ((mark ω).1, (⟨ε, hε⟩ : {e : ℝ // 0 < e}),
      (mark ω).2 / ε)) :=
    (measurable_fst.comp hmark).prodMk
      (measurable_const.prodMk ((measurable_snd.comp hmark).div_const ε))
  have hm := measurable_bmEdgeCount_shiftedMesh_array.comp harg
  have he : ε ≠ 0 := ne_of_gt hε
  change Measurable (fun ω => bmEdgeCount ε
    (fun t => ((mark ω).1 (t + ε * ((mark ω).2 / ε))).1)
    (fun t => ((mark ω).1 (t + ε * ((mark ω).2 / ε))).2)) at hm
  have hcancel (x : ℝ) : ε * (x / ε) = x := by
    field_simp
  simp only [hcancel] at hm
  apply hm.aemeasurable.congr
  filter_upwards [ae_cellMult_eq_shifted_bmEdgeCount_of_ae_marked_marginal μ P mark g hmark hlaw ε R
    hsource htarget] with ω hω
  exact hω.symm

end MatedCRT
