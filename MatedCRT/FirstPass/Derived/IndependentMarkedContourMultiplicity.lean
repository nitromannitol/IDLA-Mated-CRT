import MatedCRT.FirstPass.Derived.MarkedContourMultiplicityObservable
import Mathlib.Probability.IdentDistribIndep

/-! # Multiplicity transfer with an independent phase -/

set_option autoImplicit false

open Function MeasureTheory ProbabilityTheory

namespace MatedCRT

/-- Equal contour and phase laws give the marked multiplicity transfer when
both samples have an independent phase. -/
theorem ae_cellMult_eq_shifted_bmEdgeCount_of_independent_marginals
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ((C(ℝ, ℝ × ℝ) × ℝ) × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) [IsFiniteMeasure P]
    (mark : Ω → C(ℝ, ℝ × ℝ) × ℝ) (g : Ω → ℝ → ℂ)
    (hmark : Measurable mark)
    (hcontour : P.map (fun ω => (mark ω).1) = μ.map (fun p => p.1.1))
    (hphase : P.map (fun ω => (mark ω).2) = μ.map (fun p => p.1.2))
    (hind : IndepFun (fun ω => (mark ω).1) (fun ω => (mark ω).2) P)
    (hsourceind : IndepFun (fun p => p.1.1) (fun p => p.1.2) μ)
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
  have hc : IdentDistrib (fun ω => (mark ω).1) (fun p => p.1.1) P μ :=
    ⟨(measurable_fst.comp hmark).aemeasurable,
      (measurable_fst.comp measurable_fst).aemeasurable, hcontour⟩
  have hp : IdentDistrib (fun ω => (mark ω).2) (fun p => p.1.2) P μ :=
    ⟨(measurable_snd.comp hmark).aemeasurable,
      (measurable_snd.comp measurable_fst).aemeasurable, hphase⟩
  have hlaw : P.map mark = μ.map Prod.fst := by
    simpa only [Prod.mk.eta] using (hc.prodMk hp hind hsourceind).map_eq
  exact ae_cellMult_eq_shifted_bmEdgeCount_of_ae_marked_marginal
    μ P mark g hmark hlaw ε R hsource htarget

end MatedCRT
