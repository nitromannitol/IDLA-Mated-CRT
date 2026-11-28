import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceSteps
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.Lateral

/-!
# The law of the lateral part of a whole-plane GFF

The lateral part `h - h_{|·|}(0)` of a whole-plane GFF `X` pairs with a test function `φ` as `X` pairs with the
mean-zero test function `φ - φ̄`, `φ̄` the rotation average of `φ` (`ae_lateralPart_apply`). The law of the process of
mean-zero pairings is the same for every whole-plane GFF (`GFFLaw.map_pairProc_eq`: the GFF is unique in law modulo
an additive constant), so the finite-dimensional laws of the pairings of the lateral parts of two whole-plane GFFs
agree, and so do the laws of the lateral parts (`map_lateralPart_eq`, `lateralPartLaw`).

Source: Duplantier–Miller–Sheffield (arXiv:1409.7055), Definition 4.10 and Lemmas 4.2–4.4 (the lateral part of the
whole-plane GFF); the argument is that of `ConeScaling.map_affineComp_lateralPart`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRT

open LQGMetric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.ConeScaling
  MatedCRTHarmonic.GMCFacts

/-- **The lateral parts of two whole-plane GFFs have the same law.** -/
theorem map_lateralPart_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X X₀ : Ω → DistC}
    (hX : LQGMetric.IsWholePlaneGFF X P) (hX₀ : LQGMetric.IsWholePlaneGFF X₀ P) :
    P.map (fun ω => CellScaling.lateralPart (X ω)) =
      P.map (fun ω => CellScaling.lateralPart (X₀ ω)) := by
  have := hX.gaussian.isProbabilityMeasure
  have hL : Measurable fun ω => CellScaling.lateralPart (X ω) :=
    measurable_lateralPart.comp hX.measurable
  have hL₀ : Measurable fun ω => CellScaling.lateralPart (X₀ ω) :=
    measurable_lateralPart.comp hX₀.measurable
  apply distC_measure_ext
  rw [Measure.map_map measurable_evDist hL, Measure.map_map measurable_evDist hL₀]
  have hfin : ∀ I : Finset TestC,
      (P.map (evDist ∘ fun ω => CellScaling.lateralPart (X ω))).map I.restrict =
        (P.map (evDist ∘ fun ω => CellScaling.lateralPart (X₀ ω))).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_evDist.comp hL),
      Measure.map_map (Finset.measurable_restrict I) (measurable_evDist.comp hL₀)]
    have hleft : (I.restrict ∘ evDist ∘ fun ω => CellScaling.lateralPart (X ω)) =ᵐ[P]
        fun ω (i : I) => X ω (latTest i.1).1 := by
      filter_upwards [ae_all_iff.2 fun i : I => ae_lateralPart_apply hX i.1] with ω hω
      funext i
      exact hω i
    have hright : (I.restrict ∘ evDist ∘ fun ω => CellScaling.lateralPart (X₀ ω)) =ᵐ[P]
        fun ω (i : I) => X₀ ω (latTest i.1).1 := by
      filter_upwards [ae_all_iff.2 fun i : I => ae_lateralPart_apply hX₀ i.1] with ω hω
      funext i
      exact hω i
    rw [Measure.map_congr hleft, Measure.map_congr hright]
    let F : (TestC0 → ℝ) → (I → ℝ) := fun q i => q (latTest i.1)
    have hF : Measurable F := measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hlaw := congrArg (Measure.map F) (GFFLaw.map_pairProc_eq hX hX₀)
    rw [Measure.map_map hF (GFFLaw.measurable_pairProc hX.measurable),
      Measure.map_map hF (GFFLaw.measurable_pairProc hX₀.measurable)] at hlaw
    exact hlaw
  exact IsProjectiveLimit.unique
    (P := fun I => (P.map (evDist ∘ fun ω => CellScaling.lateralPart (X₀ ω))).map I.restrict)
    hfin (fun _ => rfl)

/-- **`LateralPartLaw` holds**, with `Λ` the lateral part itself. -/
theorem lateralPartLaw : LateralPartLaw :=
  ⟨lateralPart, measurable_lateralPart, fun _ _ _ _ => ae_of_all _ fun _ => rfl,
    fun _ _ _ _ hX hX₀ => map_lateralPart_eq hX hX₀⟩

end MatedCRT
