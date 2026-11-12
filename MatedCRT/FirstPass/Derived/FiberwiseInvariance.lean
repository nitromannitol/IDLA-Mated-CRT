import MatedCRT.Defs.Setting

/-!
# Fibrewise invariant maps preserve a product law

If `ν` is a measure on `C` and `Φ t : C → C` preserves `ν` for every parameter `t`, then the map
`(t, c) ↦ (t, Φ t c)` preserves the product measure `Q ⊗ ν`, for every measure `Q` on the parameter space and
every jointly measurable `Φ` (Fubini).  Consequently, if a random parameter `Z` is independent of a random
element `ξ` whose law `ν` is `Φ t`-invariant for every `t`, then `(Z, Φ Z ξ)` and `(Z, ξ)` have the same law.

This is the mechanism by which a random (but independent) scaling factor of a scale invariant random curve
leaves the joint law with the scaling factor unchanged.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory

variable {T C : Type*} [MeasurableSpace T] [MeasurableSpace C]

/-- **Fubini for fibrewise invariant maps.**  If every `Φ t` preserves `ν`, then
`(t, c) ↦ (t, Φ t c)` preserves `Q.prod ν`. -/
theorem map_prod_fiber_eq (Q : Measure T) (ν : Measure C) [SFinite Q] [SFinite ν]
    (Φ : T → C → C) (hΦ : Measurable fun p : T × C => Φ p.1 p.2)
    (hinv : ∀ t, ν.map (Φ t) = ν) :
    (Q.prod ν).map (fun p : T × C => (p.1, Φ p.1 p.2)) = Q.prod ν := by
  have hm : Measurable fun p : T × C => (p.1, Φ p.1 p.2) := measurable_fst.prodMk hΦ
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hm hS, Measure.prod_apply (hm hS), Measure.prod_apply hS]
  refine lintegral_congr fun t => ?_
  have hΦt : Measurable (Φ t) := hΦ.comp measurable_prodMk_left
  have hSt : MeasurableSet (Prod.mk t ⁻¹' S) := measurable_prodMk_left hS
  have h1 : Prod.mk t ⁻¹' ((fun p : T × C => (p.1, Φ p.1 p.2)) ⁻¹' S) = Φ t ⁻¹' (Prod.mk t ⁻¹' S) := rfl
  rw [h1, ← Measure.map_apply hΦt hSt, hinv t]

/-- **A random parameter independent of an invariant random element can be applied to it without changing
the joint law.**  If `Z` is independent of `ξ`, the law of `ξ` is preserved by `Φ t` for every `t`, and `Φ` is
jointly measurable, then `(Z, Φ Z ξ)` has the same law as `(Z, ξ)`. -/
theorem identDistrib_fiber_of_indepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → T} {ξ : Ω → C} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hind : IndepFun Z ξ P) (Φ : T → C → C) (hΦ : Measurable fun p : T × C => Φ p.1 p.2)
    (hinv : ∀ t, (P.map ξ).map (Φ t) = P.map ξ) :
    IdentDistrib (fun ω => (Z ω, Φ (Z ω) (ξ ω))) (fun ω => (Z ω, ξ ω)) P P := by
  have hm : Measurable fun p : T × C => (p.1, Φ p.1 p.2) := measurable_fst.prodMk hΦ
  have hlaw : P.map (fun ω => (Z ω, ξ ω)) = (P.map Z).prod (P.map ξ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hind
  have hcomp : (fun ω => (Z ω, Φ (Z ω) (ξ ω))) =
      (fun p : T × C => (p.1, Φ p.1 p.2)) ∘ fun ω => (Z ω, ξ ω) := rfl
  refine ⟨(hm.comp (hZ.prodMk hξ)).aemeasurable, (hZ.prodMk hξ).aemeasurable, ?_⟩
  rw [hcomp, ← Measure.map_map hm (hZ.prodMk hξ), hlaw, map_prod_fiber_eq _ _ Φ hΦ hinv]

end MatedCRT.FirstPass.Derived
