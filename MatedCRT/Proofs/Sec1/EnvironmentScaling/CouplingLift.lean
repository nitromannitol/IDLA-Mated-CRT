import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Independence.Basic

/-!
# Resampling on the original probability space

The measurable lifting lemma in `env-steps.tex`, lines 665–691.  Mathlib supplies
both the regular conditional distribution and the measurable inverse-CDF kernel
representation; no assumption on the sample space being standard Borel is used.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal ProbabilityTheory unitInterval

namespace MatedCRT.Sec1

/-- A jointly measurable realization of a Markov kernel gives its joint law. -/
theorem map_prod_kernel_realization {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    (ν : Measure Y) [IsProbabilityMeasure ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (f : Y → unitInterval → X) (hf : Measurable (uncurry f))
    (hkernel : ∀ y, volume.map (f y) = κ y) :
    (ν.prod volume).map (fun p => (p.1, f p.1 p.2)) = ν ⊗ₘ κ := by
  have hg : Measurable (fun p : Y × unitInterval => (p.1, f p.1 p.2)) :=
    measurable_fst.prodMk hf
  ext s hs
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs), Measure.compProd_apply hs]
  apply lintegral_congr
  intro y
  rw [← hkernel y, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hs)]
  rfl

/-- Given a uniform random variable independent of `Y`, lift `Y` on the same
sample space to a random element with law `μ` and prescribed projection. -/
theorem exists_same_space_lift {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    (π : X → Y) (hπ : Measurable π) (Ystar : Ω → Y) (hY : Measurable Ystar)
    (Z : Ω → unitInterval) (hZ : Measurable Z) (hZlaw : P.map Z = volume)
    (hindep : Ystar ⟂ᵢ[P] Z) (hYlaw : P.map Ystar = μ.map π) :
    ∃ Vstar : Ω → X, Measurable Vstar ∧ P.map Vstar = μ ∧
      ∀ᵐ ω ∂P, π (Vstar ω) = Ystar ω := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let κ : Kernel Y X := condDistrib id π μ
  obtain ⟨f, hf, hfκ⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let Vstar : Ω → X := fun ω => f (Ystar ω) (Z ω)
  have hV : Measurable Vstar := hf.comp (hY.prodMk hZ)
  have hjoint : P.map (fun ω => (Ystar ω, Vstar ω)) =
      μ.map (fun x => (π x, x)) := by
    calc
      P.map (fun ω => (Ystar ω, Vstar ω)) =
          (P.map (fun ω => (Ystar ω, Z ω))).map (fun p => (p.1, f p.1 p.2)) := by
            simpa only [Function.comp_def, Function.uncurry, Vstar] using
              (Measure.map_map (measurable_fst.prodMk hf) (hY.prodMk hZ)).symm
      _ = ((μ.map π).prod volume).map (fun p => (p.1, f p.1 p.2)) := by
        rw [hindep.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable, hYlaw, hZlaw]
      _ = (μ.map π) ⊗ₘ κ := map_prod_kernel_realization _ _ f hf hfκ
      _ = μ.map (fun x => (π x, x)) :=
        compProd_map_condDistrib hπ.aemeasurable measurable_id.aemeasurable
  refine ⟨Vstar, hV, ?_, ?_⟩
  · have h := congrArg (fun m : Measure (Y × X) => m.map Prod.snd) hjoint
    have hpair : Measurable (fun x : X => (π x, x)) := hπ.prodMk measurable_id
    rw [Measure.map_map measurable_snd (hY.prodMk hV),
      Measure.map_map measurable_snd hpair] at h
    change P.map Vstar = μ.map id at h
    simpa only [Measure.map_id] using h
  · have hpair : Measurable (fun x : X => (π x, x)) := hπ.prodMk measurable_id
    have heq : MeasurableSet {p : Y × X | π p.2 = p.1} :=
      measurableSet_eq_fun (hπ.comp measurable_snd) measurable_fst
    have hdiag : ∀ᵐ p ∂μ.map (fun x => (π x, x)), π p.2 = p.1 :=
      (ae_map_iff hpair.aemeasurable heq).2 (Filter.Eventually.of_forall fun _ => rfl)
    rw [← hjoint] at hdiag
    exact (ae_map_iff (hY.prodMk hV).aemeasurable heq).1 hdiag

end MatedCRT.Sec1
