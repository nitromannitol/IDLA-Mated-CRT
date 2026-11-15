import MatedCRT.FirstPass.Derived.AreaCellCompactMeasurable
import MatedCRT.FirstPass.Derived.ValidAreaCellConfiguration
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EdgeMeasurable

/-! # Measurable enumeration of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- A realization of the area-cell configuration admits a measurable cell
    enumeration with almost-everywhere measurable indexed conductances. -/
theorem MatedCRTEnv.IsValid.areaCellConfig_measurable_enumeration
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (H : Ω → CellConfig)
    (hH : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      H ω = areaCellConfig h hε (S.mult ε ω)) :
    ∃ C : ℤ → Ω → Cell,
      (∀ k, Measurable (C k)) ∧
      (∀ᵐ ω ∂S.P, (H ω).IsCellConfiguration ∧
        (H ω).cells = Set.range (fun k => C k ω)) ∧
      ∀ j k, AEMeasurable (fun ω => (H ω).c (C j ω) (C k ω)) S.P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, η', _, hc, hη⟩ := hS.matingOfTrees
  let C : ℤ → Ω → Cell := fun k ω => euclideanCell ε (η' ω) (η' ω).continuous hε k
  refine ⟨C, ?_, ?_, ?_⟩
  · intro k
    exact (measurable_euclideanCell ε hε k).comp hc.measurable_curves.2.1
  · filter_upwards [hH, hη, hS.ae_areaCellConfig_isCellConfiguration S hε] with ω hHω hηω hvalid
    obtain ⟨h, hHω⟩ := hHω
    rw [hHω]
    obtain ⟨h', hconfig, _, _⟩ := hvalid
    refine ⟨hconfig, ?_⟩
    change Set.range (euclideanCell ε (S.η ω) h.1 hε) = Set.range (fun k => C k ω)
    congr 1
    funext k
    dsimp [C]
    apply TopologicalSpace.NonemptyCompacts.ext
    simp only [coe_euclideanCell, hηω.1]
  · intro j k
    have hm : AEMeasurable (fun ω => (S.mult ε ω j k : ℝ)) S.P :=
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (hS.measurable_mult ε j k)).aemeasurable
    apply hm.congr
    filter_upwards [hH, hη] with ω hHω hηω
    obtain ⟨h, hHω⟩ := hHω
    rw [hHω]
    have hC (k : ℤ) : C k ω = euclideanCellEquiv h hε k := by
      change euclideanCell ε (η' ω) (η' ω).continuous hε k =
        euclideanCell ε (S.η ω) h.1 hε k
      apply TopologicalSpace.NonemptyCompacts.ext
      simp only [coe_euclideanCell, hηω.1]
    rw [hC j, hC k, areaCellConfig_conductance]

end MatedCRT
