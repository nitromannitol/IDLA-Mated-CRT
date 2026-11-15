import MatedCRT.FirstPass.Derived.AreaCellEnvironmentExteriorDerived
import MatedCRT.Proofs.Infra.RandomWalk

/-! # Paths from curve cells to the exterior of bounded sets -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- Every area cell can reach the exterior of a bounded set along positive
conductance edges, for any positive scaling of cell representatives. -/
theorem MatedCRTEnv.areaCell_exists_ambient_exterior_path
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (p : (areaCellConfig h hε (S.mult ε ω)).cells → Plane)
    (hp : ∀ C, p C ∈ (C.1 : Set Plane))
    {a : ℝ≥0} (ha : 0 < a) {U : Set Plane} (hU : Bornology.IsBounded U)
    (v : (areaCellConfig h hε (S.mult ε ω)).cells) :
    ∃ w, (a : ℝ) • p w ∉ U ∧
      Relation.ReflTransGen
        (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
          0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w := by
  let C := areaCellConfig h hε (S.mult ε ω)
  let e := euclideanCellEquiv h hε
  let : Countable C.cells := Countable.of_equiv ℤ e
  let e' : ℤ ≃ᵐ C.cells :=
    { toEquiv := e
      measurable_toFun := measurable_of_countable _
      measurable_invFun := measurable_of_countable _ }
  let E : (ℕ → ℤ) ≃ᵐ (ℕ → C.cells) :=
    MeasurableEquiv.piCongrRight (fun _ => e')
  have hwalk := S.ae_areaCell_adjacent_and_exterior_of_embedding ω h hε hlf H hH (e.symm v)
  change ∀ᵐ ξ ∂(srwLaw (S.mult ε ω) (e.symm v)).map E, _ at hwalk
  have hwalk' := E.measurableEmbedding.ae_map_iff.mp hwalk
  have hstart := srwLaw_ae_start (S.mult ε ω) (e.symm v)
  obtain ⟨ξ, hξ, hξ0⟩ := (hwalk'.and hstart).exists
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp (hξ.2 0 p hp a ha U hU)
  refine ⟨E ξ n, ?_, ?_⟩
  · simpa using hn
  · have hpath : ∀ n, Relation.ReflTransGen (fun x y : C.cells => 0 < C.c x y) (E ξ 0) (E ξ n) := by
      intro n
      induction n with
      | zero => exact Relation.ReflTransGen.refl
      | succ n ih => exact ih.tail (hξ.1 n)
    have hzero : E ξ 0 = v := by
      change e (ξ 0) = v
      rw [hξ0]
      exact e.apply_symm_apply v
    rw [← hzero]
    exact hpath n

end MatedCRT
end
