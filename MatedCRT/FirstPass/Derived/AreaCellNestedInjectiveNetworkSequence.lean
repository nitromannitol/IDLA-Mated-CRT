import MatedCRT.FirstPass.Derived.AreaCellNestedNetworkSequence
import MatedCRT.FirstPass.Derived.AreaCellInjectivePositionSequence

/-! # Injective positions on nested area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open scoped NNReal Topology

/-- A single nested accessible network sequence carries injective positions in
scaled cells, asymptotically close to the representatives after an isometry. -/
theorem MatedCRTEnv.exists_areaCell_nested_injective_network_sequence
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlf : ∀ n, IsLocallyFiniteMult (S.mult (ε n) ω))
    (hlfg : ∀ n, MatedCRTHarmonic.MatedCRT.IsLocallyFinite (ε n) (S.bm ω))
    (H : ∀ n, CellularEmbedding
      (MatedCRTHarmonic.MatedCRT.graph (ε n) (S.bm ω) (hlfg n)) (0 : ℤ))
    (hH : ∀ n, (H n).cell = cell (ε n) (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {U W : Set Plane} (hUW : U ⊆ W)
    (hW : Bornology.IsBounded W)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0))
    {X : Type*} [MetricSpace X] (φ : Plane → X) (hφ : Isometry φ) :
    ∃ (R : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
      (hR : ∀ n, (R n).Finite) (q : ∀ n, R n → Plane),
      (∀ n, Function.Injective (fun v => φ (q n v))) ∧
      (∀ n (v : R n), ∃ x ∈ (v.1.1 : Set Plane), q n v = (a : ℝ) • x) ∧
      (∀ n (v : R n), dist (φ ((a : ℝ) •
        areaCellRepresentative h (hε n) (S.mult (ε n) ω) v)) (φ (q n v)) < t n) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop, ∀ v : R n,
        dist (φ ((a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v))
          (φ (q n v)) < δ) ∧
      (∀ n, euclideanCellEquiv h (hε n) 0 ∈ R n) ∧
      (∀ n v, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ W → v ∈ R n) ∧
      (∀ n v, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ W →
        ∀ w, w ∉ R n → (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w = 0) ∧
      (∀ n, letI := (hR n).fintype
       let A : Set (R n) := {v | (a : ℝ) •
         areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ U}
       let B : Set (R n) := {v | (a : ℝ) •
         areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ W}
       let N := finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
            (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε n) (S.mult (ε n) ω) (S.mult_symm (ε n) ω))
          (areaCellConfig_conductance_nonneg h (hε n) (S.mult (ε n) ω))
          (areaCellConfig_conductance_self h (hε n) (S.mult (ε n) ω) (S.mult_self (ε n) ω))
          (R n)
       A ⊆ B ∧ (∀ v ∈ B, 0 < N.totalConductance v) ∧
         N.BoundaryAccessible A ∧ N.BoundaryAccessible B) ∧
      (∀ n (v : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells),
        ∃ w, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) w ∉ W ∧
          Relation.ReflTransGen
            (fun x y : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
              0 < (areaCellConfig h (hε n) (S.mult (ε n) ω)).c x y) v w) := by
  classical
  obtain ⟨R, hR, hs, hm, hr, hp, hx⟩ :=
    S.exists_areaCell_nested_accessible_network_sequence ω h ε hε hlf hlfg H hH ha hUW hW
  obtain ⟨q, hqinj, hqcell, hqnear, hqevent⟩ :=
    exists_areaCell_injective_position_sequence h ε hε (fun n => S.mult (ε n) ω)
      ha R t ht ht0
  refine ⟨R, hR, q, ?_, hqcell, ?_, ?_, hs, hm, hr, hp, hx⟩
  · intro n
    exact hφ.injective.comp (hqinj n)
  · intro n v
    rw [hφ.dist_eq]
    exact hqnear n v
  · intro δ hδ
    filter_upwards [hqevent δ hδ] with n hn
    intro v
    rw [hφ.dist_eq]
    exact hn v

end MatedCRT
end
