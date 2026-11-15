import MatedCRT.FirstPass.Derived.AreaCellFiniteNetworkSequence
import LatticeProb.Walk.RestrictedBoundaryAccessibility

/-! # Boundary accessibility along area-cell network sequences -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open scoped NNReal

/-- A sequence of finite restrictions simultaneously retains all active
neighbors and has accessible boundary for each restricted active set. -/
theorem MatedCRTEnv.exists_areaCell_accessible_network_sequence
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlf : ∀ n, IsLocallyFiniteMult (S.mult (ε n) ω))
    (hlfg : ∀ n, MatedCRTHarmonic.MatedCRT.IsLocallyFinite (ε n) (S.bm ω))
    (H : ∀ n, CellularEmbedding
      (MatedCRTHarmonic.MatedCRT.graph (ε n) (S.bm ω) (hlfg n)) (0 : ℤ))
    (hH : ∀ n, (H n).cell = cell (ε n) (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {U : Set Plane} (hU : Bornology.IsBounded U) :
    ∃ (R : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
      (hR : ∀ n, (R n).Finite),
      (∀ n, euclideanCellEquiv h (hε n) 0 ∈ R n) ∧
      (∀ n v, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ U → v ∈ R n) ∧
      (∀ n v, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ U →
        ∀ w, w ∉ R n → (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w = 0) ∧
      (∀ n, letI := (hR n).fintype
       let A : Set (R n) := {v | (a : ℝ) •
         areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ U}
       let N := finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
            (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε n) (S.mult (ε n) ω) (S.mult_symm (ε n) ω))
          (areaCellConfig_conductance_nonneg h (hε n) (S.mult (ε n) ω))
          (areaCellConfig_conductance_self h (hε n) (S.mult (ε n) ω) (S.mult_self (ε n) ω))
          (R n)
       (∀ v ∈ A, 0 < N.totalConductance v) ∧ N.BoundaryAccessible A) ∧
      (∀ n (v : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells),
        ∃ w, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) w ∉ U ∧
          Relation.ReflTransGen
            (fun x y : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
              0 < (areaCellConfig h (hε n) (S.mult (ε n) ω)).c x y) v w) := by
  classical
  obtain ⟨R, hR, hs, hm, hr, hp, hx⟩ :=
    S.exists_areaCell_finite_network_sequence ω h ε hε hlf hlfg H hH ha hU
  refine ⟨R, hR, hs, hm, hr, ?_, hx⟩
  intro n
  let : Fintype (R n) := (hR n).fintype
  constructor
  · exact hp n
  · apply finiteConductanceRestriction_boundaryAccessible_of_ambient_paths
      (fun v w : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
        (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w)
      (areaCellConfig_conductance_symm h (hε n) (S.mult (ε n) ω) (S.mult_symm (ε n) ω))
      (areaCellConfig_conductance_nonneg h (hε n) (S.mult (ε n) ω))
      (areaCellConfig_conductance_self h (hε n) (S.mult (ε n) ω) (S.mult_self (ε n) ω))
      (R n) _ {v | (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ U}
    · intro v
      rfl
    · intro v hv w hw
      exact hr n v hv w hw
    · intro v hv
      exact hx n v

end MatedCRT
end
