import MatedCRT.FirstPass.Derived.AreaCellFiniteNetworkPreparation

/-! # Sequences of finite area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3
open scoped NNReal

/-- Finite restrictions for a sequence of meshes can be chosen before specifying
any further data on the resulting networks. -/
theorem MatedCRTEnv.exists_areaCell_finite_network_sequence
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
       ∀ v : R n, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) v ∈ U →
        0 < (LatticeProb.finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
            (areaCellConfig h (hε n) (S.mult (ε n) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε n) (S.mult (ε n) ω) (S.mult_symm (ε n) ω))
          (areaCellConfig_conductance_nonneg h (hε n) (S.mult (ε n) ω))
          (areaCellConfig_conductance_self h (hε n) (S.mult (ε n) ω) (S.mult_self (ε n) ω))
          (R n)).totalConductance v) ∧
      (∀ n (v : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells),
        ∃ w, (a : ℝ) • areaCellRepresentative h (hε n) (S.mult (ε n) ω) w ∉ U ∧
          Relation.ReflTransGen
            (fun x y : (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells =>
              0 < (areaCellConfig h (hε n) (S.mult (ε n) ω)).c x y) v w) := by
  classical
  have hex := fun n => S.exists_areaCell_finite_network_for_bounded_domain ω h
    (hε n) (hlf n) (hlfg n) (H n) (hH n) ha hU (euclideanCellEquiv h (hε n) 0)
  choose R hR hs hm hr hp hx using hex
  exact ⟨R, hR, hs, hm, hr, hp, hx⟩

end MatedCRT
end
