import MatedCRT.FirstPass.Derived.AreaCellUnitBallPreExitMesh

/-! # Geometry of finite area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS LatticeProb

/-- A finite restriction preserves adjacency, while the unit-ball diameter
bound supplies the buffer and local mesh for its area-cell representatives. -/
theorem areaCellConfig_finiteRestriction_geometry
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R]
    {a : ℝ} (ha : 0 < a) (Uc : Set ℂ) (r d : ℝ)
    (hU : Uc ⊆ ball 0 r) (hmargin : r + a * d ≤ a)
    (hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d) :
    (∀ K, areaCellRepresentative h hε (S.mult ε ω) K ∈ (K.1 : Set Plane)) ∧
    (∀ v w : R, 0 < (finiteConductanceRestriction
      (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
        (areaCellConfig h hε (S.mult ε ω)).c x y)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).a v w →
      (areaCellConfig h hε (S.mult ε ω)).Adj v.1 w.1) ∧
    (∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc),
      closedBall x (a * d) ⊆ ball 0 a) ∧
    (∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
      (∃ z ∈ (K.1 : Set Plane), a • z ∈ ball 0 a) →
        diam (K.1 : Set Plane) ≤ d) := by
  refine ⟨areaCellRepresentative_mem h hε (S.mult ε ω), ?_, ?_⟩
  · intro v w hvw
    exact hvw
  · exact areaCellConfig_unit_ball_buffer_and_scaled_local_mesh
      h hε (S.mult ε ω) ha Uc r d hU hmargin hdiam

end MatedCRT
end
