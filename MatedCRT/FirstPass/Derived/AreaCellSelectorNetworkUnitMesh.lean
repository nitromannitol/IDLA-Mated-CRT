import MatedCRT.FirstPass.Derived.AreaCellInjectiveAccessibleSelectorNetwork
import MatedCRT.FirstPass.Derived.AreaCellUnitBallPreExitMesh

/-! # Selector networks with a target pre-exit mesh bound -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open scoped NNReal

/-- A finite ambient selector network has positive conductances on both its
selector balls and the target, and its ambient walk obeys the unit-ball mesh
bound before exiting the target. -/
theorem MatedCRTEnv.exists_areaCell_selector_network_unit_mesh
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hc : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {W : Set Plane} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (centers : Finset Plane) (s : ℝ)
    (hballs : ∀ c ∈ centers, closedBall c s ⊆ W)
    (start : (areaCellConfig h hε (S.mult ε ω)).cells) {t : ℝ} (ht : 0 < t)
    (Uc : Set ℂ) (r d : ℝ) (hd : 0 ≤ d)
    (hUW : Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc ⊆ W)
    (hU : Uc ⊆ ball 0 r) (hmargin : r + (a : ℝ) * d ≤ a)
    (hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d) :
    ∃ (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hR : R.Finite),
    start ∈ R ∧
    (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W → v ∈ R) ∧
    (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W →
      ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
    (∀ v : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ w, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) w ∉
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ∧
        Relation.ReflTransGen
          (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
            0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w) ∧
    (letI := hR.fintype
     let N := finiteConductanceRestriction
       (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
         (areaCellConfig h hε (S.mult ε ω)).c v w)
       (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
       (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
       (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
     let p : R → Plane := fun v => (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v
     let A := p ⁻¹' W
     ∃ (hA : ∀ v ∈ A, 0 < N.totalConductance v) (q : R → Plane),
       N.BoundaryAccessible A ∧ Function.Injective q ∧
       (∀ v, ∃ x ∈ (v.1.1 : Set Plane), q v = (a : ℝ) • x) ∧
       (∀ v, dist (p v) (q v) < t) ∧
       (∀ j : centers, q ⁻¹' ball j.val s ⊆ A) ∧
       (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ⊆ A) ∧
       (∀ j : centers, ∀ v ∈ q ⁻¹' ball j.val s, 0 < N.totalConductance v) ∧
       (∀ v ∈ p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc),
         0 < N.totalConductance v) ∧
       (∀ [MeasurableSpace R] [MeasurableSingletonClass R] (v : R),
         ∀ᵐ ξ ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
           (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime
             (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ξ →
           dist (p (ξ (j + 1))) (p (ξ j)) ≤ 2 * ((a : ℝ) * d))) := by
  classical
  obtain ⟨R, hR, hs, hcontain, hretain, hpos, haccess, hpaths,
    q, hqinj, hqcell, hqnear, hselector⟩ :=
    S.exists_areaCell_injective_accessible_selector_network ω h hε hlf hlfg H hH
      ha hW hWb centers s hballs start ht
  refine ⟨R, hR, hs, hcontain, hretain, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw, hpath⟩ := hpaths v
    exact ⟨w, fun hwU => hw (hUW hwU), hpath⟩
  let : Fintype R := hR.fintype
  refine ⟨hpos, q, haccess, hqinj, hqcell, hqnear, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hselector j.val j.property
  · exact preimage_mono hUW
  · intro j v hv
    exact hpos v (hselector j.val j.property hv)
  · intro v hv
    exact hpos v (hUW hv)
  · intro _ _ v
    exact areaCellConfig_trajectoryLaw_ae_preExit_step_le_unit_ball_mesh
      S ω h hε hc R _ hpos v (by exact_mod_cast ha) Uc r d hd hU hmargin hdiam

end MatedCRT
end
