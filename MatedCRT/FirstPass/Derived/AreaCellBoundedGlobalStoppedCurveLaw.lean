import MatedCRT.FirstPass.Derived.AreaCellFiniteNetworkPreparation
import MatedCRT.FirstPass.Derived.AreaCellGlobalStoppedCurveLaw

/-! # Global stopped curve laws on finite area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3
open ProbabilityTheory MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped NNReal

/-- A bounded domain has a finite retained-neighbor network whose stopped curve
law agrees with the integer walk stopped on the global active set. -/
theorem MatedCRTEnv.exists_areaCell_finite_global_stopped_curveLaw
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {U : Set Plane} (hU : Bornology.IsBounded U)
    (start : (areaCellConfig h hε (S.mult ε ω)).cells)
    {d : ℕ} (pos : (areaCellConfig h hε (S.mult ε ω)).cells → Euc d) :
    ∃ (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hR : R.Finite)
      (hs : start ∈ R),
      (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U → v ∈ R) ∧
      (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U →
        ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
      (∀ v : (areaCellConfig h hε (S.mult ε ω)).cells,
        ∃ w, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) w ∉ U ∧
          Relation.ReflTransGen
            (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
              0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w) ∧
      (letI := hR.fintype
       ∃ hactive : ∀ v : R, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U →
        0 < (LatticeProb.finiteConductanceRestriction
          (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
            (areaCellConfig h hε (S.mult ε ω)).c v w)
          (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
          (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
          (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v,
       let B := {v : (areaCellConfig h hε (S.mult ε ω)).cells |
         (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U}
       let A : Set R := {v | (v : (areaCellConfig h hε (S.mult ε ω)).cells) ∈ B}
       let N := LatticeProb.finiteConductanceRestriction
          (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
            (areaCellConfig h hε (S.mult ε ω)).c v w)
          (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
          (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
          (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
       ((N.trajectoryLaw A hactive ⟨start, hs⟩).map (fun p n =>
          (p n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
            (stoppedPolygonalCurve pos B) =
         (srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm start)).map
           (stoppedPolygonalCurve (pos ∘ euclideanCellEquiv h hε)
             ((euclideanCellEquiv h hε) ⁻¹' B))) := by
  classical
  obtain ⟨R, hR, hs, hcontain, hretain, hactive, hpaths⟩ :=
    S.exists_areaCell_finite_network_for_bounded_domain ω h hε hlf hlfg H hH ha hU start
  refine ⟨R, hR, hs, hcontain, hretain, hpaths, ?_⟩
  let : Fintype R := hR.fintype
  refine ⟨hactive, ?_⟩
  exact areaCellConfig_global_stopped_curveLaw S ω h hε hlf R _ hcontain
    (fun v hv w hw => hretain v hv w hw) hactive ⟨start, hs⟩ pos

end MatedCRT
end
