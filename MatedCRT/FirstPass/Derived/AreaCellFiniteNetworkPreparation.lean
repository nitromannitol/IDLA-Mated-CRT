import MatedCRT.FirstPass.Derived.AreaCellScaledBoundedRegion
import MatedCRT.FirstPass.Derived.AreaCellAmbientExteriorPath
import MatedCRT.FirstPass.Derived.AreaCellFiniteStep

/-! # Finite area-cell networks for bounded domains -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3
open scoped NNReal

/-- A bounded domain admits a finite region containing its cells and the initial
cell, retaining their neighbors and providing positive restricted conductance
and ambient positive-conductance paths to the domain exterior. -/
theorem MatedCRTEnv.exists_areaCell_finite_network_for_bounded_domain
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {U : Set Plane} (hU : Bornology.IsBounded U)
    (start : (areaCellConfig h hε (S.mult ε ω)).cells) :
    ∃ (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hR : R.Finite),
      start ∈ R ∧
      (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U → v ∈ R) ∧
      (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U →
        ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
      (letI := hR.fintype
       ∀ v : R, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U →
        0 < (LatticeProb.finiteConductanceRestriction
          (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
            (areaCellConfig h hε (S.mult ε ω)).c v w)
          (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
          (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
          (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v) ∧
      (∀ v : (areaCellConfig h hε (S.mult ε ω)).cells,
        ∃ w, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) w ∉ U ∧
          Relation.ReflTransGen
            (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
              0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w) := by
  classical
  obtain ⟨R, hR, hs, hm, hr⟩ :=
    areaCellConfig_exists_finite_region_of_bounded_scaled_representatives h hε
      (S.mult ε ω) hlf H hH hU (ne_of_gt (by exact_mod_cast ha)) start
  refine ⟨R, hR, hs, hm, hr, ?_, ?_⟩
  · let : Fintype R := hR.fintype
    let A : Set R := {v | (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ U}
    have hret : ∀ v ∈ A, ∀ w, w ∉ R →
        (areaCellConfig h hε (S.mult ε ω)).c v w = 0 := by
      intro v hv w hw
      exact hr v hv w hw
    intro v hv
    exact areaCellConfig_finiteRestriction_total_pos S ω h hε hlf R A hret v hv
  · intro v
    exact S.areaCell_exists_ambient_exterior_path ω h hε hlfg H hH
      (areaCellRepresentative h hε (S.mult ε ω))
      (areaCellRepresentative_mem h hε (S.mult ε ω)) ha hU v

end MatedCRT
end
