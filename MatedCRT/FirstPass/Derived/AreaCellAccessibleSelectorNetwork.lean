import MatedCRT.FirstPass.Derived.AreaCellAmbientSelectorNetwork
import LatticeProb.Walk.RestrictedBoundaryAccessibility

/-! # Accessible ambient area-cell networks for selector balls -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open scoped NNReal

/-- The ambient selector network has accessible boundary for its active set.
The same network retains active neighbors and uniformly contains selector-ball
preimages for all sufficiently close position maps. -/
theorem MatedCRTEnv.exists_areaCell_accessible_selector_network
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {W : Set Plane} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (centers : Finset Plane) (r : ℝ)
    (hballs : ∀ c ∈ centers, closedBall c r ⊆ W)
    (start : (areaCellConfig h hε (S.mult ε ω)).cells) :
    ∃ (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hR : R.Finite),
      start ∈ R ∧
      (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W → v ∈ R) ∧
      (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W →
        ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
      (letI := hR.fintype
       ∀ v : R, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W →
        0 < (LatticeProb.finiteConductanceRestriction
          (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
            (areaCellConfig h hε (S.mult ε ω)).c v w)
          (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
          (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
          (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v) ∧
      (letI := hR.fintype
       let A : Set R := {v | (a : ℝ) •
         areaCellRepresentative h hε (S.mult ε ω) v ∈ W}
       (finiteConductanceRestriction
          (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
            (areaCellConfig h hε (S.mult ε ω)).c v w)
          (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
          (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
          (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).BoundaryAccessible A) ∧
      (∀ v : (areaCellConfig h hε (S.mult ε ω)).cells,
        ∃ w, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) w ∉ W ∧
          Relation.ReflTransGen
            (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
              0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ q : R → Plane,
        (∀ v : R, dist ((a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v) (q v) ≤ δ) →
        ∀ c ∈ centers, q ⁻¹' ball c r ⊆
          (fun v : R => (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v) ⁻¹' W := by
  classical
  obtain ⟨R, hR, hs, hcontain, hretain, hpos, hpaths, δ, hδ, hselector⟩ :=
    S.exists_areaCell_ambient_selector_network ω h hε hlf hlfg H hH ha hW hWb centers r hballs start
  refine ⟨R, hR, hs, hcontain, hretain, hpos, ?_, hpaths, δ, hδ, hselector⟩
  let : Fintype R := hR.fintype
  apply finiteConductanceRestriction_boundaryAccessible_of_ambient_paths
    (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
    (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
    (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
    (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω))
    R _ {v | (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W}
  · intro v
    rfl
  · intro v hv w hw
    exact hretain v hv w hw
  · intro v hv
    exact hpaths v

end MatedCRT
end
