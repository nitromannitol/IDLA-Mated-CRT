import MatedCRT.FirstPass.Derived.AreaCellAccessibleSelectorNetwork
import MatedCRT.FirstPass.Derived.AreaCellScaledInjectivePosition

/-! # Injective positions on accessible area-cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 LatticeProb
open scoped NNReal

/-- One finite ambient network has accessible boundary and injective positions
in the scaled cells, arbitrarily close to the endpoint positions and with all
specified selector-ball preimages contained in its active set. -/
theorem MatedCRTEnv.exists_areaCell_injective_accessible_selector_network
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
    (start : (areaCellConfig h hε (S.mult ε ω)).cells)
    {t : ℝ} (ht : 0 < t) :
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
      ∃ q : R → Plane, Function.Injective q ∧
        (∀ v : R, ∃ x ∈ (v.1.1 : Set Plane), q v = (a : ℝ) • x) ∧
        (∀ v : R, dist ((a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v) (q v) < t) ∧
        ∀ c ∈ centers, q ⁻¹' ball c r ⊆
          (fun v : R => (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v) ⁻¹' W := by
  classical
  obtain ⟨R, hR, hs, hcontain, hretain, hpos, haccess, hpaths, δ, hδ, hselector⟩ :=
    S.exists_areaCell_accessible_selector_network ω h hε hlf hlfg H hH ha hW hWb centers r hballs start
  obtain ⟨q, hqinj, hqcell, hqnear⟩ :=
    exists_areaCell_scaled_injective_position h hε (S.mult ε ω) ha (lt_min hδ ht) R
  refine ⟨R, hR, hs, hcontain, hretain, hpos, haccess, hpaths, q, hqinj, hqcell, ?_, ?_⟩
  · intro v
    exact (hqnear v).trans_le (min_le_right δ t)
  · apply hselector q
    intro v
    exact (hqnear v).le.trans (min_le_left δ t)

end MatedCRT
end
