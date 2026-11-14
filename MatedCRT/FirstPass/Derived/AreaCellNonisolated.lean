import MatedCRT.FirstPass.Derived.AreaCellGraph
import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Nonisolated area cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- Every area cell has an adjacent cell: consecutive vertices are joined by
an edge in the mated-CRT map. -/
theorem MatedCRTEnv.areaCellConfig_exists_adj {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (C : (areaCellConfig h hε (S.mult ε ω)).cells) :
    ∃ D : (areaCellConfig h hε (S.mult ε ω)).cells,
      (areaCellConfig h hε (S.mult ε ω)).Adj C D := by
  let e := euclideanCellEquiv h hε
  let k := e.symm C
  have hk : e k = C := e.apply_symm_apply C
  refine ⟨e (k + 1), ?_⟩
  rw [← hk]
  have hedge : (srwGraph (S.mult ε ω)).Adj k (k + 1) :=
    ⟨by omega, Or.inl (S.mult_succ_ne_zero hε.le ω k)⟩
  exact ((areaCellConfig_graph_adj_iff h hε _ (S.mult_symm ε ω) k (k + 1)).2 hedge).2.1

/-- Every area-cell holding time is positive for a cell configuration. -/
theorem MatedCRTEnv.areaCellConfig_holding_pos {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hc : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (C : (areaCellConfig h hε (S.mult ε ω)).cells) :
    0 < (areaCellConfig h hε (S.mult ε ω)).holding C :=
  LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hc
    (S.areaCellConfig_exists_adj ω h hε) C

end MatedCRT
end
