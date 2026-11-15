import MatedCRT.FirstPass.Derived.AreaCellConfiguration
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import MatedCRT.Proofs.Infra.MatingOfTrees

/-! # Cell configurations of the mated-CRT map -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS MatedCRTHarmonic

/-- A matching cellular embedding gives the area-cell configuration of the mated-CRT map. -/
theorem MatedCRTEnv.areaCellConfig_isCellConfiguration
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ε : ℝ} (hε : 0 < ε)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω)) :
    (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration := by
  apply MatedCRT.areaCellConfig_isCellConfiguration h hε (S.mult ε ω) H hH
    (S.mult_symm ε ω) (S.mult_self ε ω)
  intro a b hp
  have hne : a ≠ b := by
    intro hab
    subst b
    rw [S.mult_self] at hp
    exact (lt_irrefl 0) hp
  rw [graph_adj_eq_srwGraph hlf hε.le]
  exact ⟨hne, Or.inl (Nat.ne_of_gt hp)⟩

end MatedCRT
