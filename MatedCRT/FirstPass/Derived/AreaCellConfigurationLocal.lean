import MatedCRT.FirstPass.Derived.AreaCellLocalFiniteness

/-! # Local finiteness of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic

/-- A matching cellular embedding gives local finiteness of the unlabelled
area-cell configuration. -/
theorem areaCellConfig_locallyFinite {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) (z : ReflectedGMS.Plane) :
    ∃ U ∈ 𝓝 z, ((areaCellConfig h hε m).restrict U).Finite := by
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
  have hf := finite_areaCellConfig_cells_meeting h hε m H hH
    (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball z (1 : ℝ)))
  convert hf.image (fun K : (areaCellConfig h hε m).cells => K.1) using 1
  ext K
  simp only [CellConfig.restrict, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hK, hmeet⟩
    exact ⟨⟨K, hK⟩, hmeet, rfl⟩
  · rintro ⟨K', hmeet, rfl⟩
    exact ⟨K'.2, hmeet⟩

end MatedCRT
