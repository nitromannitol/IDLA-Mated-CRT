import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig
import MatedCRT.FirstPass.Derived.AreaCellConfigurationNull

/-! # Geometry of time-shifted area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMS3

/-- A bounded set meets finitely many shifted cells of a matching embedding. -/
theorem finite_shiftedAreaCellConfig_cells_meeting {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ)))
    {U : Set ReflectedGMS.Plane} (hU : Bornology.IsBounded U) :
    {K : (shiftedAreaCellConfig h hε θ m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty}.Finite := by
  let f := Complex.orthonormalBasisOneI.repr
  have hbound : Bornology.IsBounded (f ⁻¹' U) :=
    f.isometry.antilipschitzWith.isBounded_preimage hU
  have hfin : {k : ℤ | (((shiftedEuclideanCellEquiv h hε θ k).1 :
      Set ReflectedGMS.Plane) ∩ U).Nonempty}.Finite := by
    apply (finite_verticesMeeting H hbound).subset
    intro k hk
    obtain ⟨z, hz, hzU⟩ := hk
    change z ∈ f '' cell ε (fun t => η (t + ε * θ)) k at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, by rw [hH]; exact hw, hzU⟩
  apply (hfin.image (shiftedEuclideanCellEquiv h hε θ)).subset
  intro K hK
  refine ⟨(shiftedEuclideanCellEquiv h hε θ).symm K, ?_,
    (shiftedEuclideanCellEquiv h hε θ).apply_symm_apply K⟩
  change (((shiftedEuclideanCellEquiv h hε θ
    ((shiftedEuclideanCellEquiv h hε θ).symm K)).1 : Set ReflectedGMS.Plane) ∩ U).Nonempty
  rw [(shiftedEuclideanCellEquiv h hε θ).apply_symm_apply]
  exact hK

/-- A matching embedding makes the shifted cell configuration locally finite. -/
theorem shiftedAreaCellConfig_locallyFinite {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ))) (z : ReflectedGMS.Plane) :
    ∃ U ∈ nhds z, ((shiftedAreaCellConfig h hε θ m).restrict U).Finite := by
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
  have hf := finite_shiftedAreaCellConfig_cells_meeting h hε θ m H hH
    (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball z (1 : ℝ)))
  convert hf.image (fun K : (shiftedAreaCellConfig h hε θ m).cells => K.1) using 1
  ext K
  simp only [CellConfig.restrict, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hK, hmeet⟩
    exact ⟨⟨K, hK⟩, hmeet, rfl⟩
  · rintro ⟨K', hmeet, rfl⟩
    exact ⟨K'.2, hmeet⟩

/-- Every shifted cell of a matching embedding is connected. -/
theorem shiftedAreaCellConfig_isConnected {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ))) :
    ∀ K ∈ (shiftedAreaCellConfig h hε θ m).cells,
      IsConnected (K : Set ReflectedGMS.Plane) := by
  rintro K ⟨k, rfl⟩
  rw [coe_euclideanCell, ← hH]
  exact (H.isConnected_cell k).image _ Complex.orthonormalBasisOneI.repr.continuous.continuousOn

/-- Every shifted cell of a matching embedding has nonempty interior. -/
theorem shiftedAreaCellConfig_interior_nonempty {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ))) :
    ∀ K ∈ (shiftedAreaCellConfig h hε θ m).cells,
      (interior (K : Set ReflectedGMS.Plane)).Nonempty := by
  rintro K ⟨k, rfl⟩
  rw [coe_euclideanCell, ← hH]
  change (interior (Complex.orthonormalBasisOneI.repr.toHomeomorph '' H.cell k)).Nonempty
  rw [← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_interior]
  exact (H.interior_cell_nonempty k).image _

/-- The shifted cells of a matching embedding cover the plane. -/
theorem shiftedAreaCellConfig_iUnion_eq_univ {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ))) :
    (⋃ K ∈ (shiftedAreaCellConfig h hε θ m).cells, (K : Set ReflectedGMS.Plane)) = univ := by
  apply eq_univ_iff_forall.mpr
  intro z
  have hz : Complex.orthonormalBasisOneI.repr.symm z ∈ ⋃ k, H.cell k := by
    rw [H.iUnion_cell]
    exact mem_univ _
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  refine mem_iUnion.mpr ⟨shiftedEuclideanCellEquiv h hε θ k,
    mem_iUnion.mpr ⟨(shiftedEuclideanCellEquiv h hε θ k).2, ?_⟩⟩
  change z ∈ (euclideanCell ε (fun t => η (t + ε * θ))
    (h.1.comp (continuous_id.add continuous_const)) hε k :
    Set ReflectedGMS.Plane)
  rw [coe_euclideanCell, ← hH]
  exact ⟨Complex.orthonormalBasisOneI.repr.symm z, hk,
    Complex.orthonormalBasisOneI.repr.apply_symm_apply z⟩

/-- Distinct shifted cells of a matching embedding have null intersection. -/
theorem shiftedAreaCellConfig_volume_inter {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε (fun t => η (t + ε * θ))) :
    ∀ K ∈ (shiftedAreaCellConfig h hε θ m).cells,
      ∀ K' ∈ (shiftedAreaCellConfig h hε θ m).cells,
        K ≠ K' → volume ((K : Set ReflectedGMS.Plane) ∩ K') = 0 := by
  rintro K ⟨j, rfl⟩ K' ⟨k, rfl⟩ hne
  have hjk : j ≠ k := by
    intro heq
    exact hne (congrArg (euclideanCell ε (fun t => η (t + ε * θ))
      (h.1.comp (continuous_id.add continuous_const)) hε) heq)
  rw [coe_euclideanCell, coe_euclideanCell, ← hH,
    ← Set.image_inter Complex.orthonormalBasisOneI.repr.injective]
  change volume (Complex.orthonormalBasisOneI.repr.toLinearEquiv.toEquiv ''
    (H.cell j ∩ H.cell k)) = 0
  rw [Equiv.image_eq_preimage_symm]
  change volume (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    (H.cell j ∩ H.cell k)) = 0
  rw [Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
    ((H.isCompact_cell j).isClosed.measurableSet.inter
      (H.isCompact_cell k).isClosed.measurableSet).nullMeasurableSet]
  exact H.volume_inter_cell j k hjk

end MatedCRT
