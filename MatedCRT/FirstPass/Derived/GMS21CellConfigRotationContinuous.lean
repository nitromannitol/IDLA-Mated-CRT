import MatedCRT.FirstPass.Derived.GMS21CellConfigRotation
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopologyBounds

/-!
# Rotations of cell configurations are continuous for GMS's metric `d^CC`

The image `eH` of a cell configuration under a linear isometry `e` of the plane
(`isometryCellConfig`, `GMS21CellConfigRotation.lean`) does not increase GMS's metric `d^CC`
(GMS21, (1.15)): a homeomorphism `f` admissible at radius `r` for `(H, H')` gives the admissible
homeomorphism `e ∘ f ∘ e⁻¹` for `(eH, eH')`, with the same displacement `sup |z − f(z)|` and the same
conductance distortion, because `e` fixes the balls `B_r(0)` and preserves distances.  Hence
`H ↦ eH` is continuous, so Borel measurable, on the space `GMSSpace` of cell configurations, and the
invariance of the law of the cell configuration under the quarter turn can be stated as
`μ.map (isometryGMS quarterTurn) = μ`.

* `dCC_isometryCellConfig_le`: `d^CC(eH, eH') ≤ d^CC(H, H')`;
* `continuous_isometryGMS`, `measurable_isometryGMS`;
* `covariance_eq_smul_one_of_map_quarterTurn`, `exists_isotropic_target_of_map_quarterTurn`:
  the isotropy statements of `GMS21CellConfigRotation.lean` with the invariance of the law in the
  form `μ.map (isometryGMS quarterTurn) = μ`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

open ReflectedGMS (Plane)
open ReflectedGMS.GMS ReflectedGMS.StatementIngredients
open ReflectedGMS.GMS.CellConfig (mapCell)

section Isometry

variable (e : Plane ≃ₗᵢ[ℝ] Plane)

/-- The conjugate `e ∘ f ∘ e⁻¹` of a homeomorphism `f` of the plane by a linear isometry `e`. -/
def isometryConj (f : Plane ≃ₜ Plane) : Plane ≃ₜ Plane :=
  e.toHomeomorph.symm.trans (f.trans e.toHomeomorph)

theorem coe_mapCell_symm_eq_preimage (K : Cell) :
    (mapCell e.toHomeomorph.symm K : Set Plane) = e ⁻¹' (K : Set Plane) := by
  rw [CellConfig.coe_mapCell_eq_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show e (e.symm y) ∈ (K : Set Plane)
    rw [e.apply_symm_apply]
    exact hy
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩

/-- A linear isometry fixes the balls `B_r(0)`, so a cell meets `B_r(0)` if and only if its image
does. -/
theorem inter_ball_nonempty_iff_isometry (K : Cell) (r : ℝ) :
    ((K : Set Plane) ∩ Metric.ball 0 r).Nonempty ↔
      ((mapCell e.toHomeomorph.symm K : Set Plane) ∩ Metric.ball 0 r).Nonempty := by
  rw [coe_mapCell_symm_eq_preimage]
  constructor
  · rintro ⟨z, hzK, hz⟩
    refine ⟨e.symm z, ?_, ?_⟩
    · show e (e.symm z) ∈ (K : Set Plane)
      rw [e.apply_symm_apply]
      exact hzK
    · rw [mem_ball_zero_iff, e.symm.norm_map]
      exact mem_ball_zero_iff.1 hz
  · rintro ⟨w, hwK, hw⟩
    refine ⟨e w, hwK, ?_⟩
    rw [mem_ball_zero_iff, e.norm_map]
    exact mem_ball_zero_iff.1 hw

variable {H : CellConfig}

theorem mem_restrict_isometryCellConfig {K : Cell} {r : ℝ} :
    K ∈ (isometryCellConfig e H).restrict (Metric.ball 0 r) ↔
      mapCell e.toHomeomorph.symm K ∈ H.restrict (Metric.ball 0 r) :=
  and_congr (mem_isometryCellConfig_cells e) (inter_ball_nonempty_iff_isometry e K r)

theorem mapCell_symm_mapCell_isometryConj (f : Plane ≃ₜ Plane) (K : Cell) :
    mapCell e.toHomeomorph.symm (mapCell (isometryConj e f) K) =
      mapCell f (mapCell e.toHomeomorph.symm K) := by
  refine TopologicalSpace.NonemptyCompacts.ext ?_
  simp only [CellConfig.coe_mapCell_eq_image, Set.image_image]
  congr 1
  funext x
  exact e.toHomeomorph.symm_apply_apply (f (e.toHomeomorph.symm x))

theorem mapCell_symm_mapCell_isometryConj_symm (f : Plane ≃ₜ Plane) (K : Cell) :
    mapCell e.toHomeomorph.symm (mapCell (isometryConj e f).symm K) =
      mapCell f.symm (mapCell e.toHomeomorph.symm K) := by
  refine TopologicalSpace.NonemptyCompacts.ext ?_
  simp only [CellConfig.coe_mapCell_eq_image, Set.image_image]
  congr 1
  funext x
  exact e.toHomeomorph.symm_apply_apply (f.symm (e.toHomeomorph.symm x))

/-- **Conjugation by `e` carries admissible homeomorphisms for `(H, H')` to admissible
homeomorphisms for `(eH, eH')`.** -/
theorem admissibleAt_isometryConj {A B : CellConfig} {r : ℝ} {f : Plane ≃ₜ Plane}
    (hf : CellConfig.AdmissibleAt A B r f) :
    CellConfig.AdmissibleAt (isometryCellConfig e A) (isometryCellConfig e B) r
      (isometryConj e f) := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨fun K hK => ?_, fun K hK => ?_, fun K hK K' hK' hKK' => ?_,
    fun K hK K' hK' hKK' => ?_⟩
  · rw [mem_restrict_isometryCellConfig, mapCell_symm_mapCell_isometryConj]
    exact h1 _ ((mem_restrict_isometryCellConfig e).1 hK)
  · rw [mem_restrict_isometryCellConfig, mapCell_symm_mapCell_isometryConj_symm]
    exact h2 _ ((mem_restrict_isometryCellConfig e).1 hK)
  · show 0 < B.c (mapCell e.toHomeomorph.symm (mapCell (isometryConj e f) K))
      (mapCell e.toHomeomorph.symm (mapCell (isometryConj e f) K'))
    rw [mapCell_symm_mapCell_isometryConj, mapCell_symm_mapCell_isometryConj]
    exact h3 _ ((mem_restrict_isometryCellConfig e).1 hK) _
      ((mem_restrict_isometryCellConfig e).1 hK') hKK'
  · show 0 < A.c (mapCell e.toHomeomorph.symm (mapCell (isometryConj e f).symm K))
      (mapCell e.toHomeomorph.symm (mapCell (isometryConj e f).symm K'))
    rw [mapCell_symm_mapCell_isometryConj_symm, mapCell_symm_mapCell_isometryConj_symm]
    exact h4 _ ((mem_restrict_isometryCellConfig e).1 hK) _
      ((mem_restrict_isometryCellConfig e).1 hK') hKK'

/-- **Conjugation by `e` does not increase the distortion** `sup_z |z − f(z)|` plus the conductance
discrepancy over adjacent cells meeting `B_r(0)`. -/
theorem distortion_isometryConj_le (A B : CellConfig) (r : ℝ) (f : Plane ≃ₜ Plane) :
    CellConfig.distortion (isometryCellConfig e A) (isometryCellConfig e B) r (isometryConj e f) ≤
      CellConfig.distortion A B r f := by
  unfold CellConfig.distortion
  refine add_le_add (iSup_le fun z => ?_)
    (iSup₂_le fun K hK => iSup₂_le fun K' hK' => iSup_le fun hKK' => ?_)
  · calc edist z (isometryConj e f z)
        = edist (e (e.symm z)) (isometryConj e f z) :=
          congrArg (fun y => edist y (isometryConj e f z)) (e.apply_symm_apply z).symm
      _ = edist (e.symm z) (f (e.symm z)) := e.isometry.edist_eq _ _
      _ ≤ ⨆ w : Plane, edist w (f w) := le_iSup (fun w => edist w (f w)) (e.symm z)
  · refine le_iSup₂_of_le (mapCell e.toHomeomorph.symm K)
      ((mem_restrict_isometryCellConfig e).1 hK)
      (le_iSup₂_of_le (mapCell e.toHomeomorph.symm K') ((mem_restrict_isometryCellConfig e).1 hK')
        (le_iSup_of_le hKK' (le_of_eq ?_)))
    show ENNReal.ofReal |A.c (mapCell e.toHomeomorph.symm K) (mapCell e.toHomeomorph.symm K') -
        B.c (mapCell e.toHomeomorph.symm (mapCell (isometryConj e f) K))
          (mapCell e.toHomeomorph.symm (mapCell (isometryConj e f) K'))| = _
    rw [mapCell_symm_mapCell_isometryConj, mapCell_symm_mapCell_isometryConj]

/-- **A linear isometry of the plane does not increase GMS's metric `d^CC`.** -/
theorem dCC_isometryCellConfig_le (A B : CellConfig) :
    CellConfig.dCC (isometryCellConfig e A) (isometryCellConfig e B) ≤ CellConfig.dCC A B := by
  unfold CellConfig.dCC
  refine lintegral_mono fun r => min_le_min le_rfl (le_iInf₂ fun f hf => ?_)
  exact (iInf₂_le _ (admissibleAt_isometryConj e hf)).trans (distortion_isometryConj_le e A B r f)

/-- **The image under a linear isometry is continuous on the space of cell configurations.** -/
theorem continuous_isometryGMS : Continuous (isometryGMS e) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨H, ε, -, rfl⟩
  refine isOpen_iff_forall_mem_open.2 fun H' hH' => ?_
  have hlt : CellConfig.dCC H.1 (isometryGMS e H').1 < ε := hH'
  refine ⟨{H'' | CellConfig.dCC H'.1 H''.1 < ε - CellConfig.dCC H.1 (isometryGMS e H').1},
    fun H'' hH'' => ?_,
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨H', _, tsub_pos_of_lt hlt, rfl⟩, ?_⟩
  · show CellConfig.dCC H.1 (isometryGMS e H'').1 < ε
    calc CellConfig.dCC H.1 (isometryGMS e H'').1
        ≤ CellConfig.dCC H.1 (isometryGMS e H').1 +
            CellConfig.dCC (isometryGMS e H').1 (isometryGMS e H'').1 :=
          ReflectedGMS.GeomTop.GMSTopology.dCC_triangle
            (ReflectedGMS.GeomTop.GMSTopology.finite_restrict_ball H.2)
            (ReflectedGMS.GeomTop.GMSTopology.finite_restrict_ball (isometryGMS e H').2) _
      _ ≤ CellConfig.dCC H.1 (isometryGMS e H').1 + CellConfig.dCC H'.1 H''.1 :=
          add_le_add le_rfl (dCC_isometryCellConfig_le e H'.1 H''.1)
      _ < CellConfig.dCC H.1 (isometryGMS e H').1 +
            (ε - CellConfig.dCC H.1 (isometryGMS e H').1) :=
          ENNReal.add_lt_add_left hlt.ne_top hH''
      _ = ε := add_tsub_cancel_of_le hlt.le
  · show CellConfig.dCC H'.1 H'.1 < _
    rw [CellConfig.dCC_self]
    exact tsub_pos_of_lt hlt

theorem measurable_isometryGMS : Measurable (isometryGMS e) :=
  (continuous_isometryGMS e).measurable

end Isometry

/-- **Isotropy of the limiting covariance (GMS21, Proposition 3.1, last assertion)**, with the
rotation invariance of the law in the form `μ.map (isometryGMS quarterTurn) = μ`. -/
theorem covariance_eq_smul_one_of_map_quarterTurn {μ : Measure GMSSpace}
    [IsProbabilityMeasure μ] (hrot : μ.map (isometryGMS quarterTurn) = μ)
    (hconn : ConnectedAlongLines μ) {target : AnisotropicBrownianTarget}
    (hconv : ∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
        ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) :
    ∃ c : ℝ≥0, 0 < c ∧ target.covariance = (c : ℝ) • 1 :=
  covariance_eq_smul_one_of_measurePreserving_quarterTurn
    ⟨measurable_isometryGMS quarterTurn, hrot⟩ hconn hconv

/-- **GMS Theorem 1.16 with an isotropic limit**, with the rotation invariance of the law in the
form `μ.map (isometryGMS quarterTurn) = μ`. -/
theorem exists_isotropic_target_of_map_quarterTurn (μ : Measure GMSSpace)
    [IsProbabilityMeasure μ] (hmt : MassTransport μ) (herg : ErgodicModuloScaling μ)
    (hfin : FiniteExpectation μ) (hconn : ConnectedAlongLines μ)
    (hrot : μ.map (isometryGMS quarterTurn) = μ) :
    ∃ target : AnisotropicBrownianTarget,
      (∃ c : ℝ≥0, 0 < c ∧ target.covariance = (c : ℝ) • 1) ∧
      (∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
        ∀ p : H.1.cells → Plane, (∀ K : H.1.cells, p K ∈ ((K : Cell) : Set Plane)) →
          ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
      (∀ᵐ H ∂μ, H.1.Recurrent) ∧
      (∀ᵐ H ∂μ, ∃ φ : H.1.cells → Plane, H.1.DiscreteHarmonic φ ∧ H.1.SublinearToCentroid φ) :=
  exists_isotropic_target_of_measurePreserving_quarterTurn μ hmt herg hfin hconn
    ⟨measurable_isometryGMS quarterTurn, hrot⟩

end MatedCRT
