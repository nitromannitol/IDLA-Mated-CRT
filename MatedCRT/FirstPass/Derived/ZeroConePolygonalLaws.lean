import MatedCRT.FirstPass.Derived.ZeroConePolygonalConfig
import MatedCRT.FirstPass.Derived.ZeroConePolygonalDataAe
import MatedCRT.FirstPass.Derived.GMS21ZeroConeQuenchedPolygonal
import MatedCRT.FirstPass.Derived.ZeroConeFiniteExpectation

/-!
# Connectedness along lines, finite expectation and the carrying clause for the zero-cone polygonal configuration

For the mating-of-trees coupling `D`, `γ ∈ (0, 2)`, a measurable version `G` of the boundary-length pair of the
zero-cone curve and a default point `H₀` of the GMS space, let
`Φ_G p := polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)` be the polygonal configuration of the unit-mesh datum
of the curve `t ↦ η₀(t + θ)` and the contour edge counts of `t ↦ G(t + θ)`, `p = (ω, θ)`. Three clauses of the
polygonal configuration in the proof of Lemma 3.5 of Gwynne–Miller–Sheffield (arXiv:1705.11161) hold for every
`H₀`:

* `ae_carriesUnitMeshWalk_polygonalConfig`: almost surely under `P ⊗ Unif[0, 1]` the cells of `Φ_G p` carry the
  walk of the datum (the polygonal cells retain the conductances and contain the vertices). The datum is valid
  almost surely (`ae_unitMeshValid_phaseShifted`).
* `connectedAlongLines_polygonalConfig`: the law of `Φ_G` is connected along lines (hypothesis 3 of
  Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16), given that `Φ_G` is almost everywhere measurable for
  the Borel σ-algebra of the metric `d^CC` (the premise `hΦ`): for a valid datum the polygonal configuration is
  connected along lines (`PolygonalInput.lineConnected`).
* `finiteExpectation_polygonalConfig`: the law of `Φ_G` satisfies the finite-expectation hypothesis (1.5) of
  arXiv:1807.07515, under the same premise `hΦ`, with the root cell `rootCell` (a cell containing `0` with the
  least `diam²/Area · π`). Almost surely the old cell `K_0 = η₀([θ - 1, θ])` contains `0 = η₀(0)`, the root
  cell has `diam²/Area · π ≤ 8 e_0` and `π* ≤ π` (`rootDensity_polygonalConfig_le`), and
  `e_0 ≤ 3 diamAreaSup(η₀) (degInner η₀ + degOuter η₀)` (`ofReal_weight_zero_le`: the counts are at most `2`
  and positive only between meeting cells); the moment bounds of arXiv:1705.11161, Propositions 4.4 and 4.6
  (`ZeroConeRoot.lintegral_diamAreaSup_mul_deg_lt_top`), give the finite expectation.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open MatedCRT MatedCRT.GMS310Transfer MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
  MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

/-- The old cells of a datum whose curve is `c` read on the lattice `ℤ + θ` are the arcs
`c([k - 1 + θ, k + θ])`. -/
theorem unitCell_phaseShifted (c : C(ℝ, ℂ)) (θ : ℝ) (m : ℤ → ℤ → ℕ) (k : ℤ) :
    unitCell (phaseShiftedCurve 1 θ c, m) k =
      Complex.orthonormalBasisOneI.repr '' (c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1)) := by
  rw [← cell_one_timeShift]
  rfl

/-- **The weight of the old cell through the origin** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of
Proposition 3.1). Let `c` be a curve with `c 0 = 0` and `diam c([-1, 1]) > 0`, `θ ∈ [0, 1]`, and let `w` be a valid
datum whose old cells are the arcs `c([k - 1 + θ, k + θ])` and whose counts are at most `2`. Then
`e_0 ≤ diamAreaSup c · 3 (degInner c + degOuter c)`: `diam(K_0)²/|K_0| ≤ diamAreaSup c`, each positive count
`m` has `m + m⁻¹ ≤ 3`, and the labels with a positive count meet `K_0` (`card_le_degInner_add_degOuter`). -/
theorem ofReal_weight_zero_le {c : C(ℝ, ℂ)} (hc0 : c 0 = 0) (hD : 0 < Metric.diam (c '' Icc (-1) 1))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (h : UnitMeshValid w)
    (hcell : ∀ k : ℤ, unitCell w k =
      Complex.orthonormalBasisOneI.repr '' (c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1)))
    (hm2 : ∀ i j, w.2 i j ≤ 2) :
    ENNReal.ofReal (weight (unitCell w) w.2 0) ≤
      diamAreaSup c * (3 * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞))) := by
  have e1 : ((0 : ℤ) : ℝ) - 1 + θ = θ - 1 := by rw [Int.cast_zero]; ring
  have e2 : ((0 : ℤ) : ℝ) - 1 + θ + 1 = θ := by rw [Int.cast_zero]; ring
  have hK0 : unitCell w 0 = Complex.orthonormalBasisOneI.repr '' (c '' Icc (θ - 1) θ) := by
    rw [hcell 0, e2, e1]
  have hCc : IsCompact (c '' Icc (θ - 1) θ) := isCompact_Icc.image c.continuous
  have hd : Metric.diam (unitCell w 0) = Metric.diam (c '' Icc (θ - 1) θ) := by
    rw [hK0]
    exact Complex.orthonormalBasisOneI.repr.isometry.diam_image _
  have hv : volume (unitCell w 0) = volume (c '' Icc (θ - 1) θ) := by
    rw [hK0]
    change volume (Complex.orthonormalBasisOneI.repr.toLinearEquiv.toEquiv '' (c '' Icc (θ - 1) θ)) = _
    rw [Equiv.image_eq_preimage_symm]
    change volume (Complex.orthonormalBasisOneI.repr.symm ⁻¹' (c '' Icc (θ - 1) θ)) = _
    exact Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
      hCc.isClosed.measurableSet.nullMeasurableSet
  have hfin : volume (c '' Icc (θ - 1) θ) ≠ ∞ := hCc.measure_ne_top
  have hquot : ENNReal.ofReal (Metric.diam (c '' Icc (θ - 1) θ) ^ 2 / (volume (c '' Icc (θ - 1) θ)).toReal) ≤
      ENNReal.ofReal (Metric.diam (c '' Icc (θ - 1) θ) ^ 2) / volume (c '' Icc (θ - 1) θ) := by
    by_cases hz : volume (c '' Icc (θ - 1) θ) = 0
    · simp [hz]
    · rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hz hfin), ENNReal.ofReal_toReal hfin]
  have hA : ENNReal.ofReal (Metric.diam (unitCell w 0) ^ 2 / (volume (unitCell w 0)).toReal) ≤
      diamAreaSup c := by
    rw [hd, hv]
    exact hquot.trans (le_iSup₂ (f := fun s (_ : s ∈ Icc (0 : ℝ) 1) =>
      ENNReal.ofReal (Metric.diam (c '' Icc (s - 1) s) ^ 2) / volume (c '' Icc (s - 1) s)) θ hθ)
  have hT : {i : ℤ | 0 < w.2 i 0}.Finite := (h.finite_setOf_pos 0).subset fun i hi => by
    show 0 < w.2 0 i
    rw [h.m_symm]
    exact hi
  have hTk : ∀ k ∈ hT.toFinset,
      (c '' Icc ((k : ℝ) - 1 + θ) ((k : ℝ) - 1 + θ + 1) ∩ c '' Icc (θ - 1) θ).Nonempty := by
    intro k hk
    obtain ⟨x, hxk, hx0⟩ := h.m_inter k 0 (hT.mem_toFinset.1 hk)
    rw [hcell k] at hxk
    rw [hK0] at hx0
    obtain ⟨y, hy, rfl⟩ := hxk
    obtain ⟨y', hy', hyy⟩ := hx0
    rw [Complex.orthonormalBasisOneI.repr.injective hyy] at hy'
    exact ⟨y, hy, hy'⟩
  have hcard : ((hT.toFinset.card : ℕ) : ℝ≥0∞) ≤ (degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe, ← ENat.toENNReal_add, ENat.toENNReal_le]
    exact ZeroConeRoot.card_le_degInner_add_degOuter hc0 hD hθ.1 hθ.2 _ hTk
  have hsum : ∑ᶠ i ∈ {i : ℤ | 0 < w.2 i 0}, ((w.2 i 0 : ℝ) + ((w.2 i 0 : ℝ))⁻¹) ≤
      (hT.toFinset.card : ℝ) * 3 := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hT, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : (1 : ℝ) ≤ w.2 i 0 := Nat.one_le_cast.mpr (hT.mem_toFinset.1 hi)
    have h2 : (w.2 i 0 : ℝ) ≤ 2 := by exact_mod_cast hm2 i 0
    have h3 : ((w.2 i 0 : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    linarith
  rw [weight, ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
  refine mul_le_mul' hA ?_
  calc ENNReal.ofReal (∑ᶠ i ∈ {i : ℤ | 0 < w.2 i 0}, ((w.2 i 0 : ℝ) + ((w.2 i 0 : ℝ))⁻¹))
      ≤ ENNReal.ofReal ((hT.toFinset.card : ℝ) * 3) := ENNReal.ofReal_le_ofReal hsum
    _ = (hT.toFinset.card : ℝ≥0∞) * 3 := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    _ ≤ 3 * ((degInner c : ℝ≥0∞) + (degOuter c : ℝ≥0∞)) := by
        rw [mul_comm]
        exact mul_le_mul' le_rfl hcard

/-- **The polygonal configuration of a valid datum carries its walk.** -/
theorem carriesUnitMeshWalk_polygonalConfig {H₀ : GMSSpace} {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (h : UnitMeshValid w) : CarriesUnitMeshWalk w (polygonalConfig H₀ w) :=
  carriesUnitMeshWalk_body_polygonalConfig h

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The polygonal configuration of the shifted zero-cone data carries their walk almost surely.** For every
default point `H₀`, almost surely under `P ⊗ Unif[0, 1]` the cells of `polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)`
carry the walk of the unit-mesh datum `phaseShiftedData η₀ G 1 p`. -/
theorem ae_carriesUnitMeshWalk_polygonalConfig
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {G : Ω → Path2} (hG : IsZeroConeBoundaryPair D hγ G) (H₀ : GMSSpace) :
    ∀ᵐ p ∂P.prod zeroConePhase,
      CarriesUnitMeshWalk (phaseShiftedData η₀ G 1 p) (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) :=
  (ae_unitMeshValid_phaseShifted D hγ hG).mono fun _ h => carriesUnitMeshWalk_polygonalConfig h

/-- **The law of the zero-cone polygonal configuration is connected along lines** (hypothesis 3 of
Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16). For every default point `H₀`, if the map
`Φ_G p = polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)` is almost everywhere measurable for `P ⊗ Unif[0, 1]`,
then its law is connected along lines. -/
theorem connectedAlongLines_polygonalConfig
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {G : Ω → Path2} (hG : IsZeroConeBoundaryPair D hγ G) (H₀ : GMSSpace)
    (hΦ : AEMeasurable (fun p => polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) (P.prod zeroConePhase)) :
    ConnectedAlongLines
      ((P.prod zeroConePhase).map fun p => polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) :=
  connectedAlongLines_map_of_ae_lineConnected (P.prod zeroConePhase)
    (fun p => (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)).1)
    ((ae_unitMeshValid_phaseShifted D hγ hG).mono fun _ h => lineConnected_polygonalConfig h) _ hΦ
    (ae_of_all _ fun _ => rfl)

/-- **The finite-expectation hypothesis for the zero-cone polygonal configuration** (hypothesis (1.5) of
Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16; answer, lines 35-40). For every default point `H₀`, if
the map `Φ_G p = polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)` is almost everywhere measurable for
`P ⊗ Unif[0, 1]`, then its law satisfies `FiniteExpectation`, with the root cell `rootCell`. -/
theorem finiteExpectation_polygonalConfig
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {G : Ω → Path2} (hG : IsZeroConeBoundaryPair D hγ G) (H₀ : GMSSpace)
    (hΦ : AEMeasurable (fun p => polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) (P.prod zeroConePhase)) :
    FiniteExpectation
      ((P.prod zeroConePhase).map fun p => polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) := by
  have := D.isProbabilityMeasure
  have hfin := ZeroConeRoot.lintegral_diamAreaSup_mul_deg_lt_top hγ.1 hγ.2 D.measurable_curves.2.2.1
    D.cellMoments
  have hphase : ∀ᵐ p ∂P.prod zeroConePhase, p.2 ∈ Icc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  have hreg : ∀ᵐ p ∂P.prod zeroConePhase,
      η₀ p.1 0 = 0 ∧ 0 < Metric.diam (η₀ p.1 '' Icc (-1) 1) :=
    Measure.quasiMeasurePreserving_fst.ae D.ae_zeroCone_root_regular
  have hbound : ∀ᵐ p ∂P.prod zeroConePhase,
      ENNReal.ofReal (rootDensity (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p))
          (rootCell (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)))) ≤
        24 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) + (degOuter (η₀ p.1) : ℝ≥0∞))) ∧
      (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)).1.piStar
          (rootCell (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p))) ≤
        (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)).1.pi
          (rootCell (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p))) := by
    filter_upwards [ae_unitMeshValid_phaseShifted D hγ hG, hphase, hreg] with p hv hθ hr
    have hcell : ∀ k : ℤ, unitCell (phaseShiftedData η₀ G 1 p) k =
        Complex.orthonormalBasisOneI.repr '' (η₀ p.1 '' Icc ((k : ℝ) - 1 + p.2) ((k : ℝ) - 1 + p.2 + 1)) :=
      fun k => unitCell_phaseShifted (η₀ p.1) p.2 _ k
    have hi : (0 : ReflectedGMS.Plane) ∈ unitCell (phaseShiftedData η₀ G 1 p) 0 := by
      rw [hcell 0]
      refine ⟨η₀ p.1 0, ⟨0, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · rw [Int.cast_zero]
        linarith [hθ.2]
      · rw [Int.cast_zero]
        linarith [hθ.1]
      · rw [hr.1, map_zero]
    have hm2 : ∀ i j, (phaseShiftedData η₀ G 1 p).2 i j ≤ 2 := fun i j =>
      show phaseShiftedEdgeCount 1 p.2 (G p.1) i j ≤ 2 from bmEdgeCount_le_two _ _ _ i j
    refine ⟨?_, piStar_polygonalConfig_le_pi hv _⟩
    calc ENNReal.ofReal (rootDensity (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p))
          (rootCell (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p))))
        ≤ ENNReal.ofReal (8 * weight (unitCell (phaseShiftedData η₀ G 1 p)) (phaseShiftedData η₀ G 1 p).2 0) :=
          ENNReal.ofReal_le_ofReal (rootDensity_polygonalConfig_le hv hi)
      _ = 8 * ENNReal.ofReal (weight (unitCell (phaseShiftedData η₀ G 1 p)) (phaseShiftedData η₀ G 1 p).2 0) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat]
      _ ≤ 8 * (diamAreaSup (η₀ p.1) * (3 * ((degInner (η₀ p.1) : ℝ≥0∞) + (degOuter (η₀ p.1) : ℝ≥0∞)))) :=
          mul_le_mul' le_rfl (ofReal_weight_zero_le hr.1 hr.2 hθ hv hcell hm2)
      _ = 24 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) + (degOuter (η₀ p.1) : ℝ≥0∞))) := by
          ring
  have hint : ∫⁻ p, 24 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) +
      (degOuter (η₀ p.1) : ℝ≥0∞))) ∂(P.prod zeroConePhase) < ∞ := by
    calc ∫⁻ p, 24 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) +
            (degOuter (η₀ p.1) : ℝ≥0∞))) ∂(P.prod zeroConePhase)
        ≤ ∫⁻ ω, ∫⁻ _ : ℝ, 24 * (diamAreaSup (η₀ ω) * ((degInner (η₀ ω) : ℝ≥0∞) +
            (degOuter (η₀ ω) : ℝ≥0∞))) ∂zeroConePhase ∂P := lintegral_prod_le _
      _ = 24 * ∫⁻ ω, diamAreaSup (η₀ ω) * ((degInner (η₀ ω) : ℝ≥0∞) + (degOuter (η₀ ω) : ℝ≥0∞)) ∂P := by
        simp only [lintegral_const, measure_univ, mul_one]
        exact lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top hfin
  refine ⟨rootCell, rootCell_mem, ?_, ?_⟩
  · calc _ ≤ ∫⁻ p, (fun H => ENNReal.ofReal (rootDensity H (rootCell H)))
            (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) ∂(P.prod zeroConePhase) :=
          lintegral_map_le (fun H => ENNReal.ofReal (rootDensity H (rootCell H))) hΦ
      _ ≤ ∫⁻ p, 24 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) +
            (degOuter (η₀ p.1) : ℝ≥0∞))) ∂(P.prod zeroConePhase) :=
          lintegral_mono_ae (hbound.mono fun _ hp => hp.1)
      _ < ∞ := hint
  · calc _ ≤ ∫⁻ p, (fun H : GMSSpace => ENNReal.ofReal
            (Metric.diam (rootCell H : Set ReflectedGMS.Plane) ^ 2 / CellConfig.area (rootCell H) *
              H.1.piStar (rootCell H)))
            (polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)) ∂(P.prod zeroConePhase) :=
          lintegral_map_le (fun H : GMSSpace => ENNReal.ofReal
            (Metric.diam (rootCell H : Set ReflectedGMS.Plane) ^ 2 / CellConfig.area (rootCell H) *
              H.1.piStar (rootCell H))) hΦ
      _ ≤ ∫⁻ p, 24 * (diamAreaSup (η₀ p.1) * ((degInner (η₀ p.1) : ℝ≥0∞) +
            (degOuter (η₀ p.1) : ℝ≥0∞))) ∂(P.prod zeroConePhase) :=
          lintegral_mono_ae (hbound.mono fun _ hp => le_trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left hp.2 (div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg))) hp.1)
      _ < ∞ := hint

end MatedCRT.ZeroConePolygonal
