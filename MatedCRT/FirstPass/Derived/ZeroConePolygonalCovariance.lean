import MatedCRT.FirstPass.Derived.ZeroConePolygonalConfig
import MatedCRT.FirstPass.Derived.CellSideMult
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurableLocal

/-!
# Covariance of the polygonal construction under isometries and integer relabelling

The polygonal cell configuration of a unit-mesh datum `w = (η, m)` (`polygonalConfig`) is built from choices that
commute with the linear isometries of the plane and with the integer relabelling `j ↦ j + k` of the cells. This is
the covariance used for the law of the polygonal configuration in the proof of Lemma 3.5 of Gwynne–Miller–Sheffield
(arXiv:1705.11161v5, p. 26), whose limiting covariance is a multiple of the identity because the law of the
configuration is invariant under rotations about the origin (proof of Proposition 3.1, p. 24).

**Linear isometries.** For a linear isometry `T` of the plane:

* `image_tile`, `image_tileVertices`, `image_shared`: `T` carries the Voronoi tiles, their vertices and their shared
  pieces of the sites `V` to those of the sites `T V`.
* `PolygonalInput.mapIso`: the image of a polygonal input; `labels_mapIso`, `owner_mapIso`, `piece_mapIso`,
  `cell_mapIso`: labels and owners are unchanged and the pieces and cells are carried by `T`;
  `cellConfig_mapIso_cells`, `cellConfig_mapIso_c`: the GMS cells are the images of the cells, with the same
  conductances.
* `dyadicSites_map`, `scaleFun_map`, `weight_map`: the dyadic sites, the scale function and the weights of the old
  cells are carried by `T`.
* `mapDatum T w`: the datum with the curve carried by `T` in the complex coordinate and the same edge counts;
  `polygonalInputOf_mapDatum`, `unitMeshValid_mapDatum_iff`, and `polygonalConfig_mapDatum_cells`,
  `polygonalConfig_mapDatum_c`: the polygonal configuration of `mapDatum T w` is the image under `T` of that of `w`.

**Integer relabelling.** For `k ∈ ℤ`, `shiftDatum k w` is the curve `t ↦ η(t + k)` with the edge counts
`m (i + k) (j + k)`: `polygonalConfig_shiftDatum` shows that it has the same polygonal configuration (the owner rule
breaks ties by the order of the labels, which the relabelling preserves).

**The frontier-side multiplicities.** `cellSideMult_homeomorph`: the multiplicities `cellSideMult ε η j k` read off
the curve (Gwynne–Miller–Sheffield, arXiv:1705.11161v5, §2.5 and Proposition 2.2, pp. 20-21) are unchanged when the
curve is composed with a homeomorphism of the plane (in particular a rotation `z ↦ i z`, `cellSideMult_mul_left`);
`cellSideMult_comp_add_int`: an integer time shift of the curve relabels them.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology Relation

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

/-! ## Linear isometries of the plane -/

section LinearIsometry

variable (T : Plane ≃ₗᵢ[ℝ] Plane)

theorem volume_image_linearIsometryEquiv (s : Set Plane) : volume (T '' s) = volume s := by
  rw [T.image_eq_preimage_symm]
  exact T.symm.measurePreserving.measure_preimage_emb T.symm.toHomeomorph.measurableEmbedding s

/-- **A linear isometry carries the Voronoi tiles.** -/
theorem image_tile (V : Set Plane) (p : Plane) : T '' tile V p = tile (T '' V) (T p) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [T.dist_map, T.dist_map]
    exact hx q hq
  · intro hy
    refine ⟨T.symm y, fun q hq => ?_, T.apply_symm_apply y⟩
    have h := hy (T q) (mem_image_of_mem T hq)
    rw [← T.dist_map (T.symm y) p, ← T.dist_map (T.symm y) q, T.apply_symm_apply]
    exact h

theorem image_tileVertices (V : Set Plane) (p : Plane) :
    T '' tileVertices V p = tileVertices (T '' V) (T p) := by
  rw [tileVertices, tileVertices, ← image_tile]
  exact image_extremePoints (𝕜 := ℝ) T (tile V p)

theorem image_segment_linearIsometryEquiv (a b : Plane) : T '' segment ℝ a b = segment ℝ (T a) (T b) := by
  simpa using image_segment ℝ T.toLinearEquiv.toLinearMap.toAffineMap a b

/-- **A linear isometry carries the shared pieces of the tiles.** -/
theorem image_shared (V : Set Plane) (p : Plane) : T '' shared V p = shared (T '' V) (T p) := by
  rw [shared, shared, image_union, image_iUnion₂, ← image_tileVertices, biUnion_image, ← image_tile]
  congr 1
  · simpa using T.toHomeomorph.image_frontier (tile V p)
  · exact iUnion₂_congr fun v _ => image_segment_linearIsometryEquiv T p v

/-! ### The dyadic sites -/

variable {T}

theorem timeCell_map (q : ℝ → Plane) (j : ℤ) : timeCell (fun t => T (q t)) j = T '' timeCell q j := by
  rw [timeCell, timeCell, image_image]

theorem scaleMin_map (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) :
    scaleMin (fun t => T (q t)) (fun z => s (T.symm z)) j = scaleMin q s j := by
  rw [scaleMin, scaleMin, timeCell_map, image_image]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem diam_image_comp (q : ℝ → Plane) (S : Set ℝ) : diam ((fun t => T (q t)) '' S) = diam (q '' S) := by
  rw [← T.diam_image (q '' S), image_image]

theorem dyadicFine_map (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) (n : ℕ) :
    DyadicFine (fun t => T (q t)) (fun z => s (T.symm z)) j n = DyadicFine q s j n := by
  simp only [DyadicFine, diam_image_comp, scaleMin_map]

theorem dyadicLevel_map (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) :
    dyadicLevel (fun t => T (q t)) (fun z => s (T.symm z)) j = dyadicLevel q s j := by
  simp only [dyadicLevel, dyadicFine_map]

theorem cellSites_map (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) :
    cellSites (fun t => T (q t)) (fun z => s (T.symm z)) j = T '' cellSites q s j := by
  rw [cellSites, cellSites, dyadicLevel_map, image_image]

/-- **A linear isometry carries the dyadic sites of a curve.** -/
theorem dyadicSites_map (q : ℝ → Plane) (s : Plane → ℝ) :
    dyadicSites (fun t => T (q t)) (fun z => s (T.symm z)) = T '' dyadicSites q s := by
  rw [dyadicSites, dyadicSites, image_iUnion]
  exact iUnion_congr fun j => cellSites_map q s j

/-! ### The old cells -/

theorem otherCells_map (K : ℤ → Set Plane) (j : ℤ) :
    otherCells (fun i => T '' K i) j = T '' otherCells K j := by
  rw [otherCells, otherCells, image_iUnion₂]

theorem coreSet_map (K : ℤ → Set Plane) (j : ℤ) (δ : ℝ) :
    coreSet (fun i => T '' K i) j δ = T '' coreSet K j δ := by
  ext y
  obtain ⟨x, rfl⟩ := T.surjective y
  rw [T.injective.mem_set_image]
  show T x ∈ T '' K j ∧ δ < infDist (T x) (otherCells (fun i => T '' K i) j) ↔
    x ∈ K j ∧ δ < infDist x (otherCells K j)
  rw [T.injective.mem_set_image, otherCells_map, Metric.infDist_image T.isometry]

theorem coreIndex_map (K : ℤ → Set Plane) (j : ℤ) : coreIndex (fun i => T '' K i) j = coreIndex K j := by
  simp only [coreIndex, T.diam_image, coreSet_map, volume_image_linearIsometryEquiv]

theorem coreScale_map (K : ℤ → Set Plane) (j : ℤ) : coreScale (fun i => T '' K i) j = coreScale K j := by
  simp only [coreScale, T.diam_image, coreIndex_map]

/-- **A linear isometry carries the scale function**: `r_{T K}(z) = r_K(T⁻¹ z)`. -/
theorem scaleFun_map (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) (z : Plane) :
    scaleFun (fun i => T '' K i) m z = scaleFun K m (T.symm z) := by
  simp only [scaleFun, coreScale_map]
  refine iInf_congr fun j => ?_
  have h : infDist z (T '' K j) = infDist (T.symm z) (K j) := by
    conv_lhs => rw [← T.apply_symm_apply z]
    exact Metric.infDist_image T.isometry
  rw [h]

/-- **The weights are invariant under a linear isometry.** -/
theorem weight_map (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) : weight (fun i => T '' K i) m = weight K m := by
  funext j
  simp only [weight, T.diam_image, volume_image_linearIsometryEquiv]

end LinearIsometry

/-! ## The polygonal input under a linear isometry -/

namespace PolygonalInput

/-- Two polygonal inputs with the same fields are equal. -/
theorem ext' {I J : PolygonalInput} (hK : I.K = J.K) (hm : I.m = J.m) (hv : I.v = J.v) (hV : I.V = J.V)
    (hr : I.r = J.r) (he : I.e = J.e) : I = J := by
  cases I
  cases J
  cases hK
  cases hm
  cases hv
  cases hV
  cases hr
  cases he
  rfl

/-- **The image of a polygonal input under a linear isometry `T`**: old cells, vertices and sites carried by `T`,
the scale function composed with `T⁻¹`, the same counts and weights. -/
def mapIso (T : Plane ≃ₗᵢ[ℝ] Plane) (I : PolygonalInput) : PolygonalInput where
  K j := T '' I.K j
  m := I.m
  v j := T (I.v j)
  V := T '' I.V
  r z := I.r (T.symm z)
  e := I.e

variable (T : Plane ≃ₗᵢ[ℝ] Plane) (I : PolygonalInput)

theorem labels_mapIso (p : Plane) : (I.mapIso T).labels (T p) = I.labels p := by
  ext j
  show (T '' I.K j ∩ tile (T '' I.V) (T p)).Nonempty ↔ (I.K j ∩ tile I.V p).Nonempty
  rw [← image_tile, ← image_inter T.injective, image_nonempty]

theorem isOwner_mapIso (p : Plane) : (I.mapIso T).IsOwner (T p) = I.IsOwner p := by
  funext j
  show (j ∈ (I.mapIso T).labels (T p) ∧ ∀ i ∈ (I.mapIso T).labels (T p), toLex (I.e j, j) ≤ toLex (I.e i, i)) =
    (j ∈ I.labels p ∧ ∀ i ∈ I.labels p, toLex (I.e j, j) ≤ toLex (I.e i, i))
  rw [labels_mapIso]

/-- **The owner of a tile is unchanged by a linear isometry.** -/
theorem owner_mapIso (p : Plane) : (I.mapIso T).owner (T p) = I.owner p := by
  rw [owner, owner, isOwner_mapIso]

theorem piece_mapIso (p : Plane) (j : ℤ) : (I.mapIso T).piece (T p) j = T '' I.piece p j := by
  unfold piece
  rw [owner_mapIso]
  split_ifs
  · exact (image_tile T I.V p).symm
  · exact (image_shared T I.V p).symm

theorem sitesOf_mapIso (j : ℤ) : (I.mapIso T).sitesOf j = T '' I.sitesOf j := by
  ext y
  obtain ⟨x, rfl⟩ := T.surjective y
  rw [T.injective.mem_set_image]
  show T x ∈ T '' I.V ∧ j ∈ (I.mapIso T).labels (T x) ↔ x ∈ I.V ∧ j ∈ I.labels x
  rw [T.injective.mem_set_image, labels_mapIso]

/-- **A linear isometry carries the polygonal cells.** -/
theorem cell_mapIso (j : ℤ) : (I.mapIso T).cell j = T '' I.cell j := by
  rw [cell, cell, sitesOf_mapIso, biUnion_image, image_iUnion₂]
  exact iUnion₂_congr fun p _ => piece_mapIso T I p j

variable {T I}

theorem cellNC_mapIso (hI : I.IsValid) (hI' : (I.mapIso T).IsValid) (j : ℤ) :
    (I.mapIso T).cellNC j = CellConfig.mapCell T.toHomeomorph (I.cellNC j) := by
  apply SetLike.coe_injective
  rw [hI'.coe_cellNC, CellConfig.coe_mapCell_eq_image, hI.coe_cellNC, cell_mapIso,
    LinearIsometryEquiv.coe_toHomeomorph]

/-- **The GMS cells of the image input are the images of the GMS cells.** -/
theorem cellConfig_mapIso_cells (hI : I.IsValid) (hI' : (I.mapIso T).IsValid) :
    (I.mapIso T).cellConfig.cells = CellConfig.mapCell T.toHomeomorph '' I.cellConfig.cells := by
  show range (I.mapIso T).cellNC = CellConfig.mapCell T.toHomeomorph '' range I.cellNC
  rw [← range_comp]
  exact congrArg range (funext (cellNC_mapIso hI hI'))

/-- **The conductances of the image input are those of the input, read through `T⁻¹`.** -/
theorem cellConfig_mapIso_c (hI : I.IsValid) (hI' : (I.mapIso T).IsValid) (K K' : Cell) :
    (I.mapIso T).cellConfig.c K K' =
      I.cellConfig.c (CellConfig.mapCell T.toHomeomorph.symm K) (CellConfig.mapCell T.toHomeomorph.symm K') := by
  have hnc := cellNC_mapIso hI hI'
  have hmem : ∀ L : Cell, L ∈ range (I.mapIso T).cellNC ↔
      CellConfig.mapCell T.toHomeomorph.symm L ∈ range I.cellNC := by
    intro L
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, by rw [hnc, CellConfig.mapCell_symm_mapCell]⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hnc, hj, CellConfig.mapCell_mapCell_symm]⟩
  by_cases h : K ∈ range (I.mapIso T).cellNC ∧ K' ∈ range (I.mapIso T).cellNC
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
    rw [hI'.cellConfig_c, hnc, hnc, CellConfig.mapCell_symm_mapCell, CellConfig.mapCell_symm_mapCell,
      hI.cellConfig_c]
    rfl
  · have h' : ¬ (CellConfig.mapCell T.toHomeomorph.symm K ∈ range I.cellNC ∧
        CellConfig.mapCell T.toHomeomorph.symm K' ∈ range I.cellNC) := by
      rwa [← hmem, ← hmem]
    rw [cellConfig_c_of_not_mem h, cellConfig_c_of_not_mem h']

end PolygonalInput

/-! ## The datum under a linear isometry -/

section MapDatum

/-- **The image of a unit-mesh datum under a linear isometry `T` of the plane**: the curve is carried by `T` in the
complex coordinate and the edge counts are unchanged. -/
def mapDatum (T : Plane ≃ₗᵢ[ℝ] Plane) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  (⟨fun t => Complex.orthonormalBasisOneI.repr.symm (T (Complex.orthonormalBasisOneI.repr (w.1 t))),
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp
      (T.continuous.comp (Complex.orthonormalBasisOneI.repr.continuous.comp w.1.continuous))⟩, w.2)

variable (T : Plane ≃ₗᵢ[ℝ] Plane) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ))

theorem curvePlane_mapDatum : curvePlane (mapDatum T w) = fun t => T (curvePlane w t) := by
  funext t
  exact Complex.orthonormalBasisOneI.repr.apply_symm_apply _

theorem unitCell_mapDatum (j : ℤ) : unitCell (mapDatum T w) j = T '' unitCell w j := by
  rw [← timeCell_curvePlane, ← timeCell_curvePlane, curvePlane_mapDatum, timeCell_map]

theorem unitVertex_mapDatum (j : ℤ) : unitVertex (mapDatum T w) j = T (unitVertex w j) := by
  rw [unitVertex_eq, unitVertex_eq, curvePlane_mapDatum]

theorem mapDatum_symm_mapDatum : mapDatum T.symm (mapDatum T w) = w := by
  refine Prod.ext (ContinuousMap.ext fun t => ?_) rfl
  show Complex.orthonormalBasisOneI.repr.symm (T.symm (Complex.orthonormalBasisOneI.repr
      (Complex.orthonormalBasisOneI.repr.symm (T (Complex.orthonormalBasisOneI.repr (w.1 t)))))) = w.1 t
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]

theorem scaleFun_unitCell_mapDatum :
    scaleFun (unitCell (mapDatum T w)) (mapDatum T w).2 = fun z => scaleFun (unitCell w) w.2 (T.symm z) := by
  rw [show unitCell (mapDatum T w) = fun i => T '' unitCell w i from funext (unitCell_mapDatum T w)]
  funext z
  exact scaleFun_map (unitCell w) w.2 z

/-- **The polygonal input of the image datum is the image of the polygonal input.** -/
theorem polygonalInputOf_mapDatum : polygonalInputOf (mapDatum T w) = (polygonalInputOf w).mapIso T := by
  refine PolygonalInput.ext' (funext (unitCell_mapDatum T w)) rfl (funext (unitVertex_mapDatum T w)) ?_
    (scaleFun_unitCell_mapDatum T w) ?_
  · show dyadicSites (curvePlane (mapDatum T w)) (scaleFun (unitCell (mapDatum T w)) (mapDatum T w).2) =
      T '' dyadicSites (curvePlane w) (scaleFun (unitCell w) w.2)
    rw [scaleFun_unitCell_mapDatum, curvePlane_mapDatum]
    exact dyadicSites_map (curvePlane w) (scaleFun (unitCell w) w.2)
  · show weight (unitCell (mapDatum T w)) w.2 = weight (unitCell w) w.2
    rw [show unitCell (mapDatum T w) = fun i => T '' unitCell w i from funext (unitCell_mapDatum T w)]
    exact weight_map (unitCell w) w.2

variable {T w}

/-- **Validity is carried by a linear isometry.** -/
theorem unitMeshValid_mapDatum (h : UnitMeshValid w) : UnitMeshValid (mapDatum T w) where
  volume_pos j := by
    rw [unitCell_mapDatum, volume_image_linearIsometryEquiv]
    exact h.volume_pos j
  lf A hA := (h.lf _ (hA.image T.symm.continuous)).subset fun j hj => by
    obtain ⟨y, hy, hyA⟩ := hj
    rw [unitCell_mapDatum] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, T x, hyA, T.symm_apply_apply x⟩
  cover z := by
    obtain ⟨j, hj⟩ := h.cover (T.symm z)
    exact ⟨j, by rw [unitCell_mapDatum]; exact ⟨T.symm z, hj, T.apply_symm_apply z⟩⟩
  volume_inter i j hij := by
    rw [unitCell_mapDatum, unitCell_mapDatum, ← image_inter T.injective, volume_image_linearIsometryEquiv]
    exact h.volume_inter i j hij
  m_symm := h.m_symm
  m_diag := h.m_diag
  m_inter i j hm := by
    rw [unitCell_mapDatum, unitCell_mapDatum, ← image_inter T.injective, image_nonempty]
    exact h.m_inter i j hm
  pt z i j hi hj := by
    have hmem : ∀ a, z ∈ unitCell (mapDatum T w) a ↔ T.symm z ∈ unitCell w a := fun a => by
      rw [unitCell_mapDatum]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rwa [T.symm_apply_apply]
      · intro hz
        exact ⟨T.symm z, hz, T.apply_symm_apply z⟩
    have key : ∀ a b, (0 < w.2 a b ∧ T.symm z ∈ unitCell w a ∧ T.symm z ∈ unitCell w b) →
        (0 < (mapDatum T w).2 a b ∧ z ∈ unitCell (mapDatum T w) a ∧ z ∈ unitCell (mapDatum T w) b) :=
      fun a b hab => ⟨hab.1, (hmem a).2 hab.2.1, (hmem b).2 hab.2.2⟩
    exact Relation.ReflTransGen.mono
      (p := fun a b => 0 < (mapDatum T w).2 a b ∧ z ∈ unitCell (mapDatum T w) a ∧ z ∈ unitCell (mapDatum T w) b)
      key i j (h.pt (T.symm z) i j ((hmem i).1 hi) ((hmem j).1 hj))

theorem unitMeshValid_mapDatum_iff : UnitMeshValid (mapDatum T w) ↔ UnitMeshValid w :=
  ⟨fun h => by
    have h' := unitMeshValid_mapDatum (T := T.symm) h
    rwa [mapDatum_symm_mapDatum] at h', unitMeshValid_mapDatum⟩

/-- **The GMS cells of the polygonal configuration of `mapDatum T w` are the images under `T` of those of `w`**,
for a valid datum `w` and any default points. -/
theorem polygonalConfig_mapDatum_cells (h : UnitMeshValid w) (H₀ H₀' : GMSSpace) :
    (polygonalConfig H₀' (mapDatum T w)).1.cells =
      CellConfig.mapCell T.toHomeomorph '' (polygonalConfig H₀ w).1.cells := by
  have h' : UnitMeshValid (mapDatum T w) := unitMeshValid_mapDatum h
  have hI' : ((polygonalInputOf w).mapIso T).IsValid :=
    polygonalInputOf_mapDatum T w ▸ isValid_polygonalInputOf h'
  rw [polygonalConfig_of_valid h', polygonalConfig_of_valid h]
  show (polygonalInputOf (mapDatum T w)).cellConfig.cells =
    CellConfig.mapCell T.toHomeomorph '' (polygonalInputOf w).cellConfig.cells
  rw [polygonalInputOf_mapDatum]
  exact PolygonalInput.cellConfig_mapIso_cells (isValid_polygonalInputOf h) hI'

/-- **The conductances of the polygonal configuration of `mapDatum T w` are those of `w` read through `T⁻¹`**, for
a valid datum `w` and any default points. -/
theorem polygonalConfig_mapDatum_c (h : UnitMeshValid w) (H₀ H₀' : GMSSpace) (K K' : Cell) :
    (polygonalConfig H₀' (mapDatum T w)).1.c K K' =
      (polygonalConfig H₀ w).1.c (CellConfig.mapCell T.toHomeomorph.symm K)
        (CellConfig.mapCell T.toHomeomorph.symm K') := by
  have h' : UnitMeshValid (mapDatum T w) := unitMeshValid_mapDatum h
  have hI' : ((polygonalInputOf w).mapIso T).IsValid :=
    polygonalInputOf_mapDatum T w ▸ isValid_polygonalInputOf h'
  rw [polygonalConfig_of_valid h', polygonalConfig_of_valid h]
  show (polygonalInputOf (mapDatum T w)).cellConfig.c K K' =
    (polygonalInputOf w).cellConfig.c (CellConfig.mapCell T.toHomeomorph.symm K)
      (CellConfig.mapCell T.toHomeomorph.symm K')
  rw [polygonalInputOf_mapDatum]
  exact PolygonalInput.cellConfig_mapIso_c (isValid_polygonalInputOf h) hI' K K'

end MapDatum

/-! ## Integer relabelling -/

section Shift

theorem image_comp_add_Icc {X : Type*} (q : ℝ → X) (c a b : ℝ) :
    (fun t => q (t + c)) '' Icc a b = q '' Icc (a + c) (b + c) := by
  rw [show (fun t => q (t + c)) = q ∘ fun t => t + c from rfl, image_comp, image_add_const_Icc]

variable (k : ℤ)

theorem timeCell_comp_add (q : ℝ → Plane) (j : ℤ) : timeCell (fun t => q (t + k)) j = timeCell q (j + k) := by
  rw [timeCell, timeCell, image_comp_add_Icc]
  push_cast
  rw [sub_add_eq_add_sub]

theorem scaleMin_comp_add (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) :
    scaleMin (fun t => q (t + k)) s j = scaleMin q s (j + k) := by
  rw [scaleMin, scaleMin, timeCell_comp_add]

theorem dyadicPoint_add (j : ℤ) (n m : ℕ) : dyadicPoint j n m + k = dyadicPoint (j + k) n m := by
  unfold dyadicPoint
  push_cast
  ring

theorem dyadicFine_comp_add (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) (n : ℕ) :
    DyadicFine (fun t => q (t + k)) s j n = DyadicFine q s (j + k) n := by
  simp only [DyadicFine, scaleMin_comp_add, image_comp_add_Icc, dyadicPoint_add]

theorem dyadicLevel_comp_add (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) :
    dyadicLevel (fun t => q (t + k)) s j = dyadicLevel q s (j + k) := by
  simp only [dyadicLevel, dyadicFine_comp_add]

theorem cellSites_comp_add (q : ℝ → Plane) (s : Plane → ℝ) (j : ℤ) :
    cellSites (fun t => q (t + k)) s j = cellSites q s (j + k) := by
  rw [cellSites, cellSites, dyadicLevel_comp_add]
  congr 1
  funext m
  simp only [dyadicPoint_add]

/-- **The dyadic sites are unchanged by an integer time shift of the curve.** -/
theorem dyadicSites_comp_add (q : ℝ → Plane) (s : Plane → ℝ) :
    dyadicSites (fun t => q (t + k)) s = dyadicSites q s := by
  rw [dyadicSites, dyadicSites]
  simp only [cellSites_comp_add]
  exact (Equiv.addRight k).surjective.iUnion_comp (cellSites q s)

theorem otherCells_comp_add (K : ℤ → Set Plane) (j : ℤ) :
    otherCells (fun i => K (i + k)) j = otherCells K (j + k) := by
  ext y
  simp only [otherCells, mem_iUnion]
  constructor
  · rintro ⟨i, hi, hy⟩
    exact ⟨i + k, fun h => hi (add_right_cancel h), hy⟩
  · rintro ⟨i, hi, hy⟩
    exact ⟨i - k, fun h => hi (by rw [← h, sub_add_cancel]), by rwa [sub_add_cancel]⟩

theorem coreSet_comp_add (K : ℤ → Set Plane) (j : ℤ) (δ : ℝ) :
    coreSet (fun i => K (i + k)) j δ = coreSet K (j + k) δ := by
  simp only [coreSet, otherCells_comp_add]

theorem coreIndex_comp_add (K : ℤ → Set Plane) (j : ℤ) :
    coreIndex (fun i => K (i + k)) j = coreIndex K (j + k) := by
  simp only [coreIndex, coreSet_comp_add]

theorem coreScale_comp_add (K : ℤ → Set Plane) (j : ℤ) :
    coreScale (fun i => K (i + k)) j = coreScale K (j + k) := by
  simp only [coreScale, coreIndex_comp_add]

/-- **The scale function is unchanged by an integer relabelling of the old cells.** -/
theorem scaleFun_comp_add (K : ℤ → Set Plane) (m m' : ℤ → ℤ → ℕ) :
    scaleFun (fun j => K (j + k)) m' = scaleFun K m := by
  funext z
  simp only [scaleFun, coreScale_comp_add]
  exact (Equiv.addRight k).iInf_comp (g := fun j => coreScale K j + infDist z (K j))

/-- **The weights are relabelled with the old cells.** -/
theorem weight_comp_add (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) (j : ℤ) :
    weight (fun i => K (i + k)) (fun a b => m (a + k) (b + k)) j = weight K m (j + k) := by
  simp only [weight]
  congr 1
  exact finsum_comp_equiv (Equiv.addRight k)
    (f := fun i => ∑ᶠ (_ : i ∈ {i : ℤ | 0 < m i (j + k)}), ((m i (j + k) : ℝ) + ((m i (j + k) : ℝ))⁻¹))

/-! ### The polygonal input under an integer relabelling -/

/-- **The polygonal input relabelled by `j ↦ j + k`**: the `j`-th old cell, vertex and weight are those of the label
`j + k`, the counts are relabelled, the sites and the scale function are unchanged. -/
def PolygonalInput.shiftInput (I : PolygonalInput) : PolygonalInput where
  K j := I.K (j + k)
  m a b := I.m (a + k) (b + k)
  v j := I.v (j + k)
  V := I.V
  r := I.r
  e j := I.e (j + k)

namespace PolygonalInput

variable {k} {I : PolygonalInput}

theorem toLex_add_le_add_iff (a b : ℝ) (i j : ℤ) :
    toLex (a, i + k) ≤ toLex (b, j + k) ↔ toLex (a, i) ≤ toLex (b, j) := by
  simp only [Prod.Lex.toLex_le_toLex, add_le_add_iff_right]

theorem isOwner_shiftInput_iff (p : Plane) (j : ℤ) : (I.shiftInput k).IsOwner p j ↔ I.IsOwner p (j + k) := by
  show (j + k ∈ I.labels p ∧ ∀ i, i + k ∈ I.labels p → toLex (I.e (j + k), j) ≤ toLex (I.e (i + k), i)) ↔
    (j + k ∈ I.labels p ∧ ∀ i ∈ I.labels p, toLex (I.e (j + k), j + k) ≤ toLex (I.e i, i))
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi => ?_⟩
    have h := h2 (i - k) (by rwa [sub_add_cancel])
    rw [sub_add_cancel] at h
    rw [← sub_add_cancel i k, toLex_add_le_add_iff, sub_add_cancel]
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => (toLex_add_le_add_iff _ _ _ _).1 (h2 (i + k) hi)⟩

/-- **The owner of a tile is relabelled** (the ties are broken by the order of the labels). -/
theorem owner_shiftInput (hI : I.IsValid) (p : Plane) : (I.shiftInput k).owner p = I.owner p - k := by
  have h : (I.shiftInput k).IsOwner p (I.owner p - k) :=
    (isOwner_shiftInput_iff p _).2 (by rw [sub_add_cancel]; exact hI.isOwner_owner p)
  exact (Classical.epsilon_spec ⟨_, h⟩ : (I.shiftInput k).IsOwner p ((I.shiftInput k).owner p)).unique h

theorem piece_shiftInput (hI : I.IsValid) (p : Plane) (j : ℤ) :
    (I.shiftInput k).piece p j = I.piece p (j + k) := by
  unfold piece
  rw [owner_shiftInput hI]
  show (if I.owner p - k = j then tile I.V p else shared I.V p) =
    if I.owner p = j + k then tile I.V p else shared I.V p
  by_cases h : I.owner p = j + k
  · rw [ite_eq_left (by omega : I.owner p - k = j), ite_eq_left h]
  · rw [ite_eq_right (by omega : ¬ I.owner p - k = j), ite_eq_right h]

theorem cell_shiftInput (hI : I.IsValid) (j : ℤ) : (I.shiftInput k).cell j = I.cell (j + k) := by
  rw [cell, cell]
  exact iUnion₂_congr fun p _ => piece_shiftInput hI p j

/-- Two inputs with the same polygonal cell have the same nonempty compact cell. -/
theorem cellNC_eq_of_cell_eq {J : PolygonalInput} {i j : ℤ} (h : I.cell i = J.cell j) : I.cellNC i = J.cellNC j := by
  unfold cellNC
  by_cases hc : IsCompact (J.cell j) ∧ (J.cell j).Nonempty
  · have hc' : IsCompact (I.cell i) ∧ (I.cell i).Nonempty := by
      rw [h]
      exact hc
    rw [dite_eq_left hc', dite_eq_left hc]
    exact TopologicalSpace.NonemptyCompacts.ext h
  · have hc' : ¬ (IsCompact (I.cell i) ∧ (I.cell i).Nonempty) := by
      rw [h]
      exact hc
    rw [dite_eq_right hc', dite_eq_right hc]

theorem cellNC_shiftInput (hI : I.IsValid) (j : ℤ) : (I.shiftInput k).cellNC j = I.cellNC (j + k) :=
  cellNC_eq_of_cell_eq (cell_shiftInput hI j)

/-- **The GMS configuration is unchanged by an integer relabelling.** -/
theorem cellConfig_shiftInput (hI : I.IsValid) : (I.shiftInput k).cellConfig = I.cellConfig := by
  have hnc : (I.shiftInput k).cellNC = fun j => I.cellNC (j + k) := funext (cellNC_shiftInput hI)
  have hinj : Function.Injective (I.shiftInput k).cellNC := by
    rw [hnc]
    exact hI.cellNC_injective.comp (Equiv.addRight k).injective
  have hrange : range (I.shiftInput k).cellNC = range I.cellNC := by
    rw [hnc]
    exact (Equiv.addRight k).surjective.range_comp I.cellNC
  have hc : (I.shiftInput k).cellConfig.c = I.cellConfig.c := by
    funext K K'
    rw [cellConfig_c_eq, cellConfig_c_eq, hrange]
    by_cases h : K ∈ range I.cellNC ∧ K' ∈ range I.cellNC
    · rw [ite_eq_left h, ite_eq_left h]
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
      have ha : I.cellNC a = (I.shiftInput k).cellNC (a - k) := by rw [cellNC_shiftInput hI, sub_add_cancel]
      have hb : I.cellNC b = (I.shiftInput k).cellNC (b - k) := by rw [cellNC_shiftInput hI, sub_add_cancel]
      rw [Function.leftInverse_invFun hI.cellNC_injective a, Function.leftInverse_invFun hI.cellNC_injective b]
      conv_lhs => rw [ha, hb]
      rw [Function.leftInverse_invFun hinj, Function.leftInverse_invFun hinj]
      show ((I.m (a - k + k) (b - k + k) : ℕ) : ℝ) = (I.m a b : ℝ)
      rw [sub_add_cancel, sub_add_cancel]
    · rw [ite_eq_right h, ite_eq_right h]
  show (⟨range (I.shiftInput k).cellNC, (I.shiftInput k).cellConfig.c⟩ : CellConfig) =
    ⟨range I.cellNC, I.cellConfig.c⟩
  rw [hrange, hc]

end PolygonalInput

/-! ### The datum under an integer relabelling -/

/-- The curve `t ↦ q(t + k)`. -/
def shiftCurve (q : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => q (t + k), q.continuous.comp (continuous_id.add continuous_const)⟩

/-- **The datum relabelled by `j ↦ j + k`**: the curve `t ↦ η(t + k)` with the edge counts `m (i + k) (j + k)`. -/
def shiftDatum (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  (shiftCurve k w.1, fun a b => w.2 (a + k) (b + k))

variable (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ))

theorem unitCell_shiftDatum (j : ℤ) : unitCell (shiftDatum k w) j = unitCell w (j + k) := by
  rw [← timeCell_curvePlane, ← timeCell_curvePlane]
  exact timeCell_comp_add k (curvePlane w) j

theorem unitVertex_shiftDatum (j : ℤ) : unitVertex (shiftDatum k w) j = unitVertex w (j + k) := by
  rw [unitVertex_eq, unitVertex_eq, Int.cast_add]
  rfl

theorem shiftDatum_neg_shiftDatum : shiftDatum (-k) (shiftDatum k w) = w := by
  refine Prod.ext (ContinuousMap.ext fun t => ?_) (funext₂ fun a b => ?_)
  · simp [shiftDatum, shiftCurve]
  · simp [shiftDatum]

/-- **The polygonal input of the relabelled datum is the relabelled polygonal input.** -/
theorem polygonalInputOf_shiftDatum : polygonalInputOf (shiftDatum k w) = (polygonalInputOf w).shiftInput k := by
  have hK : unitCell (shiftDatum k w) = fun j => unitCell w (j + k) := funext (unitCell_shiftDatum k w)
  have hr : scaleFun (unitCell (shiftDatum k w)) (shiftDatum k w).2 = scaleFun (unitCell w) w.2 := by
    rw [hK]
    exact scaleFun_comp_add k (unitCell w) w.2 _
  refine PolygonalInput.ext' hK rfl (funext (unitVertex_shiftDatum k w)) ?_ hr ?_
  · show dyadicSites (curvePlane (shiftDatum k w)) (scaleFun (unitCell (shiftDatum k w)) (shiftDatum k w).2) =
      dyadicSites (curvePlane w) (scaleFun (unitCell w) w.2)
    rw [hr]
    exact dyadicSites_comp_add k (curvePlane w) (scaleFun (unitCell w) w.2)
  · funext j
    show weight (unitCell (shiftDatum k w)) (fun a b => w.2 (a + k) (b + k)) j = weight (unitCell w) w.2 (j + k)
    rw [hK]
    exact weight_comp_add k (unitCell w) w.2 j

variable {k w}

/-- **Validity is preserved by an integer relabelling.** -/
theorem unitMeshValid_shiftDatum (h : UnitMeshValid w) : UnitMeshValid (shiftDatum k w) where
  volume_pos j := by
    rw [unitCell_shiftDatum]
    exact h.volume_pos (j + k)
  lf A hA := (Set.Finite.preimage (f := fun j : ℤ => j + k) (fun a _ b _ hab => add_right_cancel hab)
      (h.lf A hA)).subset fun j hj => by
    change (unitCell (shiftDatum k w) j ∩ A).Nonempty at hj
    rw [unitCell_shiftDatum] at hj
    exact hj
  cover z := by
    obtain ⟨j, hj⟩ := h.cover z
    exact ⟨j - k, by rw [unitCell_shiftDatum, sub_add_cancel]; exact hj⟩
  volume_inter i j hij := by
    rw [unitCell_shiftDatum, unitCell_shiftDatum]
    exact h.volume_inter (i + k) (j + k) fun e => hij (add_right_cancel e)
  m_symm a b := h.m_symm (a + k) (b + k)
  m_diag j := h.m_diag (j + k)
  m_inter a b hm := by
    rw [unitCell_shiftDatum, unitCell_shiftDatum]
    exact h.m_inter (a + k) (b + k) hm
  pt z i j hi hj := by
    rw [unitCell_shiftDatum] at hi hj
    have key : ∀ a b, (0 < w.2 a b ∧ z ∈ unitCell w a ∧ z ∈ unitCell w b) →
        (0 < (shiftDatum k w).2 (a - k) (b - k) ∧ z ∈ unitCell (shiftDatum k w) (a - k) ∧
          z ∈ unitCell (shiftDatum k w) (b - k)) := fun a b hab => by
      refine ⟨?_, ?_, ?_⟩
      · show 0 < w.2 (a - k + k) (b - k + k)
        rw [sub_add_cancel, sub_add_cancel]
        exact hab.1
      · rw [unitCell_shiftDatum, sub_add_cancel]
        exact hab.2.1
      · rw [unitCell_shiftDatum, sub_add_cancel]
        exact hab.2.2
    have h1 : ReflTransGen (fun a b => 0 < (shiftDatum k w).2 a b ∧ z ∈ unitCell (shiftDatum k w) a ∧
        z ∈ unitCell (shiftDatum k w) b) (i + k - k) (j + k - k) :=
      Relation.ReflTransGen.lift (p := fun a b => 0 < (shiftDatum k w).2 a b ∧ z ∈ unitCell (shiftDatum k w) a ∧
        z ∈ unitCell (shiftDatum k w) b) (fun a => a - k) key (i + k) (j + k) (h.pt z (i + k) (j + k) hi hj)
    rwa [add_sub_cancel_right, add_sub_cancel_right] at h1

theorem unitMeshValid_shiftDatum_iff : UnitMeshValid (shiftDatum k w) ↔ UnitMeshValid w :=
  ⟨fun h => by
    have h' := unitMeshValid_shiftDatum (k := -k) h
    rwa [shiftDatum_neg_shiftDatum] at h', unitMeshValid_shiftDatum⟩

/-- **The polygonal configuration is unchanged by an integer relabelling of the datum**: the curve `t ↦ η(t + k)`
with the edge counts `m (i + k) (j + k)` has the polygonal configuration of `(η, m)`, for every default point. -/
theorem polygonalConfig_shiftDatum (H₀ : GMSSpace) : polygonalConfig H₀ (shiftDatum k w) = polygonalConfig H₀ w := by
  by_cases h : UnitMeshValid w
  · rw [polygonalConfig_of_valid (unitMeshValid_shiftDatum_iff.2 h), polygonalConfig_of_valid h]
    apply Subtype.ext
    show (polygonalInputOf (shiftDatum k w)).cellConfig = (polygonalInputOf w).cellConfig
    rw [polygonalInputOf_shiftDatum]
    exact PolygonalInput.cellConfig_shiftInput (isValid_polygonalInputOf h)
  · rw [polygonalConfig_of_not_valid (mt unitMeshValid_shiftDatum_iff.1 h), polygonalConfig_of_not_valid h]

end Shift

/-! ## The frontier-side multiplicities -/

section CellSide

/-- A homeomorphism of the plane carries the contacts of a curve to the contacts of its image. -/
theorem cellSideContact_homeomorph (f : ℂ ≃ₜ ℂ) {a d : ℝ} {η : ℝ → ℂ} {v w : ℝ}
    (h : cellSideContact a d η v w) : cellSideContact a d (fun t => f (η t)) v w := by
  intro p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  obtain ⟨K, hK, hKc, hKconn, hKd⟩ := h p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  have hnt : K.Nontrivial := Set.not_subsingleton_iff.1 fun hs => hKd.ne' (Metric.diam_subsingleton hs)
  refine ⟨f '' K, ?_, hKc.image f.continuous, hKconn.image _ f.continuous.continuousOn,
    Metric.diam_pos (hnt.image f.injective) (hKc.image f.continuous).isBounded⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩ := hK hx
  exact ⟨⟨s, hs, congrArg f hsx⟩, ⟨t, ht, congrArg f htx⟩⟩

theorem cellSideContact_homeomorph_iff (f : ℂ ≃ₜ ℂ) {a d : ℝ} {η : ℝ → ℂ} {v w : ℝ} :
    cellSideContact a d (fun t => f (η t)) v w ↔ cellSideContact a d η v w :=
  ⟨fun h => by simpa using cellSideContact_homeomorph f.symm h, cellSideContact_homeomorph f⟩

/-- **The frontier-side multiplicities are unchanged by a homeomorphism of the plane.** -/
theorem cellSideMult_homeomorph (f : ℂ ≃ₜ ℂ) (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) :
    cellSideMult ε (fun t => f (η t)) j k = cellSideMult ε η j k := by
  have hB : ∀ a b c d : ℝ, cellSideBranchTimes a b c d (fun t => f (η t)) = cellSideBranchTimes a b c d η :=
    fun a b c d => by simp only [cellSideBranchTimes, cellSideContact_homeomorph_iff]
  have hC : ∀ a b c d : ℝ, cellSideCount a b c d (fun t => f (η t)) = cellSideCount a b c d η :=
    fun a b c d => by
      unfold cellSideCount
      rw [hB]
  unfold cellSideMult
  rw [hC]

/-- **The frontier-side multiplicities are unchanged by a rotation and dilation `z ↦ c z`, `c ≠ 0`.** -/
theorem cellSideMult_mul_left {c : ℂ} (hc : c ≠ 0) (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) :
    cellSideMult ε (fun t => c * η t) j k = cellSideMult ε η j k :=
  cellSideMult_homeomorph (Homeomorph.mulLeft₀ c hc) ε η j k

/-- **The frontier-side multiplicities are unchanged by a translation of the plane.** -/
theorem cellSideMult_add_const (z : ℂ) (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) :
    cellSideMult ε (fun t => η t + z) j k = cellSideMult ε η j k :=
  cellSideMult_homeomorph (Homeomorph.addRight z) ε η j k

theorem cellSideContact_of_comp_add_int (k : ℤ) {a d : ℝ} {η : ℝ → ℂ} {v w : ℝ}
    (h : cellSideContact a d (fun t => η (t + k)) v w) :
    cellSideContact (a + k) (d + k) η (v + k) (w + k) := by
  intro p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  have hc : ∀ p : ℚ, ((p - k : ℚ) : ℝ) = (p : ℝ) - k := fun p => by rw [Rat.cast_sub, Rat.cast_intCast]
  obtain ⟨K, hK, hK'⟩ := h (p₁ - k) (p₂ - k) (q₁ - k) (q₂ - k)
    (by rw [hc, hc]; exact ⟨by linarith [hv.1], by linarith [hv.2]⟩)
    (by rw [hc, hc]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)
    (by
      rw [hc, hc, hc, hc]
      exact Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 hdisj
        (show x + k ∈ Ioo (p₁ : ℝ) p₂ from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (show x + k ∈ Ioo (q₁ : ℝ) q₂ from ⟨by linarith [hx'.1], by linarith [hx'.2]⟩))
    (by
      rw [hc, hc]
      intro x hx
      have h' := hP (show x + k ∈ Icc (p₁ : ℝ) p₂ from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩)
    (by
      rw [hc, hc]
      intro x hx
      have h' := hQ (show x + k ∈ Icc (q₁ : ℝ) q₂ from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩)
  refine ⟨K, ?_, hK'⟩
  rwa [image_comp_add_Icc, image_comp_add_Icc, hc, hc, hc, hc, sub_add_cancel, sub_add_cancel,
    sub_add_cancel, sub_add_cancel] at hK

theorem cellSideContact_comp_add_int (k : ℤ) {a d : ℝ} {η : ℝ → ℂ} {v w : ℝ}
    (h : cellSideContact (a + k) (d + k) η (v + k) (w + k)) :
    cellSideContact a d (fun t => η (t + k)) v w := by
  intro p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  have hc : ∀ p : ℚ, ((p + k : ℚ) : ℝ) = (p : ℝ) + k := fun p => by rw [Rat.cast_add, Rat.cast_intCast]
  obtain ⟨K, hK, hK'⟩ := h (p₁ + k) (p₂ + k) (q₁ + k) (q₂ + k)
    (by rw [hc, hc]; exact ⟨by linarith [hv.1], by linarith [hv.2]⟩)
    (by rw [hc, hc]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)
    (by
      rw [hc, hc, hc, hc]
      exact Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 hdisj
        (show x - k ∈ Ioo (p₁ : ℝ) p₂ from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (show x - k ∈ Ioo (q₁ : ℝ) q₂ from ⟨by linarith [hx'.1], by linarith [hx'.2]⟩))
    (by
      rw [hc, hc]
      intro x hx
      have h' := hP (show x - k ∈ Icc (p₁ : ℝ) p₂ from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩)
    (by
      rw [hc, hc]
      intro x hx
      have h' := hQ (show x - k ∈ Icc (q₁ : ℝ) q₂ from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩)
  refine ⟨K, ?_, hK'⟩
  rw [image_comp_add_Icc, image_comp_add_Icc]
  rwa [hc, hc, hc, hc] at hK

theorem cellSideContact_comp_add_int_iff (k : ℤ) {a d : ℝ} {η : ℝ → ℂ} {v w : ℝ} :
    cellSideContact a d (fun t => η (t + k)) v w ↔ cellSideContact (a + k) (d + k) η (v + k) (w + k) :=
  ⟨cellSideContact_of_comp_add_int k, cellSideContact_comp_add_int k⟩

theorem mem_cellSideBranchTimes_comp_add_int (k : ℤ) {a b c d u : ℝ} {η : ℝ → ℂ} :
    u ∈ cellSideBranchTimes a b c d (fun t => η (t + k)) ↔
      u + k ∈ cellSideBranchTimes (a + k) (b + k) (c + k) (d + k) η := by
  simp only [cellSideBranchTimes, Set.mem_ofPred_eq, cellSideContact_comp_add_int_iff]
  constructor
  · rintro ⟨hu, s, hs, t, ht, h1, h2, h3⟩
    exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, s + k, ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      t + k, ⟨by linarith [ht.1], by linarith [ht.2]⟩, h1, h2, h3⟩
  · rintro ⟨hu, s, hs, t, ht, h1, h2, h3⟩
    refine ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, s - k, ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      t - k, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_, ?_, ?_⟩
    · rwa [sub_add_cancel]
    · rwa [sub_add_cancel]
    · rwa [sub_add_cancel, sub_add_cancel]

open Classical in
theorem cellSideCount_comp_add_int (k : ℤ) (a b c d : ℝ) (η : ℝ → ℂ) :
    cellSideCount a b c d (fun t => η (t + k)) = cellSideCount (a + k) (b + k) (c + k) (d + k) η := by
  have h1 : (cellSideBranchTimes a b c d (fun t => η (t + k))).Nonempty ↔
      (cellSideBranchTimes (a + k) (b + k) (c + k) (d + k) η).Nonempty :=
    ⟨fun ⟨u, hu⟩ => ⟨u + k, (mem_cellSideBranchTimes_comp_add_int k).1 hu⟩,
      fun ⟨u, hu⟩ => ⟨u - k, (mem_cellSideBranchTimes_comp_add_int k).2 (by rwa [sub_add_cancel])⟩⟩
  have h2 : (∃ u ∈ cellSideBranchTimes a b c d (fun t => η (t + k)),
        ∃ v ∈ cellSideBranchTimes a b c d (fun t => η (t + k)), u ≠ v) ↔
      (∃ u ∈ cellSideBranchTimes (a + k) (b + k) (c + k) (d + k) η,
        ∃ v ∈ cellSideBranchTimes (a + k) (b + k) (c + k) (d + k) η, u ≠ v) := by
    constructor
    · rintro ⟨u, hu, v, hv, huv⟩
      exact ⟨u + k, (mem_cellSideBranchTimes_comp_add_int k).1 hu, v + k,
        (mem_cellSideBranchTimes_comp_add_int k).1 hv, fun e => huv (add_right_cancel e)⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      exact ⟨u - k, (mem_cellSideBranchTimes_comp_add_int k).2 (by rwa [sub_add_cancel]), v - k,
        (mem_cellSideBranchTimes_comp_add_int k).2 (by rwa [sub_add_cancel]), fun e => huv (sub_left_inj.1 e)⟩
  unfold cellSideCount
  simp only [h1, h2]

/-- **An integer time shift of the curve relabels the frontier-side multiplicities**: the cells of the curve
`t ↦ η(t + k)` are the cells of `η` with the labels shifted by `k`. -/
theorem cellSideMult_comp_add_int (η : ℝ → ℂ) (k i j : ℤ) :
    cellSideMult 1 (fun t => η (t + k)) i j = cellSideMult 1 η (i + k) (j + k) := by
  have hC : cellSideCount ((1 : ℝ) * ((min i j : ℤ) - 1 : ℝ)) ((1 : ℝ) * (min i j : ℤ))
      ((1 : ℝ) * ((max i j : ℤ) - 1 : ℝ)) ((1 : ℝ) * (max i j : ℤ)) (fun t => η (t + k)) =
      cellSideCount ((1 : ℝ) * ((min (i + k) (j + k) : ℤ) - 1 : ℝ)) ((1 : ℝ) * (min (i + k) (j + k) : ℤ))
        ((1 : ℝ) * ((max (i + k) (j + k) : ℤ) - 1 : ℝ)) ((1 : ℝ) * (max (i + k) (j + k) : ℤ)) η := by
    rw [cellSideCount_comp_add_int, min_add_add_right, max_add_add_right]
    congr 1 <;> push_cast <;> ring
  have e1 : (i + k = j + k) ↔ i = j := add_left_inj k
  have e2 : i + k - (j + k) = i - j := by ring
  unfold cellSideMult
  rw [hC]
  simp only [e1, e2]

/-- **The polygonal configuration of a curve with the multiplicities read off the curve is invariant under an
integer time shift of the curve**: the curve `t ↦ q(t + k)` and its multiplicities are the relabelled datum. -/
theorem polygonalConfig_curveCode_shiftCurve (H₀ : GMSSpace) (k : ℤ) (q : C(ℝ, ℂ)) :
    polygonalConfig H₀ (shiftCurve k q, fun i j => cellSideMult 1 ⇑(shiftCurve k q) i j) =
      polygonalConfig H₀ (q, fun i j => cellSideMult 1 ⇑q i j) := by
  have h : (shiftCurve k q, fun i j => cellSideMult 1 ⇑(shiftCurve k q) i j) =
      shiftDatum k (q, fun i j => cellSideMult 1 ⇑q i j) :=
    Prod.ext rfl (funext fun i => funext fun j => cellSideMult_comp_add_int q k i j)
  rw [h, polygonalConfig_shiftDatum]

end CellSide

end MatedCRT.ZeroConePolygonal
