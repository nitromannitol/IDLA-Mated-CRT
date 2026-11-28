import MatedCRT.FirstPass.Derived.ZeroConePolygonalFanTri
import MatedCRT.FirstPass.Derived.ZeroConePolygonalConfig
import MatedCRT.FirstPass.Derived.ZeroConePolygonalDCC

/-!
# Matched patches of polygonal configurations are close in `d^CC`

The topology on cell configurations of Gwynne–Miller–Sheffield (arXiv:1807.07515v3, Definition 1.15
and (1.14)–(1.15), p. 15) is that of the pseudometric
`d^CC(H,H') = ∫₀^∞ e^{-r} ∧ inf_{f_r} {sup_z |z - f_r(z)| + max |c(H₁,H₂) - c'(f_r H₁, f_r H₂)|} dr`,
the infimum over homeomorphisms `f_r` of the plane taking the cells meeting the disk `B_r(0)` to cells
meeting it, preserving adjacency, and whose inverse does the same.

This file proves the comparison step of the Borel measurability of the polygonal cell configuration.
Let `w, w'` be valid unit-mesh data whose polygonal cells meeting the closed disk of radius `R` have
the same labels and conductances and are unions of the convex hulls of the same named faces, the faces
of `w` spanning vertices of single fan triangles of `w`, with the named vertices of `w'` within `b` of
those of `w` (`PatchMatch`). Moving the named vertices of the fan triangulation of `w` to their
counterparts and interpolating affinely on each fan triangle gives a homeomorphism `f` of the plane
moving points by at most `b` and carrying each matched cell of `w` onto the cell of `w'` with the same
label (`PatchMatch.exists_homeomorph`). At every radius `r ≤ R` at distance more than `b` from the
distances `dist(0, C_j)` of the matched cells, `f` is admissible with distortion at most `b`
(`PatchMatch.admissibleAt`, `PatchMatch.distortion_le`). Integrating,
`d^CC(H_w, H_{w'}) ≤ R b + 2 b |L| + e^{-R}` (`PatchMatch.dCC_le`).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

/-! ## Elementary facts -/

/-- The underlying configuration of the polygonal configuration of a valid datum. -/
theorem polygonalConfig_val {H₀ : GMSSpace} {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (h : UnitMeshValid w) :
    (polygonalConfig H₀ w).1 = (polygonalInputOf w).cellConfig := by
  rw [polygonalConfig_of_valid h]
  rfl

theorem infDist_lt_of_inter_ball {s : Set Plane} {r : ℝ} (h : (s ∩ ball 0 r).Nonempty) :
    infDist 0 s < r := by
  obtain ⟨y, hys, hyr⟩ := h
  rw [mem_ball, dist_comm] at hyr
  exact (infDist_le_dist_of_mem hys).trans_lt hyr

theorem nonempty_inter_ball_of_infDist_lt {s : Set Plane} {r : ℝ} (hs : s.Nonempty)
    (h : infDist 0 s < r) : (s ∩ ball 0 r).Nonempty := by
  obtain ⟨y, hy, hyd⟩ := (infDist_lt_iff hs).1 h
  exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hyd⟩

/-- A map moving points by at most `b` takes a set at distance `< r - b` from the origin to a set
meeting the open disk of radius `r`. -/
theorem nonempty_image_inter_ball {f : Plane → Plane} {b r : ℝ} (hf : ∀ x, dist x (f x) ≤ b)
    {s : Set Plane} (hs : s.Nonempty) (h : infDist 0 s < r - b) : (f '' s ∩ ball 0 r).Nonempty := by
  obtain ⟨y, hy, hyd⟩ := (infDist_lt_iff hs).1 h
  refine ⟨f y, mem_image_of_mem f hy, ?_⟩
  rw [mem_ball, dist_comm]
  have h1 := dist_triangle 0 y (f y)
  have h2 := hf y
  linarith

theorem symm_image_image_homeomorph (f : Plane ≃ₜ Plane) (s : Set Plane) : f.symm '' (f '' s) = s := by
  rw [image_image]
  simp

theorem lt_sub_of_lt_abs_sub {a r b : ℝ} (h : b < |r - a|) (har : a < r + b) : a < r - b := by
  rcases le_or_gt 0 (r - a) with h0 | h0
  · rw [abs_of_nonneg h0] at h
    linarith
  · rw [abs_of_neg h0] at h
    linarith

/-- A map agreeing with the affine interpolation on each triangle of a triangulation maps the convex
hull of a set of points of one triangle onto the convex hull of their images. -/
theorem image_convexHull_of_subset_tri {ι : Type*} {p : ι → Fin 3 → Plane} {σ : Plane → Plane}
    {f : Plane → Plane} (hf : ∀ i, ∀ x ∈ tri p i, f x = triInterp p σ i x) {i : ι}
    {P : Set Plane} (hP : P ⊆ tri p i) : f '' convexHull ℝ P = convexHull ℝ (f '' P) := by
  have hsub : convexHull ℝ P ⊆ tri p i := convexHull_min hP (convex_tri i)
  rw [image_congr fun x hx => hf i x (hsub hx), AffineMap.image_convexHull,
    image_congr fun x hx => (hf i x (hP hx)).symm]

/-- **The heights of the fan triangles with a vertex in a finite set are bounded below**: only
finitely many fan triangles contain a given point. -/
theorem IsSiteSystem.exists_le_minHeight {V : Set Plane} {r : Plane → ℝ} (hV : IsSiteSystem V r)
    {P : Set Plane} (hP : P.Finite) :
    ∃ h : ℝ, 0 < h ∧ ∀ i : FanIndex V, (∃ k, fanTri V i k ∈ P) →
      h ≤ minHeight (fanTri V i 0) (fanTri V i 1) (fanTri V i 2) := by
  have hT := hV.isTriangulation_fanTri
  have hfin : {i : FanIndex V | ∃ k, fanTri V i k ∈ P}.Finite := by
    refine (hP.biUnion fun x _ => hT.locallyFinite.point_finite x).subset ?_
    rintro i ⟨k, hk⟩
    have hv : fanTri V i k ∈ ({fanTri V i 0, fanTri V i 1, fanTri V i 2} : Set Plane) := by
      fin_cases k <;> simp
    exact mem_iUnion₂.2 ⟨_, hk, subset_convexHull ℝ _ hv⟩
  by_cases hne : hfin.toFinset.Nonempty
  · obtain ⟨i₀, -, hmin⟩ := hfin.toFinset.exists_min_image
      (fun i => minHeight (fanTri V i 0) (fanTri V i 1) (fanTri V i 2)) hne
    exact ⟨_, minHeight_pos (hT.nondeg i₀), fun i hi => hmin i (hfin.mem_toFinset.2 hi)⟩
  · exact ⟨1, one_pos, fun i hi => absurd ⟨i, hfin.mem_toFinset.2 hi⟩ hne⟩

/-! ## The displacement of the named vertices -/

section Disp

variable {N : Type*}

open Classical in
/-- **The vertex displacement of a matching**: `pos a ↦ pos' a - pos a` at the named points `a ∈ S`,
and `0` elsewhere. -/
def matchDisp (S : Set N) (pos pos' : N → Plane) (x : Plane) : Plane :=
  if hx : ∃ a ∈ S, pos a = x then pos' hx.choose - x else 0

variable {S : Set N} {pos pos' : N → Plane}

theorem matchDisp_apply (hinj : S.InjOn pos) {a : N} (ha : a ∈ S) :
    matchDisp S pos pos' (pos a) = pos' a - pos a := by
  have hx : ∃ a' ∈ S, pos a' = pos a := ⟨a, ha, rfl⟩
  rw [matchDisp, dite_eq_left hx, hinj hx.choose_spec.1 ha hx.choose_spec.2]

theorem matchDisp_eq_zero {x : Plane} (hx : x ∉ pos '' S) : matchDisp S pos pos' x = 0 := by
  have h : ¬ ∃ a ∈ S, pos a = x := fun ⟨a, ha, hax⟩ => hx ⟨a, ha, hax⟩
  rw [matchDisp, dite_eq_right h]

theorem norm_matchDisp_le {b : ℝ} (hb : 0 ≤ b) (hd : ∀ a ∈ S, dist (pos a) (pos' a) ≤ b)
    (x : Plane) : ‖matchDisp S pos pos' x‖ ≤ b := by
  unfold matchDisp
  split_ifs with hx
  · obtain ⟨h1, h2⟩ := hx.choose_spec
    calc ‖pos' hx.choose - x‖ = dist (pos hx.choose) (pos' hx.choose) := by
          rw [h2, dist_comm, dist_eq_norm]
      _ ≤ b := hd _ h1
  · rw [norm_zero]
    exact hb

end Disp

/-! ## Matched patches -/

variable {N : Type*} {w w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {R b : ℝ} {L : Finset ℤ} {S : Set N}
  {pos pos' : N → Plane} {Φ : ℤ → Set (Set N)}

/-- **Matched patches of two valid data** up to radius `R` with vertex displacement at most `b`. The
polygonal cells of `w` and of `w'` meeting the closed disk of radius `R` have labels in `L`; for
`j ∈ L` the cells `C_j` of `w` and of `w'` are the unions of the convex hulls of the named faces
`F ∈ Φ j`, placed by `pos` and by `pos'` respectively; each face of `w` spans vertices of one fan
triangle of `w`; the named points `S` are placed injectively by `pos` and moved by at most `b`; and
the conductances agree on `L`. -/
structure PatchMatch (w w' : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (R b : ℝ) (L : Finset ℤ) (S : Set N)
    (pos pos' : N → Plane) (Φ : ℤ → Set (Set N)) : Prop where
  valid : UnitMeshValid w
  valid' : UnitMeshValid w'
  mem_labels : ∀ j, ((polygonalInputOf w).cell j ∩ closedBall 0 R).Nonempty → j ∈ L
  mem_labels' : ∀ j, ((polygonalInputOf w').cell j ∩ closedBall 0 R).Nonempty → j ∈ L
  cell_eq : ∀ j ∈ L, (polygonalInputOf w).cell j = ⋃ F ∈ Φ j, convexHull ℝ (pos '' F)
  cell_eq' : ∀ j ∈ L, (polygonalInputOf w').cell j = ⋃ F ∈ Φ j, convexHull ℝ (pos' '' F)
  face : ∀ j ∈ L, ∀ F ∈ Φ j, F ⊆ S ∧ ∃ i : FanIndex (polygonalInputOf w).V,
    pos '' F ⊆ {fanTri _ i 0, fanTri _ i 1, fanTri _ i 2}
  injOn : S.InjOn pos
  dist_le : ∀ a ∈ S, dist (pos a) (pos' a) ≤ b
  cond : ∀ j ∈ L, ∀ k ∈ L, w.2 j k = w'.2 j k

namespace PatchMatch

/-- **The matching homeomorphism**: the piecewise affine homeomorphism of the plane interpolating the
displacement of the named vertices on the fan triangles of `w`. It moves points by at most `b` (as
does its inverse) and carries each matched cell of `w` onto the cell of `w'` with the same label. -/
theorem exists_homeomorph (hM : PatchMatch w w' R b L S pos pos' Φ) (hb : 0 ≤ b) {h : ℝ}
    (hh : 0 < h)
    (hmin : ∀ i : FanIndex (polygonalInputOf w).V, (∃ k, fanTri _ i k ∈ pos '' S) →
      h ≤ minHeight (fanTri _ i 0) (fanTri _ i 1) (fanTri _ i 2))
    (hbh : 4 * b < h) :
    ∃ f : Plane ≃ₜ Plane, (∀ x, dist x (f x) ≤ b) ∧ (∀ y, dist y (f.symm y) ≤ b) ∧
      ∀ j ∈ L, f '' (polygonalInputOf w).cell j = (polygonalInputOf w').cell j := by
  have hV := hM.valid.isSiteSystem
  have hT := hV.isTriangulation_fanTri
  obtain ⟨f, hf, hfd, hfd', -⟩ := exists_homeomorph_piecewiseAffine_of_le_minHeight hT
    (matchDisp S pos pos') hh (fun _ _ => norm_matchDisp_le hb hM.dist_le _)
    (fun i ⟨k, hk⟩ => hmin i ⟨k, by by_contra hn; exact hk (matchDisp_eq_zero hn)⟩) hbh
  refine ⟨f, hfd, hfd', fun j hj => ?_⟩
  rw [hM.cell_eq j hj, hM.cell_eq' j hj, image_iUnion₂]
  refine iUnion₂_congr fun F hF => ?_
  obtain ⟨hFS, i, hi⟩ := hM.face j hj F hF
  have hsub : pos '' F ⊆ tri (fanTri (polygonalInputOf w).V) i :=
    hi.trans (subset_convexHull ℝ _)
  rw [image_convexHull_of_subset_tri hf hsub, image_image]
  congr 1
  refine image_congr fun a ha => ?_
  show (f : Plane → Plane) (pos a) = pos' a
  have hv : pos a ∈ ({fanTri _ i 0, fanTri _ i 1, fanTri _ i 2} : Set Plane) :=
    hi (mem_image_of_mem pos ha)
  rw [hf i _ (subset_convexHull ℝ _ hv), triInterp_vertex hT _ i hv,
    matchDisp_apply hM.injOn (hFS ha)]
  abel

theorem nonempty_cell (hM : PatchMatch w w' R b L S pos pos' Φ) (j : ℤ) :
    ((polygonalInputOf w).cell j).Nonempty :=
  ⟨_, (isValid_polygonalInputOf hM.valid).v_mem_cell j⟩

theorem nonempty_cell' (hM : PatchMatch w w' R b L S pos pos' Φ) (j : ℤ) :
    ((polygonalInputOf w').cell j).Nonempty :=
  ⟨_, (isValid_polygonalInputOf hM.valid').v_mem_cell j⟩

/-- The matching homeomorphism carries the `j`-th cell of `w` to the `j`-th cell of `w'`. -/
theorem mapCell_cellNC (hM : PatchMatch w w' R b L S pos pos' Φ) {f : Plane ≃ₜ Plane}
    (hfc : ∀ j ∈ L, f '' (polygonalInputOf w).cell j = (polygonalInputOf w').cell j) {j : ℤ}
    (hj : j ∈ L) :
    CellConfig.mapCell f ((polygonalInputOf w).cellNC j) = (polygonalInputOf w').cellNC j := by
  apply TopologicalSpace.NonemptyCompacts.ext
  show f '' ((polygonalInputOf w).cellNC j : Set Plane) = ((polygonalInputOf w').cellNC j : Set Plane)
  rw [(isValid_polygonalInputOf hM.valid).coe_cellNC,
    (isValid_polygonalInputOf hM.valid').coe_cellNC]
  exact hfc j hj

theorem mapCell_symm_cellNC (hM : PatchMatch w w' R b L S pos pos' Φ) {f : Plane ≃ₜ Plane}
    (hfc : ∀ j ∈ L, f '' (polygonalInputOf w).cell j = (polygonalInputOf w').cell j) {j : ℤ}
    (hj : j ∈ L) :
    CellConfig.mapCell f.symm ((polygonalInputOf w').cellNC j) = (polygonalInputOf w).cellNC j := by
  apply TopologicalSpace.NonemptyCompacts.ext
  show f.symm '' ((polygonalInputOf w').cellNC j : Set Plane) =
    ((polygonalInputOf w).cellNC j : Set Plane)
  rw [(isValid_polygonalInputOf hM.valid).coe_cellNC,
    (isValid_polygonalInputOf hM.valid').coe_cellNC, ← hfc j hj, symm_image_image_homeomorph]

/-- **Admissibility of the matching homeomorphism** at every radius `r ≤ R` at distance more than
`b` from the distances `dist(0, C_j)` of the matched cells of `w`: a cell meets `B_r(0)` exactly when
its image does, and the conductances are those of the labels. -/
theorem admissibleAt (hM : PatchMatch w w' R b L S pos pos' Φ) (H₀ : GMSSpace) (hb : 0 ≤ b)
    {f : Plane ≃ₜ Plane} (hfd : ∀ x, dist x (f x) ≤ b) (hfd' : ∀ y, dist y (f.symm y) ≤ b)
    (hfc : ∀ j ∈ L, f '' (polygonalInputOf w).cell j = (polygonalInputOf w').cell j) {r : ℝ}
    (hrR : r ≤ R) (hgap : ∀ j ∈ L, b < |r - infDist 0 ((polygonalInputOf w).cell j)|) :
    CellConfig.AdmissibleAt (polygonalConfig H₀ w).1 (polygonalConfig H₀ w').1 r f := by
  have hI := isValid_polygonalInputOf hM.valid
  have hI' := isValid_polygonalInputOf hM.valid'
  have hball : ball (0 : Plane) r ⊆ closedBall 0 R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hrR)
  have hfwd : ∀ j ∈ L, ((polygonalInputOf w).cell j ∩ ball 0 r).Nonempty →
      ((polygonalInputOf w').cell j ∩ ball 0 r).Nonempty := by
    intro j hj hne
    have h1 := infDist_lt_of_inter_ball hne
    have h2 := lt_sub_of_lt_abs_sub (hgap j hj) (by linarith)
    rw [← hfc j hj]
    exact nonempty_image_inter_ball hfd (hM.nonempty_cell j) h2
  have hbwd : ∀ j ∈ L, ((polygonalInputOf w').cell j ∩ ball 0 r).Nonempty →
      ((polygonalInputOf w).cell j ∩ ball 0 r).Nonempty := by
    intro j hj hne
    have h1 : infDist 0 ((polygonalInputOf w').cell j) < r + b - b := by
      rw [add_sub_cancel_right]
      exact infDist_lt_of_inter_ball hne
    have h2 := nonempty_image_inter_ball hfd' (hM.nonempty_cell' j) h1
    rw [← hfc j hj, symm_image_image_homeomorph] at h2
    have h3 := lt_sub_of_lt_abs_sub (hgap j hj) (infDist_lt_of_inter_ball h2)
    exact nonempty_inter_ball_of_infDist_lt (hM.nonempty_cell j) (by linarith)
  rw [polygonalConfig_val hM.valid, polygonalConfig_val hM.valid']
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro K ⟨⟨j, rfl⟩, hK⟩
    rw [hI.coe_cellNC] at hK
    have hj := hM.mem_labels j (hK.mono (inter_subset_inter_right _ hball))
    rw [hM.mapCell_cellNC hfc hj]
    refine ⟨⟨j, rfl⟩, ?_⟩
    rw [hI'.coe_cellNC]
    exact hfwd j hj hK
  · rintro K ⟨⟨j, rfl⟩, hK⟩
    rw [hI'.coe_cellNC] at hK
    have hj := hM.mem_labels' j (hK.mono (inter_subset_inter_right _ hball))
    rw [hM.mapCell_symm_cellNC hfc hj]
    refine ⟨⟨j, rfl⟩, ?_⟩
    rw [hI.coe_cellNC]
    exact hbwd j hj hK
  · rintro K ⟨⟨j, rfl⟩, hK⟩ K' ⟨⟨k, rfl⟩, hK'⟩ hadj
    rw [hI.coe_cellNC] at hK hK'
    have hj := hM.mem_labels j (hK.mono (inter_subset_inter_right _ hball))
    have hk := hM.mem_labels k (hK'.mono (inter_subset_inter_right _ hball))
    rw [hM.mapCell_cellNC hfc hj, hM.mapCell_cellNC hfc hk]
    have hadj' : 0 < (polygonalInputOf w).cellConfig.c ((polygonalInputOf w).cellNC j)
        ((polygonalInputOf w).cellNC k) := hadj
    rw [hI.cellConfig_c] at hadj'
    show 0 < (polygonalInputOf w').cellConfig.c ((polygonalInputOf w').cellNC j)
      ((polygonalInputOf w').cellNC k)
    rw [hI'.cellConfig_c]
    show (0 : ℝ) < (w'.2 j k : ℝ)
    rw [← hM.cond j hj k hk]
    exact hadj'
  · rintro K ⟨⟨j, rfl⟩, hK⟩ K' ⟨⟨k, rfl⟩, hK'⟩ hadj
    rw [hI'.coe_cellNC] at hK hK'
    have hj := hM.mem_labels' j (hK.mono (inter_subset_inter_right _ hball))
    have hk := hM.mem_labels' k (hK'.mono (inter_subset_inter_right _ hball))
    rw [hM.mapCell_symm_cellNC hfc hj, hM.mapCell_symm_cellNC hfc hk]
    have hadj' : 0 < (polygonalInputOf w').cellConfig.c ((polygonalInputOf w').cellNC j)
        ((polygonalInputOf w').cellNC k) := hadj
    rw [hI'.cellConfig_c] at hadj'
    show 0 < (polygonalInputOf w).cellConfig.c ((polygonalInputOf w).cellNC j)
      ((polygonalInputOf w).cellNC k)
    rw [hI.cellConfig_c]
    show (0 : ℝ) < (w.2 j k : ℝ)
    rw [hM.cond j hj k hk]
    exact hadj'

/-- **The distortion of the matching homeomorphism** at a radius `r ≤ R` is at most `b`: it moves
points by at most `b`, and the conductances of matched cells are equal. -/
theorem distortion_le (hM : PatchMatch w w' R b L S pos pos' Φ) (H₀ : GMSSpace)
    {f : Plane ≃ₜ Plane} (hfd : ∀ x, dist x (f x) ≤ b)
    (hfc : ∀ j ∈ L, f '' (polygonalInputOf w).cell j = (polygonalInputOf w').cell j) {r : ℝ}
    (hrR : r ≤ R) :
    CellConfig.distortion (polygonalConfig H₀ w).1 (polygonalConfig H₀ w').1 r f ≤
      ENNReal.ofReal b := by
  have hI := isValid_polygonalInputOf hM.valid
  have hI' := isValid_polygonalInputOf hM.valid'
  have hball : ball (0 : Plane) r ⊆ closedBall 0 R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hrR)
  rw [polygonalConfig_val hM.valid, polygonalConfig_val hM.valid']
  unfold CellConfig.distortion
  rw [← add_zero (ENNReal.ofReal b)]
  refine add_le_add (iSup_le fun z => ?_)
    (iSup₂_le fun K hK => iSup₂_le fun K' hK' => iSup_le fun _ => ?_)
  · rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hfd z)
  · obtain ⟨⟨j, rfl⟩, hKn⟩ := hK
    obtain ⟨⟨k, rfl⟩, hK'n⟩ := hK'
    rw [hI.coe_cellNC] at hKn hK'n
    have hj := hM.mem_labels j (hKn.mono (inter_subset_inter_right _ hball))
    have hk := hM.mem_labels k (hK'n.mono (inter_subset_inter_right _ hball))
    rw [hM.mapCell_cellNC hfc hj, hM.mapCell_cellNC hfc hk, hI.cellConfig_c, hI'.cellConfig_c]
    show ENNReal.ofReal |((w.2 j k : ℕ) : ℝ) - ((w'.2 j k : ℕ) : ℝ)| ≤ 0
    rw [hM.cond j hj k hk, sub_self, abs_zero, ENNReal.ofReal_zero]

end PatchMatch

/-! ## The integral bound -/

/-- The radii within `b` of the numbers `a j`, `j ∈ L`. -/
def radiusGapSet (L : Finset ℤ) (a : ℤ → ℝ) (b : ℝ) : Set ℝ := ⋃ j ∈ L, Icc (a j - b) (a j + b)

theorem measurableSet_radiusGapSet (L : Finset ℤ) (a : ℤ → ℝ) (b : ℝ) :
    MeasurableSet (radiusGapSet L a b) :=
  Finset.measurableSet_biUnion L fun _ _ => measurableSet_Icc

theorem volume_radiusGapSet_le (L : Finset ℤ) (a : ℤ → ℝ) (b : ℝ) :
    volume (radiusGapSet L a b) ≤ L.card * ENNReal.ofReal (2 * b) := by
  refine (measure_biUnion_finset_le L _).trans ?_
  have h : ∀ j, a j + b - (a j - b) = 2 * b := fun j => by ring
  simp only [Real.volume_Icc, h, Finset.sum_const, nsmul_eq_mul, le_refl]

theorem lt_abs_of_notMem_radiusGapSet {L : Finset ℤ} {a : ℤ → ℝ} {b r : ℝ}
    (h : r ∉ radiusGapSet L a b) {j : ℤ} (hj : j ∈ L) : b < |r - a j| := by
  by_contra hle
  have h1 := abs_le.1 (not_lt.1 hle)
  exact h (mem_iUnion₂.2 ⟨j, hj, ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩⟩)

/-- The bound for the integrand of `d^CC`: `b` on `(0, R]`, `1` on the exceptional radii `B`, and
`e^{-r}` beyond `R`. -/
def matchBound (R b : ℝ) (B : Set ℝ) (r : ℝ) : ℝ≥0∞ :=
  (Ioc 0 R).indicator (fun _ => ENNReal.ofReal b) r + B.indicator 1 r +
    (Ioi R).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r

theorem lintegral_matchBound {R b : ℝ} (hb : 0 ≤ b) {B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ r, matchBound R b B r =
      ENNReal.ofReal (R * b) + volume B + ENNReal.ofReal (Real.exp (-R)) := by
  have hA : Measurable ((Ioc 0 R).indicator fun _ : ℝ => ENNReal.ofReal b) :=
    measurable_const.indicator measurableSet_Ioc
  have hB' : Measurable (B.indicator (1 : ℝ → ℝ≥0∞)) := measurable_const.indicator hB
  have hAB : Measurable fun r => (Ioc 0 R).indicator (fun _ => ENNReal.ofReal b) r + B.indicator 1 r :=
    hA.add hB'
  unfold matchBound
  rw [lintegral_add_left hAB, lintegral_add_left hA,
    lintegral_indicator_const measurableSet_Ioc, lintegral_indicator_one hB,
    lintegral_indicator measurableSet_Ioi, ReflectedGMS.GeomTop.GMSTopology.lintegral_exp_neg_Ioi,
    Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hb, mul_comm b R]

namespace PatchMatch

/-- **The integrand of `d^CC` is at most `matchBound`**: `e^{-r}` beyond `R` and on the exceptional
radii, and the distortion `b` of the matching homeomorphism at the other radii of `(0, R]`. -/
theorem integrand_le (hM : PatchMatch w w' R b L S pos pos' Φ) (H₀ : GMSSpace) (hb : 0 ≤ b)
    {f : Plane ≃ₜ Plane} (hfd : ∀ x, dist x (f x) ≤ b) (hfd' : ∀ y, dist y (f.symm y) ≤ b)
    (hfc : ∀ j ∈ L, f '' (polygonalInputOf w).cell j = (polygonalInputOf w').cell j) {r : ℝ}
    (hr : 0 < r) :
    min (ENNReal.ofReal (Real.exp (-r)))
        (⨅ (g : Plane ≃ₜ Plane) (_ : CellConfig.AdmissibleAt (polygonalConfig H₀ w).1
          (polygonalConfig H₀ w').1 r g),
          CellConfig.distortion (polygonalConfig H₀ w).1 (polygonalConfig H₀ w').1 r g) ≤
      matchBound R b (radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b) r := by
  unfold matchBound
  by_cases hrR : R < r
  · calc min _ _ ≤ ENNReal.ofReal (Real.exp (-r)) := min_le_left _ _
      _ = (Ioi R).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r :=
          (indicator_of_mem (show r ∈ Ioi R from hrR) (fun r => ENNReal.ofReal (Real.exp (-r)))).symm
      _ ≤ _ := le_add_self
  · have hrR' : r ≤ R := not_lt.1 hrR
    by_cases hrb : r ∈ radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b
    · calc min _ _ ≤ ENNReal.ofReal (Real.exp (-r)) := min_le_left _ _
        _ ≤ 1 := ReflectedGMS.GeomTop.GMSTopology.ofReal_exp_neg_le_one hr.le
        _ = (radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b).indicator 1 r :=
            (indicator_of_mem hrb (1 : ℝ → ℝ≥0∞)).symm
        _ ≤ _ := le_add_self.trans le_self_add
    · have hgap : ∀ j ∈ L, b < |r - infDist 0 ((polygonalInputOf w).cell j)| := fun j hj =>
        lt_abs_of_notMem_radiusGapSet hrb hj
      calc min _ _ ≤ _ := min_le_right _ _
        _ ≤ CellConfig.distortion (polygonalConfig H₀ w).1 (polygonalConfig H₀ w').1 r f :=
            iInf₂_le f (hM.admissibleAt H₀ hb hfd hfd' hfc hrR' hgap)
        _ ≤ ENNReal.ofReal b := hM.distortion_le H₀ hfd hfc hrR'
        _ = (Ioc 0 R).indicator (fun _ => ENNReal.ofReal b) r :=
            (indicator_of_mem (show r ∈ Ioc 0 R from ⟨hr, hrR'⟩) (fun _ => ENNReal.ofReal b)).symm
        _ ≤ _ := le_self_add.trans le_self_add

/-- **Matched patches are close in `d^CC`**: `d^CC(H_w, H_{w'}) ≤ R b + 2 b |L| + e^{-R}`, where `b`
bounds the displacement of the named vertices and is small compared with the heights of the fan
triangles of `w` with a named vertex. -/
theorem dCC_le (hM : PatchMatch w w' R b L S pos pos' Φ) (H₀ : GMSSpace) (hb : 0 ≤ b) {h : ℝ}
    (hh : 0 < h)
    (hmin : ∀ i : FanIndex (polygonalInputOf w).V, (∃ k, fanTri _ i k ∈ pos '' S) →
      h ≤ minHeight (fanTri _ i 0) (fanTri _ i 1) (fanTri _ i 2))
    (hbh : 4 * b < h) :
    CellConfig.dCC (polygonalConfig H₀ w).1 (polygonalConfig H₀ w').1 ≤
      ENNReal.ofReal (R * b) + L.card * ENNReal.ofReal (2 * b) +
        ENNReal.ofReal (Real.exp (-R)) := by
  obtain ⟨f, hfd, hfd', hfc⟩ := hM.exists_homeomorph hb hh hmin hbh
  have hB := measurableSet_radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b
  calc CellConfig.dCC (polygonalConfig H₀ w).1 (polygonalConfig H₀ w').1
      ≤ ∫⁻ r in Ioi (0 : ℝ), matchBound R b
          (radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b) r :=
        setLIntegral_mono' measurableSet_Ioi fun r hr =>
          hM.integrand_le H₀ hb hfd hfd' hfc hr
    _ ≤ ∫⁻ r, matchBound R b
          (radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b) r :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (R * b) +
          volume (radiusGapSet L (fun j => infDist 0 ((polygonalInputOf w).cell j)) b) +
          ENNReal.ofReal (Real.exp (-R)) := lintegral_matchBound hb hB
    _ ≤ _ := by
        gcongr
        exact volume_radiusGapSet_le L _ b

end PatchMatch

end MatedCRT.ZeroConePolygonal
