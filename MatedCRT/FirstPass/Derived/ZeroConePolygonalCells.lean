import MatedCRT.FirstPass.Derived.ZeroConePolygonalVoronoi

/-!
# The polygonal cells

The construction of the written answer `notes/fp-gaps/CODEX-MQ-sbl-32.md` (lines 23-27). The input
(`PolygonalInput`) is a family of old cells `K_j` (`j ∈ ℤ`) with integer edge counts `m`, embedded vertices
`v_j ∈ K_j`, a locally finite set `V` of sites containing every `v_j` which is dense relative to a scale
function `r` (`IsSiteSystem`), and weights `e_j`.

* `labels p`: the labels `j` whose old cell `K_j` meets the Voronoi tile `Q_p`.
* `owner p`: the label of least weight among them, ties broken by the label (answer, line 23: "Give the
  whole tile to the label of smallest `e_j` among them, breaking ties by chronological order").
* `piece p j`: the whole tile `Q_p` for its owner, and the shared piece `S_p` (frontier and axis chords
  through `p`) for every other label meeting the tile.
* `cell j`: the polygonal cell `C_j = ⋃_{p : K_j ∩ Q_p ≠ ∅} piece p j`.

Under `PolygonalInput.IsValid` (the old cells are compact, connected, locally finite, cover the plane, the
labels through every point are connected by edges of positive count, the counts are symmetric with
adjacent old cells meeting, and every label owns a tile) the polygonal cells are compact, connected, have
interior, cover the plane, are locally finite, pairwise distinct, overlap in null sets, adjacent cells meet,
`v_j ∈ C_j`, every point of `K_j` is within the diameter of a cell through it of `C_j`, and the labels
through every point are connected by edges of positive count (answer, line 27).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology Relation
open scoped RealInnerProductSpace

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-! ## Closed covers of connected sets -/

/-- **Closed covers of a connected set** (answer, line 9: "Otherwise two disjoint groups would give closed
covers of `Q` that must overlap"). Let finitely many closed sets `A i` (`i ∈ S`) cover a preconnected
set `L`, each meeting `L`, and let any two indices whose sets share a point of `L` be joined by a chain of
`R`. Then any two indices of `S` are joined by a chain of `R`. -/
theorem reflTransGen_of_closed_cover {X ι : Type*} [TopologicalSpace X] {L : Set X}
    (hL : IsPreconnected L) {S : Set ι} (hS : S.Finite) {A : ι → Set X}
    (hA : ∀ i ∈ S, IsClosed (A i)) (hcov : L ⊆ ⋃ i ∈ S, A i)
    (hmeet : ∀ i ∈ S, (A i ∩ L).Nonempty) (R : ι → ι → Prop)
    (hpt : ∀ z ∈ L, ∀ i ∈ S, ∀ j ∈ S, z ∈ A i → z ∈ A j → ReflTransGen R i j) :
    ∀ i ∈ S, ∀ j ∈ S, ReflTransGen R i j := by
  intro i hi j hj
  by_contra hij
  have hT : IsClosed (⋃ k ∈ {k | k ∈ S ∧ ReflTransGen R i k}, A k) :=
    (hS.subset fun _ hk => hk.1).isClosed_biUnion fun k hk => hA k hk.1
  have hT' : IsClosed (⋃ k ∈ {k | k ∈ S ∧ ¬ ReflTransGen R i k}, A k) :=
    (hS.subset fun _ hk => hk.1).isClosed_biUnion fun k hk => hA k hk.1
  have hcov' : L ⊆ (⋃ k ∈ {k | k ∈ S ∧ ReflTransGen R i k}, A k) ∪
      (⋃ k ∈ {k | k ∈ S ∧ ¬ ReflTransGen R i k}, A k) := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (hcov hz)
    by_cases hkT : ReflTransGen R i k
    · exact Or.inl (mem_iUnion₂.2 ⟨k, ⟨hk, hkT⟩, hzk⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨k, ⟨hk, hkT⟩, hzk⟩)
  have h1 : (L ∩ ⋃ k ∈ {k | k ∈ S ∧ ReflTransGen R i k}, A k).Nonempty := by
    obtain ⟨z, hz, hzL⟩ := hmeet i hi
    exact ⟨z, hzL, mem_iUnion₂.2 ⟨i, ⟨hi, ReflTransGen.refl⟩, hz⟩⟩
  have h2 : (L ∩ ⋃ k ∈ {k | k ∈ S ∧ ¬ ReflTransGen R i k}, A k).Nonempty := by
    obtain ⟨z, hz, hzL⟩ := hmeet j hj
    exact ⟨z, hzL, mem_iUnion₂.2 ⟨j, ⟨hj, hij⟩, hz⟩⟩
  obtain ⟨z, hzL, hz1, hz2⟩ := isPreconnected_closed_iff.1 hL _ _ hT hT' hcov' h1 h2
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hz1
  obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 hz2
  exact hb.2 (ha.2.trans (hpt z hzL a ha.1 b hb.1 hza hzb))

/-! ## The input of the construction -/

/-- **The input of the polygonal construction**: old cells `K_j` with edge counts `m` and vertices `v_j`,
sites `V` with a scale function `r`, and weights `e_j` for the owner rule. -/
structure PolygonalInput where
  /-- The old cells. -/
  K : ℤ → Set Plane
  /-- The edge counts. -/
  m : ℤ → ℤ → ℕ
  /-- The embedded vertices. -/
  v : ℤ → Plane
  /-- The sites. -/
  V : Set Plane
  /-- The scale function. -/
  r : Plane → ℝ
  /-- The weights of the owner rule. -/
  e : ℤ → ℝ

namespace PolygonalInput

variable (I : PolygonalInput)

/-- The labels whose old cell meets the tile of `p`. -/
def labels (p : Plane) : Set ℤ := {j | (I.K j ∩ tile I.V p).Nonempty}

/-- `j` is the owner of the tile of `p`: a label meeting it of least weight, ties broken by the label. -/
def IsOwner (p : Plane) (j : ℤ) : Prop :=
  j ∈ I.labels p ∧ ∀ i ∈ I.labels p, toLex (I.e j, j) ≤ toLex (I.e i, i)

/-- **The owner of the tile of `p`** (answer, line 23). -/
def owner (p : Plane) : ℤ := Classical.epsilon (I.IsOwner p)

/-- **The piece of the tile of `p` given to the label `j`**: the whole tile for its owner, the shared
piece (frontier and axis chords through `p`) for every other label. -/
def piece (p : Plane) (j : ℤ) : Set Plane := if I.owner p = j then tile I.V p else shared I.V p

/-- The sites whose tile meets the old cell `K_j`. -/
def sitesOf (j : ℤ) : Set Plane := {p | p ∈ I.V ∧ j ∈ I.labels p}

/-- **The polygonal cell** `C_j` (answer, line 23: "Let `C_j` be the union of the pieces given to label
`j`"). -/
def cell (j : ℤ) : Set Plane := ⋃ p ∈ I.sitesOf j, I.piece p j

/-- **Validity of the input.** -/
structure IsValid : Prop where
  site : IsSiteSystem I.V I.r
  compact : ∀ j, IsCompact (I.K j)
  conn : ∀ j, IsPreconnected (I.K j)
  lf : ∀ A : Set Plane, IsCompact A → {j | (I.K j ∩ A).Nonempty}.Finite
  cover : ∀ z, ∃ j, z ∈ I.K j
  pt : ∀ z i j, z ∈ I.K i → z ∈ I.K j →
    ReflTransGen (fun a b => 0 < I.m a b ∧ z ∈ I.K a ∧ z ∈ I.K b) i j
  m_symm : ∀ i j, I.m i j = I.m j i
  m_inter : ∀ i j, 0 < I.m i j → (I.K i ∩ I.K j).Nonempty
  vsite : ∀ j, I.v j ∈ I.V
  vmem : ∀ j, I.v j ∈ I.K j
  own : ∀ j, ∃ p ∈ I.V, I.owner p = j

variable {I}

theorem IsValid.finite_labels (hI : I.IsValid) (p : Plane) : (I.labels p).Finite :=
  hI.lf _ (hI.site.isCompact_tile p)

theorem IsValid.labels_nonempty (hI : I.IsValid) (p : Plane) : (I.labels p).Nonempty := by
  obtain ⟨j, hj⟩ := hI.cover p
  exact ⟨j, p, hj, self_mem_tile I.V p⟩

theorem IsValid.exists_isOwner (hI : I.IsValid) (p : Plane) : ∃ j, I.IsOwner p j := by
  obtain ⟨j₀, hj₀⟩ := hI.labels_nonempty p
  have hfin := hI.finite_labels p
  obtain ⟨j, hj, hmin⟩ := hfin.toFinset.exists_min_image (fun j => toLex (I.e j, j))
    ⟨j₀, hfin.mem_toFinset.2 hj₀⟩
  exact ⟨j, hfin.mem_toFinset.1 hj, fun i hi => hmin i (hfin.mem_toFinset.2 hi)⟩

theorem IsValid.isOwner_owner (hI : I.IsValid) (p : Plane) : I.IsOwner p (I.owner p) :=
  Classical.epsilon_spec (hI.exists_isOwner p)

/-- The owner is unique. -/
theorem IsOwner.unique {p : Plane} {j j' : ℤ} (h : I.IsOwner p j) (h' : I.IsOwner p j') : j = j' := by
  have h1 := le_antisymm (h.2 j' h'.1) (h'.2 j h.1)
  have h2 := congrArg (fun x => (ofLex x).2) h1
  simpa using h2

theorem IsValid.owner_eq (hI : I.IsValid) {p : Plane} {j : ℤ} (h : I.IsOwner p j) : I.owner p = j :=
  (hI.isOwner_owner p).unique h

theorem IsValid.owner_mem_labels (hI : I.IsValid) (p : Plane) : I.owner p ∈ I.labels p :=
  (hI.isOwner_owner p).1

/-- The owner has the least weight among the labels meeting the tile. -/
theorem IsValid.e_owner_le (hI : I.IsValid) (p : Plane) {i : ℤ} (hi : i ∈ I.labels p) :
    I.e (I.owner p) ≤ I.e i := by
  have h := (hI.isOwner_owner p).2 i hi
  rcases Prod.Lex.toLex_le_toLex.1 h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem shared_subset_piece (p : Plane) (j : ℤ) : shared I.V p ⊆ I.piece p j := by
  unfold piece
  split_ifs
  · exact shared_subset_tile I.V p
  · exact subset_rfl

theorem piece_subset_tile (p : Plane) (j : ℤ) : I.piece p j ⊆ tile I.V p := by
  unfold piece
  split_ifs
  · exact subset_rfl
  · exact shared_subset_tile I.V p

theorem piece_of_owner {p : Plane} {j : ℤ} (h : I.owner p = j) : I.piece p j = tile I.V p := by
  simp [piece, h]

theorem piece_of_ne {p : Plane} {j : ℤ} (h : I.owner p ≠ j) : I.piece p j = shared I.V p := by
  simp [piece, h]

theorem IsValid.isCompact_piece (hI : I.IsValid) (p : Plane) (j : ℤ) : IsCompact (I.piece p j) := by
  unfold piece
  split_ifs
  · exact hI.site.isCompact_tile p
  · exact hI.site.isCompact_shared p

theorem IsValid.isConnected_piece (hI : I.IsValid) (p : Plane) (j : ℤ) :
    IsConnected (I.piece p j) := by
  unfold piece
  split_ifs
  · exact (convex_tile I.V p).isConnected ⟨p, self_mem_tile I.V p⟩
  · exact hI.site.isConnected_shared p

theorem IsValid.tile_subset_cell_owner (hI : I.IsValid) {p : Plane} (hp : p ∈ I.V) :
    tile I.V p ⊆ I.cell (I.owner p) := fun y hy =>
  mem_iUnion₂.2 ⟨p, ⟨hp, hI.owner_mem_labels p⟩, by rw [piece_of_owner rfl]; exact hy⟩

theorem shared_subset_cell {p : Plane} {j : ℤ} (hp : p ∈ I.V) (hj : j ∈ I.labels p) :
    shared I.V p ⊆ I.cell j :=
  fun _ hy => mem_iUnion₂.2 ⟨p, ⟨hp, hj⟩, shared_subset_piece p j hy⟩

theorem IsValid.finite_sitesOf (hI : I.IsValid) (j : ℤ) : (I.sitesOf j).Finite := by
  obtain ⟨R, hR⟩ := (hI.compact j).isBounded.subset_closedBall (0 : Plane)
  refine (hI.site.finite_tiles_meeting 0 R).subset fun p hp => ⟨hp.1, ?_⟩
  obtain ⟨y, hyK, hyt⟩ := hp.2
  exact ⟨y, hyt, hR hyK⟩

/-! ## The polygonal cells -/

/-- **The polygonal cells are compact.** -/
theorem IsValid.isCompact_cell (hI : I.IsValid) (j : ℤ) : IsCompact (I.cell j) :=
  (hI.finite_sitesOf j).isCompact_biUnion fun p _ => hI.isCompact_piece p j

/-- **`v_j ∈ C_j`** (answer, line 25: "`v_j ∈ C_j` because it is itself a site and belongs to a spoke of
its tile"). -/
theorem IsValid.v_mem_cell (hI : I.IsValid) (j : ℤ) : I.v j ∈ I.cell j :=
  shared_subset_cell (hI.vsite j) ⟨I.v j, hI.vmem j, self_mem_tile I.V (I.v j)⟩
    (self_mem_shared I.V (I.v j))

/-- **The polygonal cells have interior**: each contains the tile it owns. -/
theorem IsValid.interior_cell_nonempty (hI : I.IsValid) (j : ℤ) : (interior (I.cell j)).Nonempty := by
  obtain ⟨p, hpV, hp⟩ := hI.own j
  rw [← hp]
  exact (hI.site.interior_tile_nonempty p).mono (interior_mono (hI.tile_subset_cell_owner hpV))

/-- **The polygonal cells cover the plane.** -/
theorem IsValid.exists_mem_cell (hI : I.IsValid) (z : Plane) : ∃ j, z ∈ I.cell j := by
  obtain ⟨p, hp, hz⟩ := hI.site.exists_mem_tile z
  exact ⟨I.owner p, hI.tile_subset_cell_owner hp hz⟩

/-- **The polygonal cells are locally finite.** -/
theorem IsValid.finite_cells_meeting (hI : I.IsValid) (z : Plane) (R : ℝ) :
    {j | (I.cell j ∩ closedBall z R).Nonempty}.Finite := by
  refine ((hI.site.finite_tiles_meeting z R).biUnion fun p _ => hI.finite_labels p).subset ?_
  rintro j ⟨y, hyc, hyB⟩
  obtain ⟨p, ⟨hpV, hj⟩, hyp⟩ := mem_iUnion₂.1 hyc
  exact mem_iUnion₂.2 ⟨p, ⟨hpV, y, piece_subset_tile p j hyp, hyB⟩, hj⟩

/-- **The polygonal cells are connected** (answer, line 25: "The tiles meeting `K_j` form a connected
intersection graph by connectedness of `K_j`, and touching tiles have a common boundary point"). -/
theorem IsValid.isConnected_cell (hI : I.IsValid) (j : ℤ) : IsConnected (I.cell j) := by
  have hcov : I.K j ⊆ ⋃ p ∈ I.sitesOf j, tile I.V p := fun z hz => by
    obtain ⟨p, hp, hzp⟩ := hI.site.exists_mem_tile z
    exact mem_iUnion₂.2 ⟨p, ⟨hp, z, hz, hzp⟩, hzp⟩
  have hmeet : ∀ p ∈ I.sitesOf j, (tile I.V p ∩ I.K j).Nonempty := fun p hp => by
    obtain ⟨y, hy1, hy2⟩ := hp.2
    exact ⟨y, hy2, hy1⟩
  have hchain := reflTransGen_of_closed_cover (hI.conn j) (hI.finite_sitesOf j)
    (fun p _ => isClosed_tile I.V p) hcov hmeet
    (fun p q => (I.piece p j ∩ I.piece q j).Nonempty ∧ p ∈ I.sitesOf j) (by
      intro z _ p hp q hq hzp hzq
      by_cases hpq : p = q
      · subst hpq
        exact ReflTransGen.refl
      · refine ReflTransGen.single ⟨⟨z, ?_, ?_⟩, hp⟩
        · exact shared_subset_piece p j (tile_inter_subset_shared hp.1 hq.1 hpq ⟨hzp, hzq⟩)
        · exact shared_subset_piece q j
            (tile_inter_subset_shared hq.1 hp.1 (Ne.symm hpq) ⟨hzq, hzp⟩))
  have hne : (I.sitesOf j).Nonempty :=
    ⟨I.v j, hI.vsite j, I.v j, hI.vmem j, self_mem_tile I.V (I.v j)⟩
  exact IsConnected.biUnion_of_reflTransGen hne (fun p _ => hI.isConnected_piece p j) hchain

/-- **Distinct polygonal cells overlap in a null set** (answer, line 25: they "overlap only on polygonal
edges and segments"). -/
theorem IsValid.volume_cell_inter (hI : I.IsValid) {i j : ℤ} (hij : i ≠ j) :
    volume (I.cell i ∩ I.cell j) = 0 := by
  have hsub : I.cell i ∩ I.cell j ⊆
      ⋃ p ∈ I.sitesOf i, ⋃ q ∈ I.sitesOf j, I.piece p i ∩ I.piece q j := by
    rintro z ⟨hzi, hzj⟩
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hzi
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hzj
    exact mem_iUnion₂.2 ⟨p, hp, mem_iUnion₂.2 ⟨q, hq, hzp, hzq⟩⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff (hI.finite_sitesOf i).countable).2
    fun p hp => (measure_biUnion_null_iff (hI.finite_sitesOf j).countable).2 fun q hq => ?_)
  by_cases hpq : p = q
  · rw [← hpq]
    by_cases hown : I.owner p = i
    · have hne : I.owner p ≠ j := fun h => hij (hown.symm.trans h)
      rw [piece_of_ne hne]
      exact measure_mono_null inter_subset_right (volume_shared I.V p)
    · rw [piece_of_ne hown]
      exact measure_mono_null inter_subset_left (volume_shared I.V p)
  · exact measure_mono_null (inter_subset_inter (piece_subset_tile p i) (piece_subset_tile q j))
      (volume_tile_inter I.V hp.1 hq.1 hpq)

/-- **Distinct labels give distinct polygonal cells**: an interior point of the owned tile off its
shared piece lies in no other cell. -/
theorem IsValid.cell_injective (hI : I.IsValid) : Function.Injective I.cell := by
  intro i j hij
  by_contra hne
  obtain ⟨p, hpV, hp⟩ := hI.own i
  obtain ⟨y, hyint, hys⟩ := hI.site.exists_mem_interior_notMem_shared p
  have hyi : y ∈ I.cell i := by
    rw [← hp]
    exact hI.tile_subset_cell_owner hpV (interior_subset hyint)
  rw [hij] at hyi
  obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 hyi
  by_cases hqp : q = p
  · rw [hqp, piece_of_ne (fun h => hne (hp.symm.trans h))] at hyq
    exact hys hyq
  · exact hys (tile_inter_subset_shared hpV hq.1 (Ne.symm hqp)
      ⟨interior_subset hyint, piece_subset_tile q j hyq⟩)

/-- **Adjacent polygonal cells meet** (answer, line 25: "If `K_i, K_j` are neighbors, a tile meeting their
common point gives both labels its boundary"). -/
theorem IsValid.cell_inter_nonempty (hI : I.IsValid) {i j : ℤ} (h : 0 < I.m i j) :
    (I.cell i ∩ I.cell j).Nonempty := by
  obtain ⟨z, hzi, hzj⟩ := hI.m_inter i j h
  obtain ⟨p, hp, hzp⟩ := hI.site.exists_mem_tile z
  exact ⟨p, shared_subset_cell hp ⟨z, hzi, hzp⟩ (self_mem_shared I.V p),
    shared_subset_cell hp ⟨z, hzj, hzp⟩ (self_mem_shared I.V p)⟩

/-- **Every point of an old cell is close to its polygonal cell** (answer, line 48: the tile containing a
point `z ∈ K_j` lies in the cell of its owner, and its boundary lies in `C_j`): some polygonal cell `C_k`
contains `z` and `C_j` has a point within `diam C_k` of `z`. -/
theorem IsValid.exists_near (hI : I.IsValid) {j : ℤ} {z : Plane} (hz : z ∈ I.K j) :
    ∃ k, z ∈ I.cell k ∧ ∃ y ∈ I.cell j, dist z y ≤ diam (I.cell k) := by
  obtain ⟨p, hp, hzp⟩ := hI.site.exists_mem_tile z
  refine ⟨I.owner p, hI.tile_subset_cell_owner hp hzp, p,
    shared_subset_cell hp ⟨z, hz, hzp⟩ (self_mem_shared I.V p), ?_⟩
  exact dist_le_diam_of_mem (hI.isCompact_cell _).isBounded (hI.tile_subset_cell_owner hp hzp)
    (hI.tile_subset_cell_owner hp (self_mem_tile I.V p))

/-! ## Connectedness at points -/

/-- The labels meeting a tile are connected by edges of positive count between them. -/
theorem IsValid.reflTransGen_labels (hI : I.IsValid) (p : Plane) :
    ∀ i ∈ I.labels p, ∀ j ∈ I.labels p,
      ReflTransGen (fun a b => 0 < I.m a b ∧ a ∈ I.labels p ∧ b ∈ I.labels p) i j := by
  refine reflTransGen_of_closed_cover (convex_tile I.V p).isPreconnected (hI.finite_labels p)
    (fun j _ => (hI.compact j).isClosed) (fun z hz => ?_) (fun j hj => hj) _ ?_
  · obtain ⟨j, hj⟩ := hI.cover z
    exact mem_iUnion₂.2 ⟨j, ⟨z, hj, hz⟩, hj⟩
  · intro z hz a _ b _ hza hzb
    exact ReflTransGen.mono (fun c d h => ⟨h.1, ⟨z, h.2.1, hz⟩, ⟨z, h.2.2, hz⟩⟩)
      _ _ (hI.pt z a b hza hzb)

/-- **The polygonal cells through a point are connected by edges of positive count** (answer, line 27: "In
a tile interior away from the spokes only its owner occurs. On a spoke in its interior all labels meeting
that tile occur and are connected. At a tile boundary take the union of the connected label sets of the
incident tiles. They all include any original label containing the point"). -/
theorem IsValid.reflTransGen_point (hI : I.IsValid) (z : Plane) {i j : ℤ} (hi : z ∈ I.cell i)
    (hj : z ∈ I.cell j) :
    ReflTransGen (fun a b => 0 < I.m a b ∧ z ∈ I.cell a ∧ z ∈ I.cell b) i j := by
  by_cases hcase : ∃ p ∈ I.V, z ∈ tile I.V p ∧ z ∉ shared I.V p
  · obtain ⟨p, hpV, hzp, hzs⟩ := hcase
    have key : ∀ l, z ∈ I.cell l → l = I.owner p := by
      intro l hl
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hl
      have hqp : q = p := by
        by_contra hne
        exact hzs (tile_inter_subset_shared hpV hq.1 (Ne.symm hne) ⟨hzp, piece_subset_tile q l hzq⟩)
      rw [hqp] at hzq
      by_contra hne
      rw [piece_of_ne (Ne.symm hne)] at hzq
      exact hzs hzq
    have hij : i = j := (key i hi).trans (key j hj).symm
    subst hij
    exact ReflTransGen.refl
  · have hcase' : ∀ p ∈ I.V, z ∈ tile I.V p → z ∈ shared I.V p := fun p hp hzp =>
      not_not.1 fun h => hcase ⟨p, hp, hzp, h⟩
    have hB : ∀ p ∈ I.V, z ∈ tile I.V p → ∀ l ∈ I.labels p, z ∈ I.cell l :=
      fun p hp hzp l hl => shared_subset_cell hp hl (hcase' p hp hzp)
    have hA : ∀ l, z ∈ I.cell l → ∃ p ∈ I.V, z ∈ tile I.V p ∧ l ∈ I.labels p := by
      intro l hl
      obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hl
      exact ⟨p, hp.1, piece_subset_tile p l hzp, hp.2⟩
    obtain ⟨k₀, hk₀⟩ := hI.cover z
    have toK : ∀ p ∈ I.V, z ∈ tile I.V p → ∀ l ∈ I.labels p,
        ReflTransGen (fun a b => 0 < I.m a b ∧ z ∈ I.cell a ∧ z ∈ I.cell b) l k₀ := by
      intro p hp hzp l hl
      exact ReflTransGen.mono (fun a b hab =>
        ⟨hab.1, hB p hp hzp a hab.2.1, hB p hp hzp b hab.2.2⟩)
        _ _ (hI.reflTransGen_labels p l hl k₀ ⟨z, hk₀, hzp⟩)
    have hsymm : Symmetric (fun a b => 0 < I.m a b ∧ z ∈ I.cell a ∧ z ∈ I.cell b) :=
      fun a b hab => ⟨by rw [← hI.m_symm a b]; exact hab.1, hab.2.2, hab.2.1⟩
    obtain ⟨p, hp, hzp, hip⟩ := hA i hi
    obtain ⟨q, hq, hzq, hjq⟩ := hA j hj
    haveI : Std.Symm (fun a b => 0 < I.m a b ∧ z ∈ I.cell a ∧ z ∈ I.cell b) := ⟨fun _ _ h => hsymm h⟩
    exact (toK p hp hzp i hip).trans (symm_of (ReflTransGen _) (toK q hq hzq j hjq))

end PolygonalInput

end MatedCRT.ZeroConePolygonal
