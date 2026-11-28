import MatedCRT.FirstPass.Derived.ZeroConePolygonalCells

/-!
# The weights, core scales and scale function of the old cells

The choices of the polygonal construction of the written answer `answers/51-zero-cone-annulus-premise.md`
(lines 7-25), made for a family of old cells `K_j` (`j ∈ ℤ`) with integer edge counts `m`.

* `OldCells K m`: the geometric hypotheses on the old cells (compact, positive area, locally finite, cover
  the plane, pairwise null overlaps, symmetric counts between cells that meet).
* `weight K m j`: `e_j = (diam K_j)² / |K_j| * ∑_{i : m_ij > 0} (m_ij + m_ij⁻¹)`.
* `coreSet K j δ`: the points of `K_j` at distance `> δ` from the other old cells.
* `coreScale K j`: `δ_j = 2⁻ⁿ diam K_j` for the least `n ≥ 1` such that `coreSet K j δ_j` has at least half
  the area of `K_j` (`coreScale_spec`).
* `scaleFun K m z`: `r(z) = inf_j (δ_j + dist z K_j)`.
* `scaleFun_lip`, `scaleFun_pos`, `scaleFun_le_of_mem`: `r` is `1`-Lipschitz and positive, and `r ≤ δ_j` on
  `K_j`. These are the fields `lip` and `pos` of `IsSiteSystem`.

For a `PolygonalInput I` over the old cells whose scale function and weights are `scaleFun` and `weight` and
whose sites form an `IsSiteSystem`:

* `PolygonalInput.exists_owner_eq`: every label owns a tile (the field `own` of `IsValid`);
* `PolygonalInput.coreSet_subset_cell`, `PolygonalInput.volume_div_two_le_volume_cell`: the core of `K_j` lies
  in `C_j`, so `|C_j| ≥ |K_j| / 2`;
* `PolygonalInput.exists_dist_le_of_mem_cell`, `PolygonalInput.diam_cell_le`: every point of `C_j` is within
  `δ_j / 40` of `K_j`, so `diam C_j ≤ 2 diam K_j`;
* `PolygonalInput.e_owner_le`, `PolygonalInput.cell_ratio_le`, `PolygonalInput.cell_ratio_owner_le`: the
  pointwise estimate `(diam C_j)² / |C_j| ∑_k (m_jk + m_jk⁻¹) ≤ 8 e_i` (answer, lines 35-38).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-! ## The hypotheses on the old cells -/

/-- **The old cells**: compact sets of positive area, locally finite, covering the plane, with pairwise
null overlaps, and symmetric edge counts `m` which are positive only between old cells that meet. -/
structure OldCells (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) : Prop where
  compact : ∀ j, IsCompact (K j)
  volume_pos : ∀ j, 0 < volume (K j)
  lf : ∀ A : Set Plane, IsCompact A → {j | (K j ∩ A).Nonempty}.Finite
  cover : ∀ z, ∃ j, z ∈ K j
  volume_inter : ∀ i j, i ≠ j → volume (K i ∩ K j) = 0
  m_symm : ∀ i j, m i j = m j i
  m_inter : ∀ i j, 0 < m i j → (K i ∩ K j).Nonempty

/-! ## Definitions -/

/-- **The weight** `e_j = (diam K_j)² / |K_j| * ∑_{i : m_ij > 0} (m_ij + m_ij⁻¹)` of the old cell `K_j`. -/
def weight (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) (j : ℤ) : ℝ :=
  diam (K j) ^ 2 / (volume (K j)).toReal *
    ∑ᶠ i ∈ {i : ℤ | 0 < m i j}, ((m i j : ℝ) + ((m i j : ℝ))⁻¹)

/-- The union of the old cells other than `K_j`. -/
def otherCells (K : ℤ → Set Plane) (j : ℤ) : Set Plane := ⋃ (i : ℤ) (_ : i ≠ j), K i

/-- The points of `K_j` at distance `> δ` from the union of the other old cells. -/
def coreSet (K : ℤ → Set Plane) (j : ℤ) (δ : ℝ) : Set Plane :=
  {z | z ∈ K j ∧ δ < infDist z (otherCells K j)}

/-- The exponent `n ≥ 1` of the core scale: the least `n ≥ 1` such that at least half the area of `K_j` lies
at distance `> 2⁻ⁿ diam K_j` from the other old cells. -/
def coreIndex (K : ℤ → Set Plane) (j : ℤ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ volume (K j) / 2 ≤ volume (coreSet K j (diam (K j) / 2 ^ n))}

/-- **The core scale** `δ_j = 2⁻ⁿ diam K_j` (answer, line 15). -/
def coreScale (K : ℤ → Set Plane) (j : ℤ) : ℝ := diam (K j) / 2 ^ coreIndex K j

/-- **The scale function** `r(z) = inf_j (δ_j + dist(z, K_j))` (answer, line 17). -/
def scaleFun (K : ℤ → Set Plane) (_m : ℤ → ℤ → ℕ) (z : Plane) : ℝ :=
  ⨅ j, (coreScale K j + infDist z (K j))

namespace OldCells

variable {K : ℤ → Set Plane} {m : ℤ → ℤ → ℕ}

theorem volume_lt_top (hK : OldCells K m) (j : ℤ) : volume (K j) < ⊤ :=
  (hK.compact j).measure_lt_top

theorem nonempty (hK : OldCells K m) (j : ℤ) : (K j).Nonempty :=
  nonempty_of_measure_ne_zero (hK.volume_pos j).ne'

theorem diam_pos (hK : OldCells K m) (j : ℤ) : 0 < diam (K j) := by
  apply Metric.diam_pos _ (hK.compact j).isBounded
  by_contra h
  rw [Set.not_nontrivial_iff] at h
  exact (hK.volume_pos j).ne' (h.measure_zero volume)

/-- Only finitely many old cells have a positive count with `K_j`. -/
theorem finite_neighbours (hK : OldCells K m) (j : ℤ) : {i : ℤ | 0 < m i j}.Finite :=
  ((hK.lf _ (hK.compact j)).subset fun i hi => hK.m_inter i j hi)

theorem otherCells_nonempty (hK : OldCells K m) (j : ℤ) : (otherCells K j).Nonempty := by
  obtain ⟨y, hy⟩ := hK.nonempty (j + 1)
  exact ⟨y, mem_iUnion₂.2 ⟨j + 1, by simp, hy⟩⟩

/-- The points of `K_j` at distance zero from the other old cells form a null set: by local finiteness
the closure of the union of the other cells near `K_j` is a finite union of old cells. -/
theorem volume_dist_eq_zero (hK : OldCells K m) (j : ℤ) :
    volume {z | z ∈ K j ∧ infDist z (otherCells K j) = 0} = 0 := by
  set F : Set ℤ := {i | (K i ∩ cthickening 1 (K j)).Nonempty} with hF
  have hFfin : F.Finite := hK.lf _ ((hK.compact j).cthickening)
  set U' : Set Plane := ⋃ i ∈ F \ {j}, K i with hU'
  have hU'closed : IsClosed U' :=
    (hFfin.sdiff).isClosed_biUnion fun i _ => (hK.compact i).isClosed
  refine measure_mono_null (t := ⋃ i ∈ F \ {j}, K j ∩ K i) ?_
    ((measure_biUnion_null_iff hFfin.sdiff.countable).2 fun i hi =>
      hK.volume_inter j i (fun h => hi.2 h.symm))
  rintro z ⟨hzK, hz0⟩
  have hzcl : z ∈ closure U' := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hne := hK.otherCells_nonempty j
    obtain ⟨y, hyU, hy⟩ := (infDist_lt_iff hne).1 (show infDist z (otherCells K j) < min ε 1 by
      rw [hz0]; exact lt_min hε one_pos)
    obtain ⟨i, hij, hyi⟩ := mem_iUnion₂.1 hyU
    have hyth : y ∈ cthickening 1 (K j) :=
      mem_cthickening_of_dist_le y z 1 (K j) hzK ((dist_comm z y ▸ hy.le).trans (min_le_right _ _))
    exact ⟨y, mem_iUnion₂.2 ⟨i, ⟨⟨y, hyi, hyth⟩, hij⟩, hyi⟩, lt_of_lt_of_le hy (min_le_left _ _)⟩
  rw [hU'closed.closure_eq] at hzcl
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hzcl
  exact mem_iUnion₂.2 ⟨i, hi, hzK, hzi⟩

theorem coreSet_mono {j : ℤ} {δ δ' : ℝ} (h : δ ≤ δ') : coreSet K j δ' ⊆ coreSet K j δ :=
  fun _ hz => ⟨hz.1, lt_of_le_of_lt h hz.2⟩

/-- A core of at least half the area of `K_j` exists at some scale `2⁻ⁿ diam K_j`, `n ≥ 1`. -/
theorem exists_core (hK : OldCells K m) (j : ℤ) :
    ∃ n : ℕ, 1 ≤ n ∧ volume (K j) / 2 ≤ volume (coreSet K j (diam (K j) / 2 ^ n)) := by
  have hmono : Monotone fun n : ℕ => coreSet K j (diam (K j) / 2 ^ n) := fun a b hab =>
    coreSet_mono (div_le_div_of_nonneg_left (hK.diam_pos j).le (by positivity)
      (pow_le_pow_right₀ one_le_two hab))
  have hsup : volume (K j) ≤ ⨆ n : ℕ, volume (coreSet K j (diam (K j) / 2 ^ n)) := by
    rw [← hmono.measure_iUnion]
    calc volume (K j) ≤ volume ((⋃ n : ℕ, coreSet K j (diam (K j) / 2 ^ n)) ∪
          {z | z ∈ K j ∧ infDist z (otherCells K j) = 0}) := by
          refine measure_mono fun z hz => ?_
          by_cases h0 : infDist z (otherCells K j) = 0
          · exact Or.inr ⟨hz, h0⟩
          · left
            have hpos : 0 < infDist z (otherCells K j) := lt_of_le_of_ne infDist_nonneg (Ne.symm h0)
            obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (diam (K j) / infDist z (otherCells K j))
              (one_lt_two (α := ℝ))
            refine mem_iUnion.2 ⟨n, hz, ?_⟩
            rw [div_lt_iff₀ hpos] at hn
            rw [div_lt_iff₀ (by positivity)]
            linarith
      _ ≤ _ := (measure_union_le _ _).trans (by rw [hK.volume_dist_eq_zero j, add_zero])
  have hlt : volume (K j) / 2 < ⨆ n : ℕ, volume (coreSet K j (diam (K j) / 2 ^ n)) :=
    lt_of_lt_of_le (ENNReal.half_lt_self (hK.volume_pos j).ne' (hK.volume_lt_top j).ne) hsup
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  exact ⟨max n 1, le_max_right _ _, hn.le.trans (measure_mono (hmono (le_max_left _ _)))⟩

theorem coreIndex_spec (hK : OldCells K m) (j : ℤ) :
    1 ≤ coreIndex K j ∧
      volume (K j) / 2 ≤ volume (coreSet K j (diam (K j) / 2 ^ coreIndex K j)) :=
  Nat.sInf_mem (hK.exists_core j)

/-- The core of `K_j` at the scale `δ_j` has at least half the area of `K_j`. -/
theorem coreScale_spec (hK : OldCells K m) (j : ℤ) :
    volume (K j) / 2 ≤ volume (coreSet K j (coreScale K j)) :=
  (hK.coreIndex_spec j).2

theorem coreScale_pos (hK : OldCells K m) (j : ℤ) : 0 < coreScale K j :=
  div_pos (hK.diam_pos j) (by positivity)

theorem coreScale_le (hK : OldCells K m) (j : ℤ) : coreScale K j ≤ diam (K j) / 2 := by
  unfold coreScale
  refine div_le_div_of_nonneg_left (hK.diam_pos j).le (by norm_num) ?_
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ coreIndex K j := pow_le_pow_right₀ one_le_two (hK.coreIndex_spec j).1

end OldCells

/-- Points of the core are at distance `> δ_j` from every other old cell. -/
theorem coreScale_lt_dist {K : ℤ → Set Plane} {j i : ℤ} {z y : Plane}
    (hz : z ∈ coreSet K j (coreScale K j)) (hij : i ≠ j)
    (hy : y ∈ K i) : coreScale K j < dist z y :=
  lt_of_lt_of_le hz.2 (infDist_le_dist_of_mem (mem_iUnion₂.2 ⟨i, hij, hy⟩))

theorem coreScale_nonneg (K : ℤ → Set Plane) (j : ℤ) : 0 ≤ coreScale K j :=
  div_nonneg Metric.diam_nonneg (by positivity)

theorem bddBelow_scaleFun (K : ℤ → Set Plane) (z : Plane) :
    BddBelow (Set.range fun j => coreScale K j + infDist z (K j)) :=
  ⟨0, by rintro _ ⟨j, rfl⟩; exact add_nonneg (coreScale_nonneg K j) infDist_nonneg⟩

theorem scaleFun_le (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) (z : Plane) (j : ℤ) :
    scaleFun K m z ≤ coreScale K j + infDist z (K j) :=
  ciInf_le (bddBelow_scaleFun K z) j

/-- **`r ≤ δ_j` on `K_j`.** -/
theorem scaleFun_le_of_mem {K : ℤ → Set Plane} (m : ℤ → ℤ → ℕ) {z : Plane} {j : ℤ} (hz : z ∈ K j) :
    scaleFun K m z ≤ coreScale K j := by
  simpa [infDist_zero_of_mem hz] using scaleFun_le K m z j

/-- **The scale function is `1`-Lipschitz** (the field `lip` of `IsSiteSystem`). -/
theorem scaleFun_lip (K : ℤ → Set Plane) (m : ℤ → ℤ → ℕ) (y z : Plane) :
    scaleFun K m y ≤ scaleFun K m z + dist y z := by
  have : scaleFun K m y - dist y z ≤ scaleFun K m z := by
    refine le_ciInf fun j => ?_
    have := scaleFun_le K m y j
    have := infDist_le_infDist_add_dist (x := y) (y := z) (s := K j)
    linarith
  linarith

/-- **The scale function is positive** (the field `pos` of `IsSiteSystem`): near `z` only finitely many old
cells occur and each has positive core scale. -/
theorem scaleFun_pos {K : ℤ → Set Plane} {m : ℤ → ℤ → ℕ} (hK : OldCells K m) (z : Plane) :
    0 < scaleFun K m z := by
  set F : Set ℤ := {i | (K i ∩ closedBall z 1).Nonempty} with hF
  have hFfin : F.Finite := hK.lf _ (isCompact_closedBall z 1)
  obtain ⟨j₀, hj₀⟩ := hK.cover z
  have hj₀F : j₀ ∈ F := ⟨z, hj₀, mem_closedBall_self zero_le_one⟩
  obtain ⟨j₁, hj₁, hmin⟩ := hFfin.toFinset.exists_min_image (coreScale K) ⟨j₀, hFfin.mem_toFinset.2 hj₀F⟩
  have hc := hK.coreScale_pos j₁
  refine lt_of_lt_of_le (lt_min one_pos hc) (le_ciInf fun j => ?_)
  by_cases hj : j ∈ F
  · exact (min_le_right _ _).trans ((hmin j (hFfin.mem_toFinset.2 hj)).trans
      (le_add_of_nonneg_right infDist_nonneg))
  · refine (min_le_left _ _).trans ?_
    have h1 : 1 ≤ infDist z (K j) := by
      rw [le_infDist (hK.nonempty j)]
      intro y hy
      by_contra hlt
      exact hj ⟨y, hy, mem_closedBall.2 (by rw [dist_comm]; exact (not_le.1 hlt).le)⟩
    exact h1.trans (le_add_of_nonneg_left (coreScale_nonneg K j))

/-! ## Polygonal cells over the old cells -/

namespace PolygonalInput

variable {I : PolygonalInput}

/-- A tile containing a core point of `K_j` meets no other old cell: the labels meeting it are `{j}`. -/
theorem labels_subset_of_mem_coreSet (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) {j : ℤ} {p z : Plane} (hz : z ∈ coreSet I.K j (coreScale I.K j))
    (hzp : z ∈ tile I.V p) : I.labels p ⊆ {j} := by
  rintro i ⟨y, hyK, hyt⟩
  by_contra hij
  have h1 := hV.dist_le_of_mem_tile_of_le hzp (hr ▸ scaleFun_le_of_mem I.m hz.1) hyt
  have h2 := coreScale_lt_dist hz hij hyK
  have h3 := hO.coreScale_pos j
  rw [dist_comm] at h2
  linarith

/-- Every tile has an owner, as the labels meeting it form a finite nonempty set. -/
theorem exists_isOwner_of_oldCells (hO : OldCells I.K I.m) (hV : IsSiteSystem I.V I.r) (p : Plane) :
    ∃ j, I.IsOwner p j := by
  obtain ⟨j₀, hj₀⟩ := hO.cover p
  have hfin : (I.labels p).Finite := hO.lf _ (hV.isCompact_tile p)
  obtain ⟨j, hj, hmin⟩ := hfin.toFinset.exists_min_image (fun j => toLex (I.e j, j))
    ⟨j₀, hfin.mem_toFinset.2 ⟨p, hj₀, self_mem_tile I.V p⟩⟩
  exact ⟨j, hfin.mem_toFinset.1 hj, fun i hi => hmin i (hfin.mem_toFinset.2 hi)⟩

theorem isOwner_owner_of_oldCells (hO : OldCells I.K I.m) (hV : IsSiteSystem I.V I.r) (p : Plane) :
    I.IsOwner p (I.owner p) :=
  Classical.epsilon_spec (exists_isOwner_of_oldCells hO hV p)

/-- **The owner of a tile containing a core point of `K_j` is `j`.** -/
theorem owner_eq_of_mem_coreSet (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) {j : ℤ} {p z : Plane} (hz : z ∈ coreSet I.K j (coreScale I.K j))
    (hzp : z ∈ tile I.V p) : I.owner p = j :=
  labels_subset_of_mem_coreSet hO hr hV hz hzp (isOwner_owner_of_oldCells hO hV p).1

/-- **Every label owns a tile** (the field `own` of `IsValid`): a tile containing a point of the half-area
core of `K_j` lies within `δ_j / 40` of that point, so it meets no other old cell. -/
theorem exists_owner_eq (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) (j : ℤ) : ∃ p ∈ I.V, I.owner p = j := by
  have hne : (coreSet I.K j (coreScale I.K j)).Nonempty := by
    refine nonempty_of_measure_ne_zero (μ := volume) fun h0 => ?_
    have := hO.coreScale_spec j
    rw [h0, nonpos_iff_eq_zero] at this
    exact (ENNReal.div_pos_iff.2 ⟨(hO.volume_pos j).ne', ENNReal.ofNat_ne_top⟩).ne' this
  obtain ⟨z, hz⟩ := hne
  obtain ⟨p, hp, hzp⟩ := hV.exists_mem_tile z
  exact ⟨p, hp, owner_eq_of_mem_coreSet hO hr hV hz hzp⟩

/-- **The core of `K_j` lies in the polygonal cell `C_j`.** -/
theorem coreSet_subset_cell (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) (j : ℤ) : coreSet I.K j (coreScale I.K j) ⊆ I.cell j := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := hV.exists_mem_tile z
  refine mem_iUnion₂.2 ⟨p, ⟨hp, z, hz.1, hzp⟩, ?_⟩
  rw [piece_of_owner (owner_eq_of_mem_coreSet hO hr hV hz hzp)]
  exact hzp

/-- **`|C_j| ≥ |K_j| / 2`** (answer, line 25). -/
theorem volume_div_two_le_volume_cell (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) (j : ℤ) : volume (I.K j) / 2 ≤ volume (I.cell j) :=
  (hO.coreScale_spec j).trans (measure_mono (coreSet_subset_cell hO hr hV j))

/-- **Every point of `C_j` is within `δ_j / 40` of `K_j`** (answer, line 25). -/
theorem exists_dist_le_of_mem_cell (hr : I.r = scaleFun I.K I.m) (hV : IsSiteSystem I.V I.r) {j : ℤ}
    {x : Plane} (hx : x ∈ I.cell j) : ∃ y ∈ I.K j, dist x y ≤ coreScale I.K j / 40 := by
  obtain ⟨p, ⟨-, y, hyK, hyt⟩, hxp⟩ := mem_iUnion₂.1 hx
  exact ⟨y, hyK, hV.dist_le_of_mem_tile_of_le hyt (hr ▸ scaleFun_le_of_mem I.m hyK)
    (piece_subset_tile p j hxp)⟩

theorem cell_subset_cthickening (hr : I.r = scaleFun I.K I.m) (hV : IsSiteSystem I.V I.r) (j : ℤ) :
    I.cell j ⊆ cthickening (coreScale I.K j / 40) (I.K j) := fun x hx => by
  obtain ⟨y, hy, hxy⟩ := exists_dist_le_of_mem_cell hr hV hx
  exact mem_cthickening_of_dist_le x y _ _ hy hxy

theorem isBounded_cell (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) (j : ℤ) : Bornology.IsBounded (I.cell j) :=
  ((hO.compact j).isBounded.cthickening).subset (cell_subset_cthickening hr hV j)

/-- **`diam C_j ≤ 2 diam K_j`** (answer, line 25). -/
theorem diam_cell_le (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (hV : IsSiteSystem I.V I.r) (j : ℤ) : diam (I.cell j) ≤ 2 * diam (I.K j) := by
  have hd := hO.diam_pos j
  have hδ := hO.coreScale_le j
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun a ha b hb => ?_
  obtain ⟨ya, hya, hay⟩ := exists_dist_le_of_mem_cell hr hV ha
  obtain ⟨yb, hyb, hby⟩ := exists_dist_le_of_mem_cell hr hV hb
  have h1 := Metric.dist_le_diam_of_mem (hO.compact j).isBounded hya hyb
  have h2 := dist_triangle a ya b
  have h3 := dist_triangle ya yb b
  rw [dist_comm yb b] at h3
  linarith

/-- **The owner of a tile has the least weight among the old cells meeting it**: if `z ∈ K_i` lies in the
tile of `p`, then `e_{owner p} ≤ e_i` (answer, line 35: "The owner rule gives `e_j ≤ e_i`"). -/
theorem e_owner_le (hO : OldCells I.K I.m) (hV : IsSiteSystem I.V I.r) {i : ℤ} {p z : Plane}
    (hzi : z ∈ I.K i) (hzp : z ∈ tile I.V p) : I.e (I.owner p) ≤ I.e i := by
  have h := (isOwner_owner_of_oldCells hO hV p).2 i ⟨z, hzi, hzp⟩
  rcases Prod.Lex.toLex_le_toLex.1 h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- **The size bounds give `(diam C_j)² / |C_j| ∑_k (m_jk + m_jk⁻¹) ≤ 8 e_j`.** -/
theorem cell_ratio_le (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (he : I.e = weight I.K I.m) (hV : IsSiteSystem I.V I.r) (j : ℤ) :
    diam (I.cell j) ^ 2 / (volume (I.cell j)).toReal *
      ∑ᶠ k ∈ {k : ℤ | 0 < I.m j k}, ((I.m j k : ℝ) + ((I.m j k : ℝ))⁻¹) ≤ 8 * I.e j := by
  have hS : ∑ᶠ k ∈ {k : ℤ | 0 < I.m j k}, ((I.m j k : ℝ) + ((I.m j k : ℝ))⁻¹) =
      ∑ᶠ i ∈ {i : ℤ | 0 < I.m i j}, ((I.m i j : ℝ) + ((I.m i j : ℝ))⁻¹) := by
    simp only [hO.m_symm j]
  have hS0 : 0 ≤ ∑ᶠ i ∈ {i : ℤ | 0 < I.m i j}, ((I.m i j : ℝ) + ((I.m i j : ℝ))⁻¹) :=
    finsum_nonneg fun i => finsum_nonneg fun _ => by positivity
  have hKpos : 0 < (volume (I.K j)).toReal :=
    ENNReal.toReal_pos (hO.volume_pos j).ne' (hO.volume_lt_top j).ne
  have hC : (volume (I.K j)).toReal / 2 ≤ (volume (I.cell j)).toReal := by
    have := ENNReal.toReal_mono (isBounded_cell hO hr hV j).measure_lt_top.ne
      (volume_div_two_le_volume_cell hO hr hV j)
    rwa [ENNReal.toReal_div, ENNReal.toReal_ofNat] at this
  have hd := hO.diam_pos j
  have hdc := diam_cell_le hO hr hV j
  have hdc0 : 0 ≤ diam (I.cell j) := Metric.diam_nonneg
  have hratio : diam (I.cell j) ^ 2 / (volume (I.cell j)).toReal ≤
      8 * (diam (I.K j) ^ 2 / (volume (I.K j)).toReal) := by
    calc diam (I.cell j) ^ 2 / (volume (I.cell j)).toReal
        ≤ (2 * diam (I.K j)) ^ 2 / ((volume (I.K j)).toReal / 2) :=
          div_le_div₀ (by positivity) (pow_le_pow_left₀ hdc0 hdc 2) (by positivity) hC
      _ = 8 * (diam (I.K j) ^ 2 / (volume (I.K j)).toReal) := by field_simp; ring
  rw [hS, he]
  unfold weight
  calc _ ≤ 8 * (diam (I.K j) ^ 2 / (volume (I.K j)).toReal) *
        ∑ᶠ i ∈ {i : ℤ | 0 < I.m i j}, ((I.m i j : ℝ) + ((I.m i j : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right hratio hS0
    _ = _ := by ring

/-- **The pointwise estimate** (answer, lines 35-38): if `z ∈ K_i` lies in the tile of `p`, whose owner is
`j`, then `(diam C_j)² / |C_j| ∑_k (m_jk + m_jk⁻¹) ≤ 8 e_i`. -/
theorem cell_ratio_owner_le (hO : OldCells I.K I.m) (hr : I.r = scaleFun I.K I.m)
    (he : I.e = weight I.K I.m) (hV : IsSiteSystem I.V I.r) {i : ℤ} {p z : Plane}
    (hzi : z ∈ I.K i) (hzp : z ∈ tile I.V p) :
    diam (I.cell (I.owner p)) ^ 2 / (volume (I.cell (I.owner p))).toReal *
      ∑ᶠ k ∈ {k : ℤ | 0 < I.m (I.owner p) k},
        ((I.m (I.owner p) k : ℝ) + ((I.m (I.owner p) k : ℝ))⁻¹) ≤ 8 * I.e i :=
  (cell_ratio_le hO hr he hV _).trans
    (mul_le_mul_of_nonneg_left (e_owner_le hO hV hzi hzp) (by norm_num))

end PolygonalInput

end MatedCRT.ZeroConePolygonal
