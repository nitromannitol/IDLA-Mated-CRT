import MatedCRT.Proofs.Sec5.StoppedInteriorGeometryProof
import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize
import MatedCRT.Steps.Sec5.IDLALowerBound

/-!
# The number of missing sites of the stopped cluster

`StoppedMissingSitesStep` (the first part of the layer step of Proposition 5.1): for
`κ > 0`, on `{t < T}` and with probability tending to one, `ε #(V^ε(Λ_t) \ Λ^ε_t) ≤ κ`, where `Λ^ε_t` is the discrete
cluster of the divisible sandpile in `B_ρ` (`matedDiscreteCluster`).

The argument (`eps_mul_card_missing_le`): each cell has `μ_h`-mass `ε` and distinct cells overlap in `μ_h`-null sets
(`IsAreaParametrized.measure_cell`, `IsAreaParametrized.measure_cell_inter`), so `ε #S` is the mass of the union of
the cells of the missing sites `S`. If the `h`-inner neighbourhood of `Λ_t` is covered by the cells of the discrete
cluster (Proposition 4.2 in the form `DiscreteClusterInnerBoundStep`) and the cells meeting `Λ_t` have diameter at most
`h`, then the points of the cells of `S` off a null set lie within `h` of `∂Λ_t`: a segment from a point of `Λ_t` to a
point outside meets the frontier (`exists_frontier_mem_segment`). These points are covered by the half-open squares
of side `h` whose `3h`-neighbourhood contains points of a countable dense set inside and outside `Λ_t`
(`flagged`), and the total mass of these squares, `squareBound`, is at most `μ_h(cthickening (5h) (∂Λ_t))`.

`squareBound` is a `σ(h)`-measurable function of the field-measurable version of `μ_h` and of the code of `Λ_t`
(`StoppedCode.ae_codeBall_eq`), and it tends to `μ_h(∂Λ_t) = 0` (Theorem 2.3(a)) as `h → 0` almost surely on
`{t < T}`. With the cell-size estimate of Lemma 2.8 this gives `stoppedMissingSites_of_innerBound`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace StoppedMissing

/-- A segment from a point of an open set to a point outside meets its frontier. -/
theorem exists_frontier_mem_segment {U : Set ℂ} (hU : IsOpen U) {x y : ℂ} (hx : x ∈ U) (hy : y ∉ U) :
    ∃ z ∈ segment ℝ x y, z ∈ frontier U := by
  by_contra h
  push Not at h
  have hcover : segment ℝ x y ⊆ interior U ∪ (closure U)ᶜ := fun z hz => by
    by_cases hzc : z ∈ closure U
    · left
      by_contra hzi
      exact h z hz ⟨hzc, hzi⟩
    · exact Or.inr hzc
  have hdisj : Disjoint (interior U) (closure U)ᶜ :=
    disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  have hsub := (convex_segment x y).isPreconnected.subset_left_of_subset_union isOpen_interior
    isClosed_closure.isOpen_compl hdisj hcover ⟨x, left_mem_segment ℝ x y, hU.interior_eq.symm ▸ hx⟩
  exact hy (interior_subset (hsub (right_mem_segment ℝ x y)))

/-- A condition `P → w ∈ s` with `s` measurable and `P` independent of `w` is measurable. -/
theorem measurableSet_const_imp {X : Type*} {m : MeasurableSpace X} {s : Set X} (hs : MeasurableSet[m] s)
    (P : Prop) : MeasurableSet[m] {w | P → w ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

/-- A condition `P ∧ w ∈ s` with `s` measurable and `P` independent of `w` is measurable. -/
theorem measurableSet_const_and {X : Type*} {m : MeasurableSpace X} {s : Set X} (hs : MeasurableSet[m] s)
    (P : Prop) : MeasurableSet[m] {w | P ∧ w ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

/-- A point of the segment `[x, y]` is within `dist x y` of `x`. -/
theorem dist_le_of_mem_segment {x y z : ℂ} (hz : z ∈ segment ℝ x y) : dist z x ≤ dist x y :=
  (convex_closedBall x (dist x y)).segment_subset (mem_closedBall_self dist_nonneg)
    (by rw [mem_closedBall, dist_comm]) hz

/-! ### Half-open squares -/

/-- The half-open square `[i h, (i + 1) h) × [j h, (j + 1) h)`. -/
def sq (h : ℝ) (i j : ℤ) : Set ℂ :=
  {x | (i : ℝ) * h ≤ x.re ∧ x.re < (i + 1) * h ∧ (j : ℝ) * h ≤ x.im ∧ x.im < (j + 1) * h}

theorem measurableSet_sq (h : ℝ) (i j : ℤ) : MeasurableSet (sq h i j) := by
  have h1 : Measurable fun x : ℂ => x.re := Complex.measurable_re
  have h2 : Measurable fun x : ℂ => x.im := Complex.measurable_im
  exact (measurableSet_le measurable_const h1).inter ((measurableSet_lt h1 measurable_const).inter
    ((measurableSet_le measurable_const h2).inter (measurableSet_lt h2 measurable_const)))

theorem convex_sq (h : ℝ) (i j : ℤ) : Convex ℝ (sq h i j) := by
  have hre : Convex ℝ (Complex.re ⁻¹' Ico ((i : ℝ) * h) ((i + 1) * h)) :=
    (convex_Ico _ _).linear_preimage Complex.reLm
  have him : Convex ℝ (Complex.im ⁻¹' Ico ((j : ℝ) * h) ((j + 1) * h)) :=
    (convex_Ico _ _).linear_preimage Complex.imLm
  convert hre.inter him using 1
  ext x
  simp only [sq, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ico]
  tauto

theorem dist_lt_of_mem_sq {h : ℝ} {i j : ℤ} {x y : ℂ} (hx : x ∈ sq h i j) (hy : y ∈ sq h i j) :
    dist x y < 2 * h := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im (x - y)).trans_lt ?_
  rw [Complex.sub_re, Complex.sub_im]
  have : |x.re - y.re| < h := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have : |x.im - y.im| < h := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  linarith

theorem mem_sq_floor {h : ℝ} (hh : 0 < h) (x : ℂ) : x ∈ sq h ⌊x.re / h⌋ ⌊x.im / h⌋ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ hh).1 (Int.floor_le _)
  · exact (div_lt_iff₀ hh).1 (Int.lt_floor_add_one _)
  · exact (le_div_iff₀ hh).1 (Int.floor_le _)
  · exact (div_lt_iff₀ hh).1 (Int.lt_floor_add_one _)

theorem eq_floor_of_mem_sq {h : ℝ} (hh : 0 < h) {i j : ℤ} {x : ℂ} (hx : x ∈ sq h i j) :
    i = ⌊x.re / h⌋ ∧ j = ⌊x.im / h⌋ := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  refine ⟨(Int.floor_eq_iff.2 ⟨(le_div_iff₀ hh).2 hx1, (div_lt_iff₀ hh).2 hx2⟩).symm,
    (Int.floor_eq_iff.2 ⟨(le_div_iff₀ hh).2 hx3, (div_lt_iff₀ hh).2 hx4⟩).symm⟩

theorem disjoint_sq {h : ℝ} (hh : 0 < h) {p q : ℤ × ℤ} (hpq : p ≠ q) :
    Disjoint (sq h p.1 p.2) (sq h q.1 q.2) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  obtain ⟨h1, h2⟩ := eq_floor_of_mem_sq hh hxp
  obtain ⟨h3, h4⟩ := eq_floor_of_mem_sq hh hxq
  exact hpq (Prod.ext (h1.trans h3.symm) (h2.trans h4.symm))

/-- The index set of the squares of side `1/(n+1)` meeting `[-3, 3)²`. -/
def sqIndex (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico (-3 * ((n : ℤ) + 1)) (3 * ((n : ℤ) + 1)) ×ˢ Finset.Ico (-3 * ((n : ℤ) + 1)) (3 * ((n : ℤ) + 1))

/-- The side `1/(n+1)` of the squares of level `n`. -/
noncomputable def side (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem side_pos (n : ℕ) : 0 < side n := by unfold side; positivity

theorem side_le_one (n : ℕ) : side n ≤ 1 := by
  unfold side
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem floor_mem_index {n : ℕ} {a : ℝ} (ha : |a| < 2) :
    ⌊a / side n⌋ ∈ Finset.Ico (-3 * ((n : ℤ) + 1)) (3 * ((n : ℤ) + 1)) := by
  have hs : a / side n = a * ((n : ℝ) + 1) := by rw [side, div_div_eq_mul_div, div_one]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨ha1, ha2⟩ := abs_lt.1 ha
  rw [Finset.mem_Ico, hs]
  constructor
  · rw [Int.le_floor]
    push_cast
    nlinarith
  · rw [Int.floor_lt]
    push_cast
    nlinarith

/-- The square of level `n` containing a point of the disc `B_2`. -/
theorem exists_sq_of_norm_lt {n : ℕ} {x : ℂ} (hx : ‖x‖ < 2) : ∃ p ∈ sqIndex n, x ∈ sq (side n) p.1 p.2 := by
  refine ⟨(⌊x.re / side n⌋, ⌊x.im / side n⌋), ?_, mem_sq_floor (side_pos n) x⟩
  rw [sqIndex, Finset.mem_product]
  exact ⟨floor_mem_index ((Complex.abs_re_le_norm x).trans_lt hx),
    floor_mem_index ((Complex.abs_im_le_norm x).trans_lt hx)⟩

/-! ### Flagged squares -/

/-- A square of side `h` is flagged for `U` if its `3h`-neighbourhood contains points of `denseC` in `U` and outside
`U`. -/
def flagged (U : Set ℂ) (h : ℝ) (p : ℤ × ℤ) : Prop :=
  (∃ q ∈ denseC, q ∈ U ∧ q ∈ thickening (3 * h) (sq h p.1 p.2)) ∧
    ∃ q ∈ denseC, q ∉ U ∧ q ∈ thickening (3 * h) (sq h p.1 p.2)

/-- A square containing a point within `h` of the frontier of a regular open set is flagged. -/
theorem flagged_of_frontier {U : Set ℂ} (hreg : interior (closure U) = U) {h : ℝ} (hh : 0 < h) {p : ℤ × ℤ}
    {x z : ℂ} (hx : x ∈ sq h p.1 p.2) (hz : z ∈ frontier U) (hxz : dist x z ≤ h) : flagged U h p := by
  have hU : IsOpen U := hreg ▸ isOpen_interior
  have hball : ball z h ⊆ thickening (3 * h) (sq h p.1 p.2) := fun y hy => by
    rw [mem_thickening_iff]
    refine ⟨x, hx, ?_⟩
    rw [mem_ball] at hy
    linarith [dist_triangle y z x, dist_comm x z]
  have hin : (U ∩ ball z h).Nonempty := by
    obtain ⟨y, hyU, hyz⟩ := Metric.mem_closure_iff.1 hz.1 h hh
    exact ⟨y, hyU, by rw [mem_ball, dist_comm]; exact hyz⟩
  have hout : ((closure U)ᶜ ∩ ball z h).Nonempty := by
    have hz' : z ∈ closure (closure U)ᶜ := by
      rw [closure_compl, hreg]
      exact fun hzU => hz.2 (hU.interior_eq.symm ▸ hzU)
    obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.1 hz' h hh
    exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hyz⟩
  obtain ⟨q, ⟨hqU, hqb⟩, hqD⟩ := denseC_spec.2.inter_open_nonempty _ (hU.inter isOpen_ball) hin
  obtain ⟨q', ⟨hq'U, hq'b⟩, hq'D⟩ :=
    denseC_spec.2.inter_open_nonempty _ (isClosed_closure.isOpen_compl.inter isOpen_ball) hout
  exact ⟨⟨q, hqD, hqU, hball hqb⟩, ⟨q', hq'D, fun h' => hq'U (subset_closure h'), hball hq'b⟩⟩

/-- A flagged square lies within `5h` of the frontier of an open set. -/
theorem sq_subset_cthickening_of_flagged {U : Set ℂ} (hU : IsOpen U) {h : ℝ} {p : ℤ × ℤ}
    (hf : flagged U h p) : sq h p.1 p.2 ⊆ cthickening (5 * h) (frontier U) := by
  obtain ⟨⟨q, -, hqU, hqT⟩, ⟨q', -, hq'U, hq'T⟩⟩ := hf
  obtain ⟨z, hzseg, hz⟩ := exists_frontier_mem_segment hU hqU hq'U
  have hzT : z ∈ thickening (3 * h) (sq h p.1 p.2) :=
    ((convex_sq h p.1 p.2).thickening (3 * h)).segment_subset hqT hq'T hzseg
  obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hzT
  intro x hx
  refine mem_cthickening_of_dist_le x z _ _ hz ?_
  have := dist_lt_of_mem_sq hx hy
  linarith [dist_triangle x y z, dist_comm z y]

open Classical in
/-- The total `μ`-mass of the flagged squares of level `n` in `[-3, 3)²`. -/
noncomputable def squareBound (μ : Measure ℂ) (U : Set ℂ) (n : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ sqIndex n, if flagged U (side n) p then μ (sq (side n) p.1 p.2) else 0

/-- The union of the flagged squares of level `n`. -/
def flaggedUnion (U : Set ℂ) (n : ℕ) : Set ℂ :=
  ⋃ p ∈ sqIndex n, ⋃ (_ : flagged U (side n) p), sq (side n) p.1 p.2

/-- `squareBound` is the mass of the union of the flagged squares. -/
theorem squareBound_eq (μ : Measure ℂ) (U : Set ℂ) (n : ℕ) : squareBound μ U n = μ (flaggedUnion U n) := by
  classical
  rw [flaggedUnion, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : flagged U (side n) p
    · simp [hp]
    · simp [hp]
  · intro p _ q _ hpq
    exact (disjoint_sq (side_pos n) hpq).mono (iUnion_subset fun _ => subset_rfl) (iUnion_subset fun _ => subset_rfl)
  · intro p _
    by_cases hp : flagged U (side n) p
    · simpa [hp] using measurableSet_sq (side n) p.1 p.2
    · simp [hp]

/-- `squareBound` is at most the mass of the `5h`-neighbourhood of the frontier, `h = 1/(n+1)`. -/
theorem squareBound_le (μ : Measure ℂ) {U : Set ℂ} (hU : IsOpen U) (n : ℕ) :
    squareBound μ U n ≤ μ (cthickening (5 * side n) (frontier U)) := by
  rw [squareBound_eq]
  refine measure_mono (iUnion₂_subset fun p _ => iUnion_subset fun hp => ?_)
  exact sq_subset_cthickening_of_flagged hU hp

/-! ### The deterministic bound on the missing sites -/

/-- A point of a cell meeting `Λ` that is not in the `h`-inner neighbourhood of `Λ` lies within `h` of `∂Λ`. -/
theorem exists_frontier_near {Λ : Set ℂ} (hΛo : IsOpen Λ) {h : ℝ} {x p : ℂ} (hp : p ∈ Λ) (hxp : dist x p ≤ h)
    (hx : x ∉ innerNbhd h Λ) : ∃ z ∈ frontier Λ, dist x z ≤ h := by
  by_cases hxΛ : x ∈ Λ
  · have hlt : Metric.infEDist x Λᶜ < ENNReal.ofReal h := by
      by_contra hge
      exact hx ⟨hxΛ, not_lt.1 hge⟩
    obtain ⟨y, hy, hxy⟩ := Metric.infEDist_lt_iff.1 hlt
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff'] at hxy
    obtain ⟨z, hzseg, hz⟩ := exists_frontier_mem_segment hΛo hxΛ hy
    exact ⟨z, hz, by rw [dist_comm]; exact (dist_le_of_mem_segment hzseg).trans hxy.1.le⟩
  · obtain ⟨z, hzseg, hz⟩ := exists_frontier_mem_segment hΛo hp hxΛ
    refine ⟨z, hz, ?_⟩
    have h1 : z ∈ closedBall x (dist x p) :=
      (convex_closedBall x (dist x p)).segment_subset (by rw [mem_closedBall, dist_comm])
        (mem_closedBall_self dist_nonneg) hzseg
    rw [mem_closedBall, dist_comm] at h1
    exact h1.trans hxp

/-- For an area parametrization, the mass of a finite union of cells is `ε` times their number. -/
theorem ofReal_mul_card_eq_measure {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) (Sf : Finset ℤ) : ENNReal.ofReal (ε * (Sf.card : ℝ)) = μ (⋃ a ∈ Sf, cell ε η a) := by
  have hmeas : ∀ k, MeasurableSet (cell ε η k) := fun k => (isCompact_Icc.image harea.1).isClosed.measurableSet
  have hd : (Sf : Set ℤ).Pairwise (Function.onFun (AEDisjoint μ) fun a => cell ε η a) := fun a _ b _ hab =>
    harea.measure_cell_inter hε hab
  rw [measure_biUnion_finset₀ hd (fun a _ => (hmeas a).nullMeasurableSet),
    Finset.sum_congr rfl fun a _ => harea.measure_cell hε a, Finset.sum_const, nsmul_eq_mul,
    ENNReal.ofReal_mul hε.le, ENNReal.ofReal_natCast, mul_comm]

/-- The points of a cell that lie in another cell form a null set, also for finitely many cells. -/
theorem measure_overlaps_eq_zero {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) (Sf : Finset ℤ) : μ (⋃ a ∈ Sf, ⋃ j : ℤ, ⋃ (_ : j ≠ a), cell ε η a ∩ cell ε η j) = 0 := by
  refine le_antisymm ((measure_biUnion_finset_le Sf fun a => ⋃ j : ℤ, ⋃ (_ : j ≠ a), cell ε η a ∩ cell ε η j).trans
    (Finset.sum_eq_zero fun a _ => ?_).le) zero_le
  exact measure_iUnion_null fun j => measure_iUnion_null fun hj => harea.measure_cell_inter hε (Ne.symm hj)

/-- The points of the cells of the missing sites lie in the flagged squares or in another cell. -/
theorem cells_subset_flaggedUnion {η : ℝ → ℂ} (hη : Continuous η) {Λ : Set ℂ} (hreg : interior (closure Λ) = Λ)
    (hΛB : Λ ⊆ ball 0 1) {C : Set ℤ} {ε : ℝ} (n : ℕ) (hinner : innerNbhd (side n) Λ ⊆ fillCells ε η C)
    (hdiam : ∀ k ∈ cellVertices ε η Λ, diam (cell ε η k) ≤ side n) (Sf : Finset ℤ)
    (hSf : ∀ a ∈ Sf, a ∈ cellVertices ε η Λ ∧ a ∉ C) :
    (⋃ a ∈ Sf, cell ε η a) ⊆ flaggedUnion Λ n ∪ ⋃ a ∈ Sf, ⋃ j : ℤ, ⋃ (_ : j ≠ a), cell ε η a ∩ cell ε η j := by
  have hΛo : IsOpen Λ := hreg ▸ isOpen_interior
  intro x hx
  obtain ⟨a, haS, hxa⟩ := mem_iUnion₂.1 hx
  obtain ⟨haV, haC⟩ := hSf a haS
  by_cases hxin : x ∈ innerNbhd (side n) Λ
  · right
    obtain ⟨j, hjC, hxj⟩ := mem_iUnion₂.1 (hinner hxin)
    have hja : j ≠ a := fun h => haC (h ▸ hjC)
    exact mem_iUnion₂.2 ⟨a, haS, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hja, hxa, hxj⟩⟩⟩
  · left
    obtain ⟨p, hpa, hpΛ⟩ := haV
    have hxp : dist x p ≤ side n :=
      (dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded hxa hpa).trans (hdiam a ⟨p, hpa, hpΛ⟩)
    obtain ⟨z, hz, hxz⟩ := exists_frontier_near hΛo hpΛ hxp hxin
    have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.1 (hΛB hpΛ)
    have hxnorm : ‖x‖ < 2 := by
      have h1 : ‖x‖ ≤ ‖p‖ + ‖x - p‖ := by
        calc ‖x‖ = ‖p + (x - p)‖ := by rw [add_sub_cancel]
          _ ≤ ‖p‖ + ‖x - p‖ := norm_add_le _ _
      rw [← dist_eq_norm] at h1
      linarith [side_le_one n]
    obtain ⟨q, hq, hxq⟩ := exists_sq_of_norm_lt (n := n) hxnorm
    exact mem_iUnion₂.2 ⟨q, hq, mem_iUnion.2 ⟨flagged_of_frontier hreg (side_pos n) hxq hz hxz, hxq⟩⟩

/-- **The missing sites of the stopped cluster are few (deterministic form).** Let `η` be an area parametrization of
`μ`, `Λ ⊆ B_1` regular open, and let the cells meeting `Λ` have diameter at most `h = 1/(n+1)`. If the `h`-inner
neighbourhood of `Λ` lies in the union of the cells of `C`, and `S = V^ε(Λ) \ C` is finite, then `ε #S` is at most the
mass of the flagged squares of level `n`. -/
theorem eps_mul_card_missing_le {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η) {Λ : Set ℂ}
    (hreg : interior (closure Λ) = Λ) (hΛB : Λ ⊆ ball 0 1) {C : Set ℤ} {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (hinner : innerNbhd (side n) Λ ⊆ fillCells ε η C)
    (hdiam : ∀ k ∈ cellVertices ε η Λ, diam (cell ε η k) ≤ side n)
    (hfin : (cellVertices ε η Λ \ C).Finite) :
    ENNReal.ofReal (ε * ((cellVertices ε η Λ \ C).ncard : ℝ)) ≤ squareBound μ Λ n := by
  rw [Set.ncard_eq_toFinset_card _ hfin, ofReal_mul_card_eq_measure harea hε, squareBound_eq]
  have hSf : ∀ a ∈ hfin.toFinset, a ∈ cellVertices ε η Λ ∧ a ∉ C := fun a ha => hfin.mem_toFinset.1 ha
  calc μ (⋃ a ∈ hfin.toFinset, cell ε η a)
      ≤ μ (flaggedUnion Λ n ∪ ⋃ a ∈ hfin.toFinset, ⋃ j : ℤ, ⋃ (_ : j ≠ a), cell ε η a ∩ cell ε η j) :=
        measure_mono (cells_subset_flaggedUnion harea.1 hreg hΛB n hinner hdiam _ hSf)
    _ ≤ μ (flaggedUnion Λ n) + μ (⋃ a ∈ hfin.toFinset, ⋃ j : ℤ, ⋃ (_ : j ≠ a), cell ε η a ∩ cell ε η j) :=
        measure_union_le _ _
    _ = μ (flaggedUnion Λ n) := by rw [measure_overlaps_eq_zero harea hε, add_zero]

/-! ### Measurability and the limit -/

/-- `squareBound` of a measure and the regularized cluster of a code is Borel in the pair. -/
theorem measurable_squareBound {Ω : Type*} {mΩ : MeasurableSpace Ω} {g : Ω → Measure ℂ} (hg : Measurable g)
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) {W : Ω → DiskFun ρ} (hW : Measurable W) (n : ℕ) :
    Measurable fun ω => squareBound (g ω) (StoppedCode.codeBall ρ t (W ω)) n := by
  classical
  have : Countable denseC := denseC_spec.1.to_subtype
  have hmem : ∀ x : ℂ, MeasurableSet {ω | x ∈ StoppedCode.codeBall ρ t (W ω)} := fun x =>
    hW (StoppedCode.measurableSet_mem_codeBall hρ ht x)
  refine Finset.measurable_sum _ fun p _ => Measurable.ite ?_
    ((Measure.measurable_coe (measurableSet_sq _ _ _)).comp hg) measurable_const
  have h1 : MeasurableSet {ω | ∃ q ∈ denseC, q ∈ StoppedCode.codeBall ρ t (W ω) ∧
      q ∈ thickening (3 * side n) (sq (side n) p.1 p.2)} := by
    convert MeasurableSet.iUnion fun q : denseC =>
      StoppedCode.measurableSet_and_const (hmem (q : ℂ)) ((q : ℂ) ∈ thickening (3 * side n) (sq (side n) p.1 p.2))
      using 1
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨q, hqD, hq⟩ => ⟨⟨q, hqD⟩, hq⟩, fun ⟨q, hq⟩ => ⟨q, q.2, hq⟩⟩
  have h2 : MeasurableSet {ω | ∃ q ∈ denseC, q ∉ StoppedCode.codeBall ρ t (W ω) ∧
      q ∈ thickening (3 * side n) (sq (side n) p.1 p.2)} := by
    convert MeasurableSet.iUnion fun q : denseC =>
      StoppedCode.measurableSet_and_const (hmem (q : ℂ)).compl
        ((q : ℂ) ∈ thickening (3 * side n) (sq (side n) p.1 p.2)) using 1
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff]
    exact ⟨fun ⟨q, hqD, hq⟩ => ⟨⟨q, hqD⟩, hq⟩, fun ⟨q, hq⟩ => ⟨q, q.2, hq⟩⟩
  exact h1.inter h2

/-- For a bounded open set whose frontier is null for a locally finite measure, `squareBound` tends to `0`. -/
theorem tendsto_squareBound {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hfr : μ (frontier U) = 0) :
    Tendsto (fun n => squareBound μ U n) atTop (𝓝 0) := by
  have hfin : ∃ R > 0, μ (cthickening R (frontier U)) ≠ ∞ := by
    refine ⟨1, one_pos, (IsCompact.measure_lt_top ?_).ne⟩
    exact Metric.isCompact_of_isClosed_isBounded isClosed_cthickening
      (hUb.closure.subset frontier_subset_closure).cthickening
  have hlim := tendsto_measure_cthickening_of_isClosed hfin isClosed_frontier
  rw [hfr] at hlim
  have hside : Tendsto (fun n : ℕ => 5 * side n) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 5
    simpa [side] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim.comp hside)
    (fun n => zero_le) (fun n => squareBound_le μ hU n)

/-! ### The missing-sites step -/

/-- **The missing-sites step** `StoppedMissingSitesStep` from Proposition 4.2 in the form
`DiscreteClusterInnerBoundStep`: the cell-size estimate of Lemma 2.8, the field-measurable code of `Λ_t` and
`μ_h(∂Λ_t) = 0` (Theorem 2.3(a)). -/
theorem stoppedMissingSites_of_innerBound (𝒮 : SpaceFillingSLEModel) (hinner : DiscreteClusterInnerBoundStep 𝒮) :
    StoppedMissingSitesStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht κ hκ
  have := hS.isProbabilityMeasure
  obtain ⟨W, hWm, hWae⟩ := StoppedCode.ae_codeBall_eq 𝒮 hγ hγ2 hρ hρ1 hS hΛ ht
  obtain ⟨g, hgm, hgae⟩ := frozenLQGMeasureFieldMeasurable_holds 𝒮 γ hγ hγ2 Ω S hS
  set B : ℕ → Ω → ℝ≥0∞ := fun m ω => squareBound (g ω) (StoppedCode.codeBall ρ t (W ω)) m with hBdef
  have hBm : ∀ m, Measurable[S.envSigma] (B m) := fun m =>
    (measurable_squareBound hgm hρ ht hWm m).mono le_sup_left le_rfl
  -- the good event
  set G : Set Ω := {ω | (t < clusterExitTime (Λ ω) ρ → Λ ω t = StoppedCode.codeBall ρ t (W ω)) ∧
    IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ S.μ ω = g ω ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
    IsLocallyFiniteMeasure (S.μ ω)} with hGdef
  have hG : S.P Gᶜ = 0 := by
    have h : ∀ᵐ ω ∂S.P, ω ∈ G := by
      filter_upwards [hWae, hΛ, hgae, hS.isAreaParametrized, hS.isLQGMeasure] with ω hωW hωΛ hωg hωη hωμ
      exact ⟨fun hT => (hωW hT).1, hωΛ, hωg, hωη, hωμ.isLocallyFiniteMeasure⟩
    exact ae_iff.1 h
  have hconv : ∀ ω ∈ G, t < clusterExitTime (Λ ω) ρ → Tendsto (fun m => B m ω) atTop (𝓝 0) := by
    rintro ω ⟨hcode, hfam, hg, -, hloc⟩ hT
    have hΛeq := hcode hT
    have hU : IsOpen (StoppedCode.codeBall ρ t (W ω)) := isOpen_interior
    have hfr : (g ω) (frontier (StoppedCode.codeBall ρ t (W ω))) = 0 := by
      rw [← hg, ← hΛeq]
      exact hfam.2.1.measure_frontier t ht
    have : IsLocallyFiniteMeasure (g ω) := hg ▸ hloc
    exact tendsto_squareBound hU (hΛeq ▸ hfam.2.1.isBounded t ht) hfr
  -- the eventual-smallness event and the tail events
  set Ev : Set Ω := ⋃ N : ℕ, ⋂ m : ℕ, {ω | N ≤ m → B m ω ≤ ENNReal.ofReal (κ / 2)} with hEvdef
  set A : ℕ → Set Ω := fun n => Ev ∩ ⋃ m : ℕ, {ω | n ≤ m ∧ ENNReal.ofReal κ < B m ω} with hAdef
  have hEvm : MeasurableSet[S.envSigma] Ev := MeasurableSet.iUnion fun N => MeasurableSet.iInter fun m =>
    measurableSet_const_imp (measurableSet_le (hBm m) measurable_const) (N ≤ m)
  have hAm : ∀ n, NullMeasurableSet (A n) S.P := fun n =>
    hS.nullMeasurableSet_of_envSigma (hEvm.inter (MeasurableSet.iUnion fun m =>
      measurableSet_const_and (measurableSet_lt measurable_const (hBm m)) (n ≤ m)))
  have hAanti : Antitone A := by
    intro n n' hnn' ω ⟨hEv, hω⟩
    obtain ⟨m, hm1, hm2⟩ := mem_iUnion.1 hω
    exact ⟨hEv, mem_iUnion.2 ⟨m, hnn'.trans hm1, hm2⟩⟩
  have hAinter : (⋂ n, A n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨hEv, -⟩ := h 0
    obtain ⟨N, hN⟩ := mem_iUnion.1 hEv
    obtain ⟨-, hω⟩ := h N
    obtain ⟨m, hm1, hm2⟩ := mem_iUnion.1 hω
    have hle : B m ω ≤ ENNReal.ofReal (κ / 2) := mem_iInter.1 hN m hm1
    have hlt : ENNReal.ofReal (κ / 2) < ENNReal.ofReal κ :=
      (ENNReal.ofReal_lt_ofReal_iff hκ).2 (by linarith)
    exact absurd (hm2.trans_le hle) (not_lt.2 hlt.le)
  have hAlim : Tendsto (fun n => S.P (A n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hAm hAanti ⟨0, measure_ne_top _ _⟩
    rwa [hAinter, measure_empty] at h
  -- the exponent of the cell-size estimate
  have hζ0 : (0 : ℝ) < 1 / (2 + γ) ^ 2 := by positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hb : 0 < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    rw [div_sub_div_same]
    norm_num
    positivity
  have hcell := S5e.tendsToOneOn_of_polyHighProb {ω | t < clusterExitTime (Λ ω) ρ}
    (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮 γ hγ hγ2 (1 / (2 + γ) ^ 2) ρ hζ0 hζ1 hρ hρ1 Ω S hS)
  unfold TendsToOneOn
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he3 : (0 : ℝ≥0∞) < e / 3 := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  have hsideρ : ∀ᶠ n : ℕ in atTop, side n < ρ := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [side] using h.eventually (gt_mem_nhds hρ)
  obtain ⟨n, hnρ, hnA⟩ := (hsideρ.and (ENNReal.tendsto_nhds_zero.1 hAlim (e / 3) he3)).exists
  have hinnerT := hinner γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (side n) t (side_pos n) hnρ ht
  have hpow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) < side n :=
    (tendsto_rpow_nhdsGT_zero_zero hb).eventually (gt_mem_nhds (side_pos n))
  filter_upwards [self_mem_nhdsWithin, hpow, ENNReal.tendsto_nhds_zero.1 hcell (e / 3) he3,
    ENNReal.tendsto_nhds_zero.1 hinnerT (e / 3) he3] with ε hε hεd hεC hεI
  have hεpos : 0 < ε := hε
  have hsub : {ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ε * ((cellVertices ε (S.η ω) (Λ ω t) \
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ) ≤ κ}ᶜ ⊆
      ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)}ᶜ) ∪
      ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | innerNbhd (side n) (Λ ω t) ⊆
        fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}ᶜ) ∪ A n ∪ Gᶜ := by
    rintro ω ⟨hT, hbad⟩
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_or, not_and, not_not] at hcon
    obtain ⟨⟨⟨hcellω, hinω⟩, hAω⟩, hGω⟩ := hcon
    have hcellω := hcellω hT
    have hinω := hinω hT
    obtain ⟨hcode, hfam, hg, harea, hloc⟩ := hGω
    have hΛeq := hcode hT
    have hreg : interior (closure (Λ ω t)) = Λ ω t :=
      StoppedInteriorMargin.interior_closure_eq_self_of_eq hΛeq
    have hΛR : Λ ω t ⊆ ball 0 (ρ / 3) :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hfam.2.1.monotoneOn ht hT
    have hΛB : Λ ω t ⊆ ball 0 1 := hΛR.trans (ball_subset_ball (by linarith))
    simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hbad
    by_cases hfin : (cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite
    · have hbound := eps_mul_card_missing_le harea hreg hΛB hεpos n hinω (fun k hk => by
        obtain ⟨y, hyk, hyΛ⟩ := id hk
        exact (hcellω k ⟨y, hyk, ball_subset_ball (by linarith) (hΛR hyΛ)⟩).2.trans hεd.le) hfin
      have hBn : squareBound (S.μ ω) (Λ ω t) n = B n ω := by
        simp only [hBdef]
        rw [hg, hΛeq]
      rw [hBn] at hbound
      apply hAω
      refine ⟨?_, mem_iUnion.2 ⟨n, le_rfl, ?_⟩⟩
      · obtain ⟨N, hN⟩ := eventually_atTop.1 ((hconv ω ⟨hcode, hfam, hg, harea, hloc⟩ hT).eventually
          (ge_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hκ))))
        exact mem_iUnion.2 ⟨N, mem_iInter.2 fun m hm => hN m hm⟩
      · exact ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hbad).trans_le hbound
    · rw [Set.Infinite.ncard hfin, Nat.cast_zero, mul_zero] at hbad
      linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hG, add_zero]
  refine (measure_union_le _ _).trans ((add_le_add ((measure_union_le _ _).trans (add_le_add hεC hεI)) hnA).trans ?_)
  exact (ENNReal.add_thirds e).le

end StoppedMissing

end MatedCRT
