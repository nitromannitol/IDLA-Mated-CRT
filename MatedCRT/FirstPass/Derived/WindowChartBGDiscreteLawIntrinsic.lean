import MatedCRT.FirstPass.Derived.CellSideMult
import MatedCRT.FirstPass.Derived.WindowChartBGFieldIntrinsic
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring

/-!
# The discrete window laws of Berestycki–Gwynne as functions of the intrinsic wedges

Step of the proof of Lemma 7.21 of Berestycki–Gwynne (arXiv:2003.10320, 2003.10320.txt lines 3783-3831) with the two
quantum surfaces of (7.35) taken as intrinsic curve-decorated wedges: `BG20DiscreteWindowLawIntrinsicInput`
(`WindowChartBGIntrinsicIndependence.lean`), following the written answers MQ-sbl-21 (Q2) and MQ-sbl-31.

For a window `(a, u, b)`, a time interval `[p, q] ⊃ [a, b]` and a cell size `ε > 0`, the **frozen window law**
`frozenWindowLaw` is the law of the following walk, drawn in the intrinsic chart `ψ = windowChartIntr` of the window
(the inverse of the normalized conformal map of the open unit disc onto the window domain `U`):
* the labels `j` whose cell interval `[ε(j-1), εj]` lies in `[p, q]` are retained, and the cells `η([ε(j-1), εj])` of
  retained labels contained in `U` are inside (`WindowCellInside`);
* the walk starts from the label `⌈u/ε⌉`; from an inside cell `i` it moves to a retained label `j` with probability
  proportional to the weight `m i j`; it is frozen at its current position before its first step to a cell which is
  not inside (`frozenSeq`);
* its positions `ψ(η(εj))` are interpolated linearly at the time step `1/mε` (`interpPathCM`).
For the weights `cellSideMult ε η` (the frontier-side multiplicities read off the curve, `CellSideMult.lean`) the frozen
window law is a Borel function of the curve (`measurable_frozenWindowLaw`), and it takes the same value at two pairs
(field, curve) with the same intrinsic curve-decorated surface over a set of times `T ⊇ [p, q]`
(`IsIntrinsicCurveDecoratedReembedding.frozenWindowLaw_eq`): the re-embedding `f` maps the window domains onto each
other, `ψ₁ ∘ f = ψ₂` on `U₂`, and a contact of two cells through a point of `U` is carried by `f` and its inverse
(`cellSideMult_eq_of_map`, written answer MQ-sbl-31, lines 44-46).

The main result `bg20DiscreteWindowLawIntrinsicInput_of_cellSideIdentity` derives `BG20DiscreteWindowLawIntrinsicInput`
from two steps on the paper's objects:
* `MatingOfTreesCellSideIdentity`: the multiplicities of the mated-CRT map (Definition 1.1) are almost surely the
  frontier-side multiplicities of the cells (written answer MQ-sbl-31, lines 26-40);
* `BG20FrozenWindowLawComparison`: for the multiplicities of the map, the frozen window law is close in probability to
  the chart law of the window for the interpolated walk law (Berestycki–Gwynne, lines 3812-3831; written answer
  MQ-sbl-21, Q2).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

/-! ### The multiplicities of the map are the frontier-side multiplicities of the cells -/

/-- **Step (written answer MQ-sbl-31, lines 26-40): the edge multiplicities of the mated-CRT map are the frontier-side
multiplicities of the cells of the space-filling SLE.** PENDING TRUTH CHECK.

In a valid environment, for every cell size `ε > 0`, almost surely the multiplicity `S.mult ε` of Definition 1.1 (read
off the boundary-length pair, `MatedCRTEnv.mult`) equals `cellSideMult ε (S.η)`, the number of frontier sides shared by
two cells, read off the curve (`CellSideMult.lean`). Sources: Duplantier–Miller–Sheffield, arXiv:1409.7055, Theorem
8.18 and Lemmas 8.8, 8.12-8.15 (1409.7055.txt lines 8042-8370); Gwynne–Holden–Miller, arXiv:1512.01223, Corollary 6.5
(1512.01223.txt line 2742); Gwynne–Miller–Sheffield, arXiv:1705.11161, §2.5 and Proposition 2.2. -/
def MatingOfTreesCellSideIdentity (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, S.mult ε ω = cellSideMult ε (S.η ω)

/-! ### Contacts through an open set are carried by injective continuous maps -/

/-- Closed rational intervals about a point of `(a, d)`, inside `(a, d)` and of radius less than `δ`. -/
theorem exists_rat_Ioo_subset {v a d δ : ℝ} (hv : v ∈ Ioo a d) (hδ : 0 < δ) :
    ∃ p₁ p₂ : ℚ, v ∈ Ioo (p₁ : ℝ) p₂ ∧ Icc (p₁ : ℝ) p₂ ⊆ Ioo a d ∧ Icc (p₁ : ℝ) p₂ ⊆ Ioo (v - δ) (v + δ) := by
  have hδ' : 0 < min δ (min (v - a) (d - v)) := lt_min hδ (lt_min (by linarith [hv.1]) (by linarith [hv.2]))
  have h1 : min δ (min (v - a) (d - v)) ≤ δ := min_le_left _ _
  have h2 : min δ (min (v - a) (d - v)) ≤ v - a := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min δ (min (v - a) (d - v)) ≤ d - v := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p₁, hp₁⟩ := exists_rat_btwn (show v - min δ (min (v - a) (d - v)) < v by linarith)
  obtain ⟨p₂, hp₂⟩ := exists_rat_btwn (show v < v + min δ (min (v - a) (d - v)) by linarith)
  refine ⟨p₁, p₂, ⟨hp₁.2, hp₂.1⟩, fun x hx => ⟨by linarith [hx.1, hp₁.1], by linarith [hx.2, hp₂.2]⟩,
    fun x hx => ⟨by linarith [hx.1, hp₁.1], by linarith [hx.2, hp₂.2]⟩⟩

/-- **A contact joins two points of the same image**: `D_η(v, w)` for distinct times `v, w ∈ (a, d)` of a continuous
curve forces `η(v) = η(w)`. -/
theorem eq_of_cellSideContact {a d v w : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hvd : v ∈ Ioo a d)
    (hwd : w ∈ Ioo a d) (hvw : v ≠ w) (hD : cellSideContact a d η v w) : η v = η w := by
  by_contra hne
  have hr0 : 0 < dist (η v) (η w) / 3 := by have := dist_pos.2 hne; positivity
  obtain ⟨δv, hδv, hcv⟩ := Metric.continuous_iff.1 hη v _ hr0
  obtain ⟨δw, hδw, hcw⟩ := Metric.continuous_iff.1 hη w _ hr0
  have hvw' : 0 < |v - w| := abs_pos.2 (sub_ne_zero.2 hvw)
  have hδ0 : 0 < min (min δv δw) (|v - w| / 2) := lt_min (lt_min hδv hδw) (by positivity)
  have h1 : min (min δv δw) (|v - w| / 2) ≤ δv := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : min (min δv δw) (|v - w| / 2) ≤ δw := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : min (min δv δw) (|v - w| / 2) ≤ |v - w| / 2 := min_le_right _ _
  obtain ⟨p₁, p₂, hvp, hP, hPδ⟩ := exists_rat_Ioo_subset hvd hδ0
  obtain ⟨q₁, q₂, hwq, hQ, hQδ⟩ := exists_rat_Ioo_subset hwd hδ0
  have hdisj : Disjoint (Ioo (p₁ : ℝ) p₂) (Ioo (q₁ : ℝ) q₂) := by
    rw [Set.disjoint_left]
    intro x hxP hxQ
    have hx1 := hPδ (Ioo_subset_Icc_self hxP)
    have hx2 := hQδ (Ioo_subset_Icc_self hxQ)
    have key : |v - w| < 2 * min (min δv δw) (|v - w| / 2) := by
      rw [abs_lt]
      constructor <;> linarith [hx1.1, hx1.2, hx2.1, hx2.2]
    linarith
  obtain ⟨K, hK, -, hKc, -⟩ := hD p₁ p₂ q₁ q₂ hvp hwq hdisj hP hQ
  obtain ⟨z, hz⟩ := hKc.nonempty
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := hK hz
  have hx' := hPδ hx
  have hy' := hQδ hy
  have e1 : dist (η x) (η v) < dist (η v) (η w) / 3 :=
    hcv x (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx'.1, hx'.2])
  have e2 : dist (η y) (η w) < dist (η v) (η w) / 3 :=
    hcw y (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy'.1, hy'.2])
  rw [hxy] at e2
  have e3 := dist_triangle_left (η v) (η w) (η x)
  linarith

/-- Closed rational intervals about `v` inside a given open rational interval about `v`, inside `(a, d)`, on which the
curve stays in an open set `W` containing `η(v)`. -/
theorem exists_rat_sub_of_mem {v a d : ℝ} {p₁ p₂ : ℚ} (hvd : v ∈ Ioo a d) (hvp : v ∈ Ioo (p₁ : ℝ) p₂)
    {η : ℝ → ℂ} (hη : Continuous η) {W : Set ℂ} (hW : IsOpen W) (hv : η v ∈ W) :
    ∃ p₁' p₂' : ℚ, v ∈ Ioo (p₁' : ℝ) p₂' ∧ Icc (p₁' : ℝ) p₂' ⊆ Ioo a d ∧ Icc (p₁' : ℝ) p₂' ⊆ Ioo (p₁ : ℝ) p₂ ∧
      η '' Icc (p₁' : ℝ) p₂' ⊆ W := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hW _ hv
  obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuous_iff.1 hη v ρ hρ
  have hδ : 0 < min δ₀ (min (v - p₁) (p₂ - v)) :=
    lt_min hδ₀ (lt_min (by linarith [hvp.1]) (by linarith [hvp.2]))
  have h1 : min δ₀ (min (v - p₁) (p₂ - v)) ≤ δ₀ := min_le_left _ _
  have h2 : min δ₀ (min (v - p₁) (p₂ - v)) ≤ v - p₁ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min δ₀ (min (v - p₁) (p₂ - v)) ≤ p₂ - v := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p₁', p₂', hv', hsub, hsubδ⟩ := exists_rat_Ioo_subset hvd hδ
  refine ⟨p₁', p₂', hv', hsub, fun x hx => ?_, ?_⟩
  · have hx' := hsubδ hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := hsubδ hx
    apply hball
    rw [mem_ball]
    apply hcont
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx'.1, hx'.2]

/-- **A contact through an open set `W` is carried by a continuous map `g`, injective on `W`,** relating the curves at
the times of `(a, d)` at which `η₂` visits `W`. -/
theorem cellSideContact_of_map {a d v w : ℝ} {η₁ η₂ : ℝ → ℂ} {W : Set ℂ} (hW : IsOpen W) {g : ℂ → ℂ}
    (hg : ContinuousOn g W) (hgi : InjOn g W) (hη₂ : Continuous η₂)
    (hrel : ∀ t ∈ Ioo a d, η₂ t ∈ W → η₁ t = g (η₂ t)) (hvd : v ∈ Ioo a d) (hwd : w ∈ Ioo a d)
    (hv : η₂ v ∈ W) (hw : η₂ w ∈ W) (hD : cellSideContact a d η₂ v w) : cellSideContact a d η₁ v w := by
  intro p₁ p₂ q₁ q₂ hvp hwq hdisj hP hQ
  obtain ⟨p₁', p₂', hvp', hP', hPP, hPW⟩ := exists_rat_sub_of_mem hvd hvp hη₂ hW hv
  obtain ⟨q₁', q₂', hwq', hQ', hQQ, hQW⟩ := exists_rat_sub_of_mem hwd hwq hη₂ hW hw
  have hdisj' : Disjoint (Ioo (p₁' : ℝ) p₂') (Ioo (q₁' : ℝ) q₂') :=
    hdisj.mono (Ioo_subset_Icc_self.trans hPP) (Ioo_subset_Icc_self.trans hQQ)
  obtain ⟨K, hK, hKc, hKconn, hKd⟩ := hD p₁' p₂' q₁' q₂' hvp' hwq' hdisj' hP' hQ'
  have hKW : K ⊆ W := fun z hz => hPW (hK hz).1
  have himg : ∀ r₁ r₂ s₁ s₂ : ℚ, Icc (r₁ : ℝ) r₂ ⊆ Ioo a d → Icc (r₁ : ℝ) r₂ ⊆ Ioo (s₁ : ℝ) s₂ →
      η₂ '' Icc (r₁ : ℝ) r₂ ⊆ W → g '' (η₂ '' Icc (r₁ : ℝ) r₂) ⊆ η₁ '' Icc (s₁ : ℝ) s₂ := by
    rintro r₁ r₂ s₁ s₂ hr hrs hrW _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, Ioo_subset_Icc_self (hrs ht), hrel t (hr ht) (hrW ⟨t, ht, rfl⟩)⟩
  refine ⟨g '' K, ?_, hKc.image_of_continuousOn (hg.mono hKW), hKconn.image g (hg.mono hKW), ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨himg _ _ _ _ hP' hPP hPW ⟨y, (hK hy).1, rfl⟩, himg _ _ _ _ hQ' hQQ hQW ⟨y, (hK hy).2, rfl⟩⟩
  · have hns : ¬ K.Subsingleton := fun h => by
      rw [Metric.diam_subsingleton h] at hKd
      exact lt_irrefl 0 hKd
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hns
    have hb := (hKc.image_of_continuousOn (hg.mono hKW)).isBounded
    have hgxy : g x ≠ g y := fun h => hxy (hgi (hKW hx) (hKW hy) h)
    exact (dist_pos.2 hgxy).trans_le (Metric.dist_le_diam_of_mem hb ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-- **The branch times of the shared sides are carried by `g`** when one of the two cells stays in `W`: every witness
triple `(s, u, t)` has `η₂(s) = η₂(u) = η₂(t)`, a point of `W`. -/
theorem cellSideBranchTimes_subset_of_map {a b c d : ℝ} {η₁ η₂ : ℝ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    {g : ℂ → ℂ} (hg : ContinuousOn g W) (hgi : InjOn g W) (hη₂ : Continuous η₂)
    (hrel : ∀ t ∈ Ioo a d, η₂ t ∈ W → η₁ t = g (η₂ t))
    (hcell : (∀ s ∈ Ioo a b, η₂ s ∈ W) ∨ ∀ t ∈ Ioo c d, η₂ t ∈ W) :
    cellSideBranchTimes a b c d η₂ ⊆ cellSideBranchTimes a b c d η₁ := by
  rintro x ⟨hx, s, hs, t, ht, h1, h2, h3⟩
  have hsd : s ∈ Ioo a d := ⟨hs.1, by linarith [hs.2, hx.1, hx.2, ht.1, ht.2]⟩
  have hxd : x ∈ Ioo a d := ⟨by linarith [hs.1, hs.2, hx.1], by linarith [hx.2, ht.1, ht.2]⟩
  have htd : t ∈ Ioo a d := ⟨by linarith [hs.1, hs.2, hx.1, hx.2, ht.1], ht.2⟩
  have e1 : η₂ s = η₂ x := eq_of_cellSideContact hη₂ hsd hxd (ne_of_lt (by linarith [hs.2, hx.1])) h1
  have e2 : η₂ x = η₂ t := eq_of_cellSideContact hη₂ hxd htd (ne_of_lt (by linarith [hx.2, ht.1])) h2
  have hsW : η₂ s ∈ W := by
    rcases hcell with hc | hc
    · exact hc s hs
    · rw [e1, e2]
      exact hc t ht
  have hxW : η₂ x ∈ W := by
    rw [← e1]
    exact hsW
  have htW : η₂ t ∈ W := by
    rw [← e2]
    exact hxW
  exact ⟨hx, s, hs, t, ht, cellSideContact_of_map hW hg hgi hη₂ hrel hsd hxd hsW hxW h1,
    cellSideContact_of_map hW hg hgi hη₂ hrel hxd htd hxW htW h2,
    cellSideContact_of_map hW hg hgi hη₂ hrel hsd htd hsW htW h3⟩

/-- The count of shared sides is carried by maps in both directions. -/
theorem cellSideCount_eq_of_map {a b c d : ℝ} {η₁ η₂ : ℝ → ℂ} {W₁ W₂ : Set ℂ} (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) {g₁ g₂ : ℂ → ℂ} (hg₁ : ContinuousOn g₁ W₁) (hgi₁ : InjOn g₁ W₁)
    (hg₂ : ContinuousOn g₂ W₂) (hgi₂ : InjOn g₂ W₂) (hη₁ : Continuous η₁) (hη₂ : Continuous η₂)
    (hrel₁ : ∀ t ∈ Ioo a d, η₂ t ∈ W₂ → η₁ t = g₂ (η₂ t))
    (hrel₂ : ∀ t ∈ Ioo a d, η₁ t ∈ W₁ → η₂ t = g₁ (η₁ t))
    (hcell₁ : (∀ s ∈ Ioo a b, η₁ s ∈ W₁) ∨ ∀ t ∈ Ioo c d, η₁ t ∈ W₁)
    (hcell₂ : (∀ s ∈ Ioo a b, η₂ s ∈ W₂) ∨ ∀ t ∈ Ioo c d, η₂ t ∈ W₂) :
    cellSideCount a b c d η₁ = cellSideCount a b c d η₂ := by
  have h : cellSideBranchTimes a b c d η₁ = cellSideBranchTimes a b c d η₂ :=
    Subset.antisymm (cellSideBranchTimes_subset_of_map hW₁ hg₁ hgi₁ hη₁ hrel₂ hcell₁)
      (cellSideBranchTimes_subset_of_map hW₂ hg₂ hgi₂ hη₂ hrel₁ hcell₂)
  unfold cellSideCount
  rw [h]

/-- **The row of the frontier-side multiplicities from a cell is carried by maps in both directions** when the cell
stays in `W₁` and `W₂` and the curves are related on the time interval from the first to the second cell. -/
theorem cellSideMult_eq_of_map {ε : ℝ} {η₁ η₂ : ℝ → ℂ} {W₁ W₂ : Set ℂ} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    {g₁ g₂ : ℂ → ℂ} (hg₁ : ContinuousOn g₁ W₁) (hgi₁ : InjOn g₁ W₁) (hg₂ : ContinuousOn g₂ W₂)
    (hgi₂ : InjOn g₂ W₂) (hη₁ : Continuous η₁) (hη₂ : Continuous η₂) {i j : ℤ}
    (hrel₁ : ∀ t ∈ Ioo (ε * ((min i j : ℤ) - 1 : ℝ)) (ε * (max i j : ℤ)), η₂ t ∈ W₂ → η₁ t = g₂ (η₂ t))
    (hrel₂ : ∀ t ∈ Ioo (ε * ((min i j : ℤ) - 1 : ℝ)) (ε * (max i j : ℤ)), η₁ t ∈ W₁ → η₂ t = g₁ (η₁ t))
    (hcell₁ : ∀ t ∈ Icc (ε * ((i : ℝ) - 1)) (ε * i), η₁ t ∈ W₁)
    (hcell₂ : ∀ t ∈ Icc (ε * ((i : ℝ) - 1)) (ε * i), η₂ t ∈ W₂) :
    cellSideMult ε η₁ i j = cellSideMult ε η₂ i j := by
  unfold cellSideMult
  by_cases h0 : ε ≤ 0 ∨ i = j
  · rw [ite_eq_left h0, ite_eq_left h0]
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases h1 : |i - j| = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
  rw [ite_eq_right h1, ite_eq_right h1]
  have hij : i ≠ j := fun h => h0 (Or.inr h)
  have hcases : ∀ {η : ℝ → ℂ} {W : Set ℂ}, (∀ t ∈ Icc (ε * ((i : ℝ) - 1)) (ε * i), η t ∈ W) →
      (∀ s ∈ Ioo (ε * ((min i j : ℤ) - 1 : ℝ)) (ε * (min i j : ℤ)), η s ∈ W) ∨
        ∀ t ∈ Ioo (ε * ((max i j : ℤ) - 1 : ℝ)) (ε * (max i j : ℤ)), η t ∈ W := by
    intro η W hc
    rcases lt_or_gt_of_ne hij with h | h
    · left
      rw [min_eq_left h.le]
      exact fun s hs => hc s (Ioo_subset_Icc_self hs)
    · right
      rw [max_eq_left h.le]
      exact fun s hs => hc s (Ioo_subset_Icc_self hs)
  exact cellSideCount_eq_of_map hW₁ hW₂ hg₁ hgi₁ hg₂ hgi₂ hη₁ hη₂ hrel₁ hrel₂ (hcases hcell₁) (hcases hcell₂)

/-! ### The cells inside the window -/

/-- The label `j` is **retained** for the time interval `[p, q]`: its cell interval `[ε(j-1), εj]` lies in `[p, q]`. -/
def WindowRetained (p q ε : ℝ) (j : ℤ) : Prop :=
  p ≤ ε * ((j : ℝ) - 1) ∧ ε * j ≤ q

/-- The cell of label `j` is **inside the window `(a, u, b)`**: `j` is retained for `[p, q]`, and at the rational
times of its interval the curve lies in the window domain `U` with values of the intrinsic chart in a closed disc of
radius `r < 1`. For a window with an intrinsic chart this says that the cell `η([ε(j-1), εj])` lies in `U`
(`WindowGoodIntr.windowCellInside_iff_subset`). -/
def WindowCellInside (a u b p q ε : ℝ) (η : C(ℝ, ℂ)) (j : ℤ) : Prop :=
  WindowRetained p q ε j ∧ ∃ r : ℚ, (r : ℝ) < 1 ∧ ∀ t : ℚ, (t : ℝ) ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j) →
    η (t : ℝ) ∈ windowDomain η a u b ∧ ‖windowChartIntr a u b η (η (t : ℝ))‖ ≤ r

theorem measurableSet_setOf_windowCellInside (a u b p q ε : ℝ) (j : ℤ) :
    MeasurableSet {η : C(ℝ, ℂ) | WindowCellInside a u b p q ε η j} := by
  unfold WindowCellInside
  refine measurableSet_setOfPred.2 (Measurable.and measurable_const (Measurable.exists fun r =>
    Measurable.and measurable_const (Measurable.forall fun t => measurable_const.imp (Measurable.and ?_ ?_))))
  · exact measurableSet_setOfPred.1 (measurableSet_setOf_mem_windowDomain a u b (continuous_eval_const _).measurable)
  · exact measurableSet_setOfPred.1 (measurableSet_le ((measurable_windowChartIntr a u b).comp
      (measurable_id.prodMk (continuous_eval_const _).measurable)).norm measurable_const)

/-- An inside cell lies in the window domain. -/
theorem WindowGoodIntr.mem_windowDomain_of_windowCellInside {a u b p q ε : ℝ} {η : C(ℝ, ℂ)}
    (hG : WindowGoodIntr a u b η) (hε : 0 < ε) {j : ℤ} (hj : WindowCellInside a u b p q ε η j) {t : ℝ}
    (ht : t ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j)) : η t ∈ windowDomain η a u b := by
  obtain ⟨-, r, hr, hrat⟩ := hj
  have hφ := hG.isOpenDiscMap
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hr
  have hK : IsCompact (windowDiscMapIntr a u b η '' closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) (r : ℝ)).image_of_continuousOn (hφ.differentiableOn.continuousOn.mono hsub)
  have hKU : windowDiscMapIntr a u b η '' closedBall (0 : ℂ) r ⊆ windowDomain η a u b := by
    rw [← hφ.image_ball]
    exact image_mono hsub
  have hcd : ε * ((j : ℝ) - 1) < ε * j := by
    rw [mul_sub, mul_one]
    linarith
  have hA : η '' (Ioo (ε * ((j : ℝ) - 1)) (ε * j) ∩ range ((↑) : ℚ → ℝ)) ⊆
      windowDiscMapIntr a u b η '' closedBall (0 : ℂ) r := by
    rintro _ ⟨_, ⟨hx, s, rfl⟩, rfl⟩
    obtain ⟨hU, hle⟩ := hrat s (Ioo_subset_Icc_self hx)
    exact ⟨windowChartIntr a u b η (η s), mem_closedBall_zero_iff.2 hle, hG.windowDiscMapIntr_windowChartIntr hU⟩
  have hcl : t ∈ closure (Ioo (ε * ((j : ℝ) - 1)) (ε * j) ∩ range ((↑) : ℚ → ℝ)) := by
    have h1 : Ioo (ε * ((j : ℝ) - 1)) (ε * j) ⊆
        closure (Ioo (ε * ((j : ℝ) - 1)) (ε * j) ∩ range ((↑) : ℚ → ℝ)) :=
      Dense.open_subset_closure_inter (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)) isOpen_Ioo
    have h2 := closure_minimal h1 isClosed_closure
    rw [closure_Ioo hcd.ne] at h2
    exact h2 ht
  exact hKU (hK.isClosed.closure_subset_iff.2 hA (image_closure_subset_closure_image η.continuous ⟨t, hcl, rfl⟩))

/-- For a window with an intrinsic chart, a retained cell is inside exactly when it lies in the window domain. -/
theorem WindowGoodIntr.windowCellInside_iff_subset {a u b p q ε : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (hε : 0 < ε) (j : ℤ) : WindowCellInside a u b p q ε η j ↔
      WindowRetained p q ε j ∧ ∀ t ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j), η t ∈ windowDomain η a u b := by
  constructor
  · exact fun h => ⟨h.1, fun t ht => hG.mem_windowDomain_of_windowCellInside hε h ht⟩
  rintro ⟨hret, hin⟩
  refine ⟨hret, ?_⟩
  have hcont : ContinuousOn (fun t => windowChartIntr a u b η (η t)) (Icc (ε * ((j : ℝ) - 1)) (ε * j)) :=
    hG.differentiableOn_windowChartIntr.continuousOn.comp η.continuous.continuousOn fun t ht => hin t ht
  have hKb : (fun t => windowChartIntr a u b η (η t)) '' Icc (ε * ((j : ℝ) - 1)) (ε * j) ⊆ ball (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩
    exact windowChartIntr_mem_ball a u b η _
  obtain ⟨r', hr', hsub⟩ := exists_lt_subset_ball (isCompact_Icc.image_of_continuousOn hcont).isClosed hKb
  obtain ⟨r, hr'r, hr1⟩ := exists_rat_btwn hr'
  refine ⟨r, hr1, fun t ht => ⟨hin t ht, ?_⟩⟩
  have h := hsub ⟨t, ht, rfl⟩
  rw [mem_ball_zero_iff] at h
  exact (h.trans hr'r).le

/-! ### The frozen walk -/

open Classical in
/-- **The walk frozen before its first step out of `A`**: `x k` while `x 0, …, x k` all lie in `A`, afterwards the last
of these positions (and `x 0` throughout if `x 0 ∉ A`). -/
noncomputable def frozenSeq (A : Set ℤ) (x : ℕ → ℤ) : ℕ → ℤ
  | 0 => x 0
  | k + 1 => if ∀ i ≤ k + 1, x i ∈ A then x (k + 1) else frozenSeq A x k

theorem measurable_mem_of {X : Type*} [MeasurableSpace X] {A : X → Set ℤ}
    (hA : ∀ j, MeasurableSet {ξ | j ∈ A ξ}) (i : ℕ) :
    Measurable fun z : X × (ℕ → ℤ) => z.2 i ∈ A z.1 :=
  (measurable_from_prod_countable_left (f := fun z : X × ℤ => z.2 ∈ A z.1)
    fun j => measurableSet_setOfPred.1 (hA j)).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem measurable_frozenSeq {X : Type*} [MeasurableSpace X] {A : X → Set ℤ}
    (hA : ∀ j, MeasurableSet {ξ | j ∈ A ξ}) :
    Measurable fun z : X × (ℕ → ℤ) => frozenSeq (A z.1) z.2 := by
  refine measurable_pi_iff.2 fun k => ?_
  induction k with
  | zero => exact (measurable_pi_apply 0).comp measurable_snd
  | succ k ih =>
    have hS : MeasurableSet {z : X × (ℕ → ℤ) | ∀ i ≤ k + 1, z.2 i ∈ A z.1} :=
      measurableSet_setOfPred.2 (Measurable.forall fun i => measurable_const.imp (measurable_mem_of hA i))
    simp only [frozenSeq]
    exact Measurable.ite hS ((measurable_pi_apply (k + 1)).comp measurable_snd) ih

theorem measurable_frozenSeq_const (A : Set ℤ) : Measurable (frozenSeq A) :=
  (measurable_frozenSeq (X := Unit) (A := fun _ => A) fun _ => MeasurableSet.const _).comp
    ((measurable_const (a := ())).prodMk measurable_id)

/-- The walk laws from `j₀` for the weights `W ξ`, as a kernel. -/
noncomputable def frozenWalkKernel {X : Type*} [MeasurableSpace X] {W : X → ℤ → ℤ → ℕ} (hW : Measurable W)
    (j₀ : ℤ) : Kernel X (ℕ → ℤ) :=
  ⟨fun ξ => srwLaw (W ξ) j₀, (measurable_srwLaw j₀).comp hW⟩

instance {X : Type*} [MeasurableSpace X] {W : X → ℤ → ℤ → ℕ} (hW : Measurable W) (j₀ : ℤ) :
    IsMarkovKernel (frozenWalkKernel hW j₀) :=
  ⟨fun ξ => isProbabilityMeasure_srwLaw (W ξ) j₀⟩

/-- **The law of the frozen walk path**: the walk with weights `W` from `j₀`, frozen before its first step out of
`A`, with positions `V` interpolated linearly at the time step `1/mε`. -/
noncomputable def frozenWalkPathLaw (j₀ : ℤ) (A : Set ℤ) (V : ℤ → ℂ) (W : ℤ → ℤ → ℕ) {mε : ℝ} (hm : 0 ≤ mε) :
    ProbabilityMeasure (ContinuousPath ℂ) :=
  ⟨(srwLaw W j₀).map fun x => interpPathCM V hm (frozenSeq A x),
    (Measure.isProbabilityMeasure_map_iff
      ((measurable_interpPathCM V hm).comp (measurable_frozenSeq_const A)).aemeasurable).2 inferInstance⟩

theorem measurable_frozenWalkPathLaw {X : Type*} [MeasurableSpace X] (j₀ : ℤ) {A : X → Set ℤ}
    {V : X → ℤ → ℂ} {W : X → ℤ → ℤ → ℕ} (hA : ∀ j, MeasurableSet {ξ | j ∈ A ξ}) (hV : Measurable V)
    (hW : Measurable W) {mε : ℝ} (hm : 0 ≤ mε) :
    Measurable fun ξ => frozenWalkPathLaw j₀ (A ξ) (V ξ) (W ξ) hm := by
  unfold frozenWalkPathLaw
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hT : MeasurableSet {z : X × (ℕ → ℤ) | interpPathCM (V z.1) hm (frozenSeq (A z.1) z.2) ∈ s} :=
    (measurable_interpPathCM_uncurry hm).comp ((hV.comp measurable_fst).prodMk (measurable_frozenSeq hA)) hs
  have key := (frozenWalkKernel hW j₀).measurable_kernel_prodMk_left hT
  convert key using 1
  funext ξ
  exact Measure.map_apply ((measurable_interpPathCM (V ξ) hm).comp (measurable_frozenSeq_const (A ξ))) hs

/-! ### The frozen window law -/

open Classical in
/-- The positions of the frozen walk in the intrinsic chart: `ψ(η(εj))` for an inside cell, `0` otherwise. -/
noncomputable def frozenChartVertex (a u b p q ε : ℝ) (η : C(ℝ, ℂ)) (j : ℤ) : ℂ :=
  if WindowCellInside a u b p q ε η j then windowChartIntr a u b η (η (ε * j)) else 0

open Classical in
/-- The weights of the frozen walk: the weights `m i j` from an inside cell `i` to a retained label `j`; zero rows at
the other labels. -/
noncomputable def frozenWindowMult (a u b p q ε : ℝ) (η : C(ℝ, ℂ)) (m : ℤ → ℤ → ℕ) (i j : ℤ) : ℕ :=
  if WindowCellInside a u b p q ε η i ∧ WindowRetained p q ε j then m i j else 0

open Classical in
/-- **The frozen window law** of the window `(a, u, b)` with retained times `[p, q]` at cell size `ε`, for the weights
`m` (written answer MQ-sbl-21, Q2): the walk on the retained labels from `⌈u/ε⌉` with weights `m` from the inside
cells, frozen before its first step to a cell which is not inside, drawn in the intrinsic chart `windowChartIntr` of
the window and interpolated at the time step `1/mε`. The constant path at `0` if the window has no intrinsic chart or
the starting cell is not inside. -/
noncomputable def frozenWindowLaw (a u b p q ε : ℝ) {mε : ℝ} (hm : 0 ≤ mε) (m : ℤ → ℤ → ℕ) (η : C(ℝ, ℂ)) :
    ProbabilityMeasure (ContinuousPath ℂ) :=
  if WindowGoodIntr a u b η ∧ WindowCellInside a u b p q ε η ⌈u / ε⌉ then
    frozenWalkPathLaw ⌈u / ε⌉ {j | WindowCellInside a u b p q ε η j} (frozenChartVertex a u b p q ε η)
      (frozenWindowMult a u b p q ε η m) hm
  else frozenWalkPathLaw 0 ∅ (fun _ => 0) (fun _ _ => 0) hm

theorem measurable_frozenChartVertex (a u b p q ε : ℝ) : Measurable (frozenChartVertex a u b p q ε) := by
  refine measurable_pi_iff.2 fun j => ?_
  have h := (measurable_windowChartIntr a u b).comp
    (measurable_id'.prodMk (continuous_eval_const (ε * (j : ℝ)) : Continuous fun η : C(ℝ, ℂ) => η (ε * j)).measurable)
  simp only [Function.comp_def] at h
  unfold frozenChartVertex
  exact Measurable.ite (measurableSet_setOf_windowCellInside a u b p q ε j) h measurable_const

theorem measurable_frozenWindowMult (a u b p q ε : ℝ) {M : C(ℝ, ℂ) → ℤ → ℤ → ℕ} (hM : Measurable M) :
    Measurable fun η => frozenWindowMult a u b p q ε η (M η) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  unfold frozenWindowMult
  exact Measurable.ite (measurableSet_setOfPred.2 (Measurable.and
      (measurableSet_setOfPred.1 (measurableSet_setOf_windowCellInside a u b p q ε i)) measurable_const))
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)) measurable_const

/-- **The frozen window law is a Borel function of the curve** for weights read off the curve measurably. -/
theorem measurable_frozenWindowLaw (a u b p q ε : ℝ) {mε : ℝ} (hm : 0 ≤ mε) {M : C(ℝ, ℂ) → ℤ → ℤ → ℕ}
    (hM : Measurable M) : Measurable fun η => frozenWindowLaw a u b p q ε hm (M η) η := by
  unfold frozenWindowLaw
  refine Measurable.ite (measurableSet_setOfPred.2 (Measurable.and
      (measurableSet_setOfPred.1 (measurableSet_setOf_windowGoodIntr a u b))
      (measurableSet_setOfPred.1 (measurableSet_setOf_windowCellInside a u b p q ε _)))) ?_ measurable_const
  exact measurable_frozenWalkPathLaw _ (A := fun η => {j | WindowCellInside a u b p q ε η j})
    (V := frozenChartVertex a u b p q ε) (W := fun η => frozenWindowMult a u b p q ε η (M η))
    (fun j => measurableSet_setOf_windowCellInside a u b p q ε j) (measurable_frozenChartVertex a u b p q ε)
    (measurable_frozenWindowMult a u b p q ε hM) hm

/-! ### Invariance under intrinsic re-embedding -/

namespace IsIntrinsicCurveDecoratedReembedding

variable {γ : ℝ} {T : Set ℝ} {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ} {a u b p q ε : ℝ}

/-- **The intrinsic charts correspond under `f`**: `ψ₁ ∘ f = ψ₂` on the window domain of `η₂`. -/
theorem windowChartIntr_map_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (hG₂ : WindowGoodIntr a u b η₂) {x : ℂ} (hx : x ∈ windowDomain η₂ a u b) :
    windowChartIntr a u b η₁ (f x) = windowChartIntr a u b η₂ x := by
  have hG₁ := (hf.windowGoodIntr_iff hJ hu).2 hG₂
  have hw := windowChartIntr_mem_ball a u b η₂ x
  have h1 := hG₂.windowDiscMapIntr_windowChartIntr hx
  have h2 := hf.windowDiscMapIntr_eq hJ hu hG₂ hw
  rw [h1] at h2
  rw [← h2, hG₁.windowChartIntr_windowDiscMapIntr hw]

/-- **Inside cells correspond under `f`.** -/
theorem windowCellInside_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (hpq : Icc p q ⊆ T) (hG₂ : WindowGoodIntr a u b η₂) (j : ℤ) :
    WindowCellInside a u b p q ε η₁ j ↔ WindowCellInside a u b p q ε η₂ j := by
  unfold WindowCellInside
  refine and_congr_right fun hret => exists_congr fun r => and_congr_right fun _ =>
    forall_congr' fun t => forall_congr' fun ht => ?_
  have htT : (t : ℝ) ∈ T := hpq ⟨hret.1.trans ht.1, ht.2.trans hret.2⟩
  rw [hf.mem_windowDomain_iff hJ hu htT]
  refine and_congr_right fun hU => ?_
  rw [← hf.1 _ htT (windowDomain_subset hJ η₂ u hU), hf.windowChartIntr_map_eq hJ hu hG₂ hU]

/-- **The chart positions of the frozen walk correspond under `f`.** -/
theorem frozenChartVertex_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (hpq : Icc p q ⊆ T) (hG₂ : WindowGoodIntr a u b η₂) (hε : 0 < ε) :
    frozenChartVertex a u b p q ε η₁ = frozenChartVertex a u b p q ε η₂ := by
  funext j
  unfold frozenChartVertex
  by_cases hj : WindowCellInside a u b p q ε η₂ j
  · rw [ite_eq_left ((hf.windowCellInside_iff hJ hu hpq hG₂ j).2 hj), ite_eq_left hj]
    have hmem : ε * (j : ℝ) ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j) := ⟨by rw [mul_sub, mul_one]; linarith, le_rfl⟩
    have hU := hG₂.mem_windowDomain_of_windowCellInside hε hj hmem
    have hT : ε * (j : ℝ) ∈ T := hpq ⟨hj.1.1.trans hmem.1, hj.1.2⟩
    rw [← hf.1 _ hT (windowDomain_subset hJ η₂ u hU), hf.windowChartIntr_map_eq hJ hu hG₂ hU]
  · rw [ite_eq_right fun h => hj ((hf.windowCellInside_iff hJ hu hpq hG₂ j).1 h), ite_eq_right hj]

/-- **The frontier-side multiplicities from an inside cell to a retained label correspond under `f`** (written answer
MQ-sbl-31, line 46): the contacts go through points of the window domains, where `f` and its inverse are continuous and
injective. -/
theorem cellSideMult_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (hpq : Icc p q ⊆ T) (hG₂ : WindowGoodIntr a u b η₂) (hε : 0 < ε) {i j : ℤ}
    (hi : WindowCellInside a u b p q ε η₂ i) (hj : WindowRetained p q ε j) :
    cellSideMult ε η₁ i j = cellSideMult ε η₂ i j := by
  have hG₁ := (hf.windowGoodIntr_iff hJ hu).2 hG₂
  have hi₁ := (hf.windowCellInside_iff hJ hu hpq hG₂ i).2 hi
  have hT : ∀ t ∈ Ioo (ε * ((min i j : ℤ) - 1 : ℝ)) (ε * (max i j : ℤ)), t ∈ T := by
    intro t ht
    have hlo : p ≤ ε * ((min i j : ℤ) - 1 : ℝ) := by
      rcases min_choice i j with h | h <;> rw [h]
      · exact hi.1.1
      · exact hj.1
    have hhi : ε * (max i j : ℤ) ≤ q := by
      rcases max_choice i j with h | h <;> rw [h]
      · exact hi.1.2
      · exact hj.2
    exact hpq ⟨hlo.trans ht.1.le, ht.2.le.trans hhi⟩
  refine cellSideMult_eq_of_map (isOpen_windowDomain η₁ a u b) (isOpen_windowDomain η₂ a u b)
    (hf.differentiableOn_inv.continuousOn.mono (windowDomain_subset hJ η₁ u))
    (hf.injOn_inv.mono (windowDomain_subset hJ η₁ u))
    (hf.2.2.2.1.continuousOn.mono (windowDomain_subset hJ η₂ u))
    (hf.2.2.1.mono (windowDomain_subset hJ η₂ u)) η₁.continuous η₂.continuous ?_ ?_ ?_ ?_
  · intro t ht h
    exact (hf.1 t (hT t ht) (windowDomain_subset hJ η₂ u h)).symm
  · intro t ht h
    have h₂ := (hf.mem_windowDomain_iff hJ hu (hT t ht)).1 h
    rw [← hf.1 t (hT t ht) (windowDomain_subset hJ η₂ u h₂), hf.inv_apply (windowDomain_subset hJ η₂ u h₂)]
  · exact fun t ht => hG₁.mem_windowDomain_of_windowCellInside hε hi₁ ht
  · exact fun t ht => hG₂.mem_windowDomain_of_windowCellInside hε hi ht

/-- **The frozen window law for the frontier-side multiplicities is invariant under intrinsic re-embedding** over a set
of times `T` containing `[a, b]` and the retained times `[p, q]`. -/
theorem frozenWindowLaw_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) (hpq : Icc p q ⊆ T) (hε : 0 < ε) {mε : ℝ} (hm : 0 ≤ mε) :
    frozenWindowLaw a u b p q ε hm (cellSideMult ε η₁) η₁ =
      frozenWindowLaw a u b p q ε hm (cellSideMult ε η₂) η₂ := by
  by_cases hG₂ : WindowGoodIntr a u b η₂
  swap
  · have hG₁ : ¬ WindowGoodIntr a u b η₁ := fun h => hG₂ ((hf.windowGoodIntr_iff hJ hu).1 h)
    unfold frozenWindowLaw
    rw [ite_eq_right fun h => hG₁ h.1, ite_eq_right fun h => hG₂ h.1]
  have hG₁ := (hf.windowGoodIntr_iff hJ hu).2 hG₂
  have hin : ∀ j, WindowCellInside a u b p q ε η₁ j ↔ WindowCellInside a u b p q ε η₂ j :=
    hf.windowCellInside_iff hJ hu hpq hG₂
  have hA : {j | WindowCellInside a u b p q ε η₁ j} = {j | WindowCellInside a u b p q ε η₂ j} := Set.ext hin
  have hV := hf.frozenChartVertex_eq hJ hu hpq hG₂ hε
  have hW : frozenWindowMult a u b p q ε η₁ (cellSideMult ε η₁) =
      frozenWindowMult a u b p q ε η₂ (cellSideMult ε η₂) := by
    funext i j
    unfold frozenWindowMult
    by_cases hij : WindowCellInside a u b p q ε η₂ i ∧ WindowRetained p q ε j
    · rw [ite_eq_left (And.intro ((hin i).2 hij.1) hij.2), ite_eq_left hij]
      exact hf.cellSideMult_eq hJ hu hpq hG₂ hε hij.1 hij.2
    · rw [ite_eq_right fun h => hij ⟨(hin i).1 h.1, h.2⟩, ite_eq_right hij]
  unfold frozenWindowLaw
  rw [hA, hV, hW]
  by_cases h2 : WindowCellInside a u b p q ε η₂ ⌈u / ε⌉
  · rw [ite_eq_left (And.intro hG₁ ((hin _).2 h2)), ite_eq_left (And.intro hG₂ h2)]
  · rw [ite_eq_right fun h => h2 ((hin _).1 h.2), ite_eq_right fun h => h2 h.2]

end IsIntrinsicCurveDecoratedReembedding

/-! ### The comparison with the chart law of the walk -/

/-- **Step of Berestycki–Gwynne (2020), proof of Lemma 7.21 (2003.10320.txt lines 3812-3831): the discrete window law
is close to the chart law of the window for the walk.** Proved: `bg20FrozenWindowLawComparison`
(`BG20FrozenWindowLawComparisonProof.lean`), from the time-change half of Lemma 7.4 of Berestycki–Gwynne, the Jordan
frontier of the window domain (`WindowFrontierJordanInput`) and `JordanDomainExteriorRegularity`.

In a valid environment with a measurable version `η'` of the curve, for every sequence `ε_n → 0`, every window
`a < u < b` and retained times `[p, q]` with `p < a` and `b < q`: for every bounded continuous `g`, the difference of
the integrals of `g` against the frozen window law (`frozenWindowLaw`) for the multiplicities `S.mult (ε n)` of the map
and against the chart law of the window for the interpolated walk law at level `ε n` (`windowLawBG`) tends to zero in
probability. Written argument: answer MQ-sbl-21, Q2 (the comparison with the full interpolated walk: the label walks
agree until freezing, Proposition 6.1 and Lemma 7.17 of Berestycki–Gwynne give the joint limits, the time-changed
Brownian paths visit the open exterior of the window arbitrarily soon after exit, and the inverse chart is uniformly
continuous on the closure of the window), and answer MQ-sbl-31, line 46. -/
def BG20FrozenWindowLawComparison (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ a u b p q : ℝ, p < a → a < u → u < b → b < q →
      ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => S.P {ω | δ ≤
        |∫ x, g x ∂(frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n)) (S.mult (ε n) ω) (η' ω) :
            Measure (ContinuousPath ℂ)) -
          ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0)

/-- The frozen window laws for the frontier-side multiplicities, functions of the intrinsic curve-decorated surface
over `T ⊇ [p, q]`, are close in probability to the chart laws of the window for the walk. -/
theorem exists_intrinsic_frozenWindowLaw {𝒮 : SpaceFillingSLEModel} (hcell : MatingOfTreesCellSideIdentity 𝒮)
    (hcmp : BG20FrozenWindowLawComparison 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) (H : Ω → LQGMetric.DistC) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) {a u b p q : ℝ} {T : Set ℝ} (hpa : p < a) (hau : a < u) (hub : u < b)
    (hbq : b < q) (hpq : Icc p q ⊆ T) :
    ∃ R : ℕ → LQGMetric.DistC × C(ℝ, ℂ) → ProbabilityMeasure (ContinuousPath ℂ),
      (∀ n, Measurable[intrinsicCurveDecoratedSurfaceSigma γ T] (R n)) ∧
        ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => S.P {ω | δ ≤
          |∫ x, g x ∂(R n (H ω, η' ω) : Measure (ContinuousPath ℂ)) -
            ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|}) atTop (𝓝 0) := by
  have hJ : Icc a b ⊆ T := fun x hx => hpq ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hu : u ∈ Icc a b := ⟨hau.le, hub.le⟩
  refine ⟨fun n z => frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n)) (cellSideMult (ε n) ⇑z.2) z.2,
    fun n => ?_, fun g δ hδ => ?_⟩
  · refine measurable_intrinsicCurveDecoratedSurfaceSigma_of_forall_eq
      ((measurable_frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n))
        (M := fun η => cellSideMult (ε n) ⇑η)
        (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_cellSideMult (ε n) i j)).comp
        measurable_snd) ?_
    rintro ⟨h₁, η₁⟩ ⟨h₂, η₂⟩ ⟨f, hf⟩
    exact hf.frozenWindowLaw_eq hJ hu hpq (hε n) (S.mε_nonneg (ε n))
  · refine (hcmp γ hγ hγ2 Ω S hS η' hη' hae ε hε hε0 a u b p q hpa hau hub hbq g δ hδ).congr fun n => ?_
    have hae' : ∀ᵐ ω ∂S.P, frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n)) (S.mult (ε n) ω) (η' ω) =
        frozenWindowLaw a u b p q (ε n) (S.mε_nonneg (ε n)) (cellSideMult (ε n) ⇑(η' ω)) (η' ω) := by
      filter_upwards [hcell γ hγ hγ2 Ω S hS (ε n) (hε n), hae] with ω h1 h2
      rw [h1, h2]
    refine measure_congr (Filter.Eventually.set_eq (hae'.mono fun ω h => Iff.of_eq ?_))
    exact congrArg (fun P : ProbabilityMeasure (ContinuousPath ℂ) => δ ≤ |∫ x, g x ∂(P : Measure (ContinuousPath ℂ)) -
      ∫ x, g x ∂windowLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)|) h

/-- **`BG20DiscreteWindowLawIntrinsicInput` from the mating-of-trees identity for the frontier-side multiplicities and
the comparison of the frozen window laws with the chart laws of the walk.** For `s > b` the frozen window laws with
retained times `[a - 1, (b + s)/2]` are functions of the intrinsic past wedge at `s`; for `s < a` those with retained
times `[(s + a)/2, b + 1]` are functions of the intrinsic future wedge at `s`. -/
theorem bg20DiscreteWindowLawIntrinsicInput_of_cellSideIdentity {𝒮 : SpaceFillingSLEModel}
    (hcell : MatingOfTreesCellSideIdentity 𝒮) (hcmp : BG20FrozenWindowLawComparison 𝒮) :
    BG20DiscreteWindowLawIntrinsicInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H _ _ ε hε hε0 a u b s hau hub
  refine ⟨fun hbs => ?_, fun hsa => ?_⟩
  · exact exists_intrinsic_frozenWindowLaw hcell hcmp hγ hγ2 hS hη' hae H hε hε0 (p := a - 1) (q := (b + s) / 2)
      (by linarith) hau hub (by linarith) fun x hx => Set.mem_Iic.2 (by linarith [hx.2])
  · exact exists_intrinsic_frozenWindowLaw hcell hcmp hγ hγ2 hS hη' hae H hε hε0 (p := (s + a) / 2) (q := b + 1)
      (by linarith) hau hub (by linarith) fun x hx => Set.mem_Ici.2 (by linarith [hx.1])

end MatedCRT
