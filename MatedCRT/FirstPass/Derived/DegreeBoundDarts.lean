import MatedCRT.Defs.Map
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsEdge

/-!
# The degree of the mated-CRT map is at most the number of labelled edge ends

Definition 1.1 builds the `γ`-mated-CRT map with cell size `ε` from the pair of paths `(L, R)` as an edge
multiplicity `bmEdgeCount ε L R` on `ℤ`: the vertices `εj` and `εk` carry one edge if the adjacency condition
(eq:edge-map) holds for `L` or for `R`, and two edges if moreover `|k - j| > 1` and it holds for both.
Gwynne–Miller–Sheffield (2019), (1.1), describe the same graph by labelled edges `(x, y, side)` with `x < y`
(`MatedCRTHarmonic.MatedCRT.IsEdge`): consecutive vertices carry the single edge `(x, x + 1, false)`, and a
non-consecutive pair carries its `L`-edge iff (1.1) holds for `L` and its `R`-edge iff (1.1) holds for `R`.

The adjacency condition (eq:edge-map) is condition (1.1) (`bmAdjacent_iff_sideCond`), so for every pair of
vertices the multiplicity `bmEdgeCount` is at most the number of labelled edges joining them
(`bmEdgeCount_le_card_isEdge`), and the degree `deg^ε(x)` is at most the number of labelled edge ends at `x`
(`matedDeg_bmEdgeCount_le_encard`). The right-hand side is the extended degree whose exponential tail is GMS19
Lemma 2.5; this bound transfers that tail to the degree of the paper's map (GMS19 Lemma 2.6).

## Main statements

* `MatedCRT.bmAdjacent_iff_sideCond`
* `MatedCRT.bmEdgeCount_le_card_isEdge`
* `MatedCRT.matedDeg_bmEdgeCount_le_encard`
-/

namespace MatedCRT

open Set

/-- The adjacency condition (eq:edge-map) of Definition 1.1 for one coordinate `X` is condition (1.1) of
Gwynne–Miller–Sheffield (2019). -/
theorem bmAdjacent_iff_sideCond (ε : ℝ) (X : ℝ → ℝ) (j k : ℤ) :
    bmAdjacent ε X j k ↔ MatedCRTHarmonic.MatedCRT.SideCond ε X j k := by
  simp only [bmAdjacent, MatedCRTHarmonic.MatedCRT.SideCond, MatedCRTHarmonic.MatedCRT.intervalInf, mul_sub,
    mul_one]

open Classical in
/-- The number of edges of the mated-CRT map (Definition 1.1) joining the vertices `a` and `b` is at most the number
of labelled edges `(min a b, max a b, side)` of Gwynne–Miller–Sheffield (2019), (1.1). -/
theorem bmEdgeCount_le_card_isEdge (ε : ℝ) (ω : MatedCRTHarmonic.MatedCRT.Path2) (a b : ℤ) :
    bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) a b ≤
      (Finset.univ.filter fun s : Bool => MatedCRTHarmonic.MatedCRT.IsEdge ε ω (min a b, max a b, s)).card := by
  classical
  by_cases hab : a = b
  · simp [bmEdgeCount, hab]
  have hlt : min a b < max a b := min_lt_max.mpr hab
  have hE : ∀ s : Bool, MatedCRTHarmonic.MatedCRT.IsEdge ε ω (min a b, max a b, s) ↔
      ((max a b = min a b + 1 ∧ s = false) ∨ (max a b ≠ min a b + 1 ∧
        bmAdjacent ε (fun t => if s then (ω t).2 else (ω t).1) (min a b) (max a b))) := by
    intro s
    simp only [MatedCRTHarmonic.MatedCRT.IsEdge, ← bmAdjacent_iff_sideCond, hlt, true_and]
  rw [Finset.card_filter, Fintype.sum_bool]
  by_cases hc : max a b = min a b + 1
  · have h1 : ¬ (1 < max a b - min a b) := by omega
    have hF : MatedCRTHarmonic.MatedCRT.IsEdge ε ω (min a b, max a b, false) :=
      (hE false).2 (Or.inl ⟨hc, rfl⟩)
    have hle : bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) a b ≤ 1 := by
      simp only [bmEdgeCount, hab, h1, false_and, ↓reduceIte]
      split_ifs <;> omega
    simp only [hF, ↓reduceIte]
    omega
  · have h1 : 1 < max a b - min a b := by omega
    have hT := hE true
    have hF := hE false
    simp only [hc, false_and, false_or, true_and, ne_eq, not_false_eq_true] at hT hF
    simp only [Bool.false_eq_true, ↓reduceIte] at hT hF
    simp only [bmEdgeCount, hab, h1, true_and, ↓reduceIte]
    by_cases hL : bmAdjacent ε (fun t => (ω t).1) (min a b) (max a b) <;>
    by_cases hR : bmAdjacent ε (fun t => (ω t).2) (min a b) (max a b) <;>
    simp [hL, hR, hT, hF]

/-- The degree `deg^ε(x)` of the mated-CRT map of Definition 1.1, for the pair of paths `(L, R) = ω`, is at most the
number of labelled edge ends at `x` in the sense of Gwynne–Miller–Sheffield (2019), (1.1): pairs `(e, end)` of a
labelled edge `e = (lo, hi, side)` and an end of it at `x` (`end = true` selects `hi`). The right-hand side is the
extended degree of GMS19 Lemma 2.5. (If `x` has infinitely many neighbours, `deg^ε(x)` is the junk value `0`.) -/
theorem matedDeg_bmEdgeCount_le_encard (ε : ℝ) (ω : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ) :
    ((matedDeg (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x : ℕ) : ℕ∞) ≤
      {d : (ℤ × ℤ × Bool) × Bool | MatedCRTHarmonic.MatedCRT.IsEdge ε ω d.1 ∧
        (if d.2 then d.1.2.1 else d.1.1) = x}.encard := by
  classical
  set m := bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) with hm
  unfold matedDeg mdeg
  by_cases hfin : (Function.support (m x)).Finite
  swap
  · rw [finsum_of_infinite_support hfin]
    simp
  rw [finsum_eq_sum (m x) hfin]
  set Sb := hfin.toFinset
  set F : Finset (ℤ × Bool) := (Sb ×ˢ Finset.univ).filter
    fun p => MatedCRTHarmonic.MatedCRT.IsEdge ε ω (min x p.1, max x p.1, p.2) with hFdef
  set g : ℤ × Bool → (ℤ × ℤ × Bool) × Bool :=
    fun p => ((min x p.1, max x p.1, p.2), decide (p.1 < x)) with hgdef
  have hg : Function.Injective g := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ h
    simp only [hgdef, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := h
    have hsum := congrArg₂ (· + ·) h1 h2
    simp only [min_add_max] at hsum
    have hb : b = b' := by omega
    rw [hb, h3]
  have hsum : ∑ b ∈ Sb, m x b ≤ F.card := by
    rw [hFdef, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← Finset.card_filter]
    exact bmEdgeCount_le_card_isEdge ε ω x b
  have hsub : (↑(F.image g) : Set ((ℤ × ℤ × Bool) × Bool)) ⊆
      {d : (ℤ × ℤ × Bool) × Bool | MatedCRTHarmonic.MatedCRT.IsEdge ε ω d.1 ∧
        (if d.2 then d.1.2.1 else d.1.1) = x} := by
    intro d hd
    rw [Finset.coe_image] at hd
    obtain ⟨⟨b, s⟩, hp, rfl⟩ := hd
    have hE := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    refine ⟨hE, ?_⟩
    by_cases hb : b < x
    · simp [hgdef, hb, max_eq_left hb.le]
    · simp [hgdef, hb, min_eq_left (not_lt.1 hb)]
  calc ((∑ b ∈ Sb, m x b : ℕ) : ℕ∞) ≤ (F.card : ℕ∞) := by exact_mod_cast hsum
    _ = ((F.image g).card : ℕ∞) := by rw [Finset.card_image_of_injective _ hg]
    _ = (↑(F.image g) : Set ((ℤ × ℤ × Bool) × Bool)).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ _ := Set.encard_le_encard hsub

end MatedCRT
