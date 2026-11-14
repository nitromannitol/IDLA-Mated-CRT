import MatedCRT.FirstPass.Derived.BoundaryLengthPastMeasurable

/-!
# Recentered boundary-length edge data

Edge multiplicities are invariant under independent additive shifts of the two
continuous boundary-length coordinates. Consequently the edges before a fixed
time are measurable from the recentered past increments.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

private theorem inf_image_sub_const {X : ℝ → ℝ} (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    sInf ((fun t => X t - c) '' Icc a b) = sInf (X '' Icc a b) - c := by
  have hne : (X '' Icc a b).Nonempty := (nonempty_Icc.mpr hab).image X
  have hb : BddBelow (X '' Icc a b) := (isCompact_Icc.image hX).bddBelow
  have h := (OrderIso.addRight (-c)).map_csInf' hne hb
  simpa only [OrderIso.addRight_apply, sub_eq_add_neg, Set.image_image, Function.comp_def] using h.symm

/-- Translating a continuous path preserves the side-adjacency test for ordered vertices. -/
theorem bmAdjacent_sub_const {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : Continuous X) (c : ℝ) {j k : ℤ} (hjk : j < k) :
    bmAdjacent ε (fun t => X t - c) j k ↔ bmAdjacent ε X j k := by
  have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  have hmid : ε * (j : ℝ) ≤ ε * (k : ℝ) - ε := by nlinarith
  unfold bmAdjacent
  rw [inf_image_sub_const hX (by linarith) c,
      inf_image_sub_const hX (by linarith) c,
      inf_image_sub_const hX hmid c]
  simp only [max_sub_sub_right, sub_le_sub_iff_right]

/-- Translating either coordinate does not change the edge multiplicity. -/
theorem bmEdgeCount_sub_const {ε : ℝ} (hε : 0 < ε) {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) (c d : ℝ) (j k : ℤ) :
    bmEdgeCount ε (fun t => L t - c) (fun t => R t - d) j k =
      bmEdgeCount ε L R j k := by
  classical
  by_cases h : j = k
  · simp [bmEdgeCount, h]
  · have hlt : min j k < max j k := min_lt_max.mpr h
    have hL' := bmAdjacent_sub_const hε hL c hlt
    have hR' := bmAdjacent_sub_const hε hR d hlt
    simp [bmEdgeCount, h, hL', hR']

/-- Every edge before a fixed time is measurable from recentered past increments. -/
theorem measurable_bmEdgeCount_of_past_increments {Ω : Type} [MeasurableSpace Ω]
    (B : Ω → C(ℝ, ℝ × ℝ)) (s ε : ℝ)
    (hB : ∀ t ≤ s, Measurable fun ω => B ω t - B ω s)
    (hε : 0 < ε) (j k : ℤ) (hjk : ε * ((max j k : ℤ) : ℝ) ≤ s) :
    Measurable fun ω =>
      bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k := by
  let D : Ω → C(ℝ, ℝ × ℝ) := fun ω =>
    ⟨fun t => B ω t - B ω s, (B ω).continuous.sub continuous_const⟩
  have hD : ∀ t ≤ s, Measurable fun ω => D ω t := hB
  have h := measurable_bmEdgeCount_of_past D s ε hD hε.le j k hjk
  convert h using 1
  funext ω
  exact (bmEdgeCount_sub_const hε ((B ω).continuous.fst) ((B ω).continuous.snd)
    (B ω s).1 (B ω s).2 j k).symm

end MatedCRT
