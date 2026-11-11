import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffInverse

/-!
# Lemma 3.4: measurability of the cutoff inverse

For a family of monotone clocks `C p` depending jointly measurably on the parameter `p` and the time, the cutoff inverse
`(p, t) ↦ cutInv (C p) n t` is jointly measurable. The proof uses the level sets: for a level `x ≤ n`, the event
`{cutInv (C p) n t < x}` is witnessed by a rational time `q < x` with `t < C p q`; for `x > n` the event is certain, since
`cutInv ≤ n`. Only the monotonicity of the clocks is used.

Terminology: approximate Liouville clock inverse (Garban–Rhodes–Vargas, Liouville Brownian motion).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- The cutoff inverse does not exceed the cutoff. -/
theorem cutInv_le_cutoff (C : ℝ≥0 → ℝ) (n t : ℝ≥0) : cutInv C n t ≤ n := by
  unfold cutInv
  exact csInf_le (OrderBot.bddBelow _) (Or.inr rfl)

/-- For a level `x ≤ n`, the cutoff inverse lies below `x` exactly when some rational time `q ∈ [0, x)` has
`t < C q`. -/
theorem cutInv_lt_iff {C : ℝ≥0 → ℝ} (hC : Monotone C) {n t x : ℝ≥0} (hx : x ≤ n) :
    cutInv C n t < x ↔ ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < x ∧ (t : ℝ) < C (Real.toNNReal q) := by
  constructor
  · intro h
    unfold cutInv at h
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt ⟨n, Or.inr rfl⟩ h
    rcases hs with ⟨hsn, hts⟩ | hs'
    · obtain ⟨q, hsq, hqx⟩ := exists_rat_btwn (show (s : ℝ) < (x : ℝ) from hsx)
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans s.2 hsq.le
      refine ⟨q, hq0, hqx, ?_⟩
      have hsq' : s ≤ Real.toNNReal q := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact hsq.le
      exact lt_of_lt_of_le hts (hC hsq')
    · rw [Set.mem_singleton_iff] at hs'
      rw [hs'] at hsx
      exact absurd (lt_of_lt_of_le hsx hx) (lt_irrefl _)
  · rintro ⟨q, hq0, hqx, htC⟩
    have hle : Real.toNNReal q ≤ n := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact le_trans hqx.le (by exact_mod_cast hx)
    have hmem : Real.toNNReal q ∈ ({s | s ≤ n ∧ (t : ℝ) < C s} ∪ {n} : Set ℝ≥0) :=
      Or.inl ⟨hle, htC⟩
    have h1 : cutInv C n t ≤ Real.toNNReal q := by
      unfold cutInv
      exact csInf_le (OrderBot.bddBelow _) hmem
    have h2 : ((Real.toNNReal q : ℝ≥0) : ℝ) < (x : ℝ) := by
      rw [Real.coe_toNNReal _ hq0]
      exact hqx
    exact lt_of_le_of_lt h1 (NNReal.coe_lt_coe.1 h2)

/-- **Measurability of the cutoff inverse.** If the clocks `C p` are monotone in time and their values are jointly
measurable in the parameter and the time, then `(p, t) ↦ cutInv (C p) n t` is measurable. -/
theorem measurable_cutInv {α : Type*} [MeasurableSpace α] {C : α → ℝ≥0 → ℝ} (hmono : ∀ p, Monotone (C p))
    (hC : Measurable fun q : α × ℝ≥0 => C q.1 q.2) (n : ℝ≥0) :
    Measurable fun q : α × ℝ≥0 => cutInv (C q.1) n q.2 := by
  refine measurable_of_Iio fun x => ?_
  by_cases hx : n < x
  · have hall : (fun q : α × ℝ≥0 => cutInv (C q.1) n q.2) ⁻¹' Iio x = univ := by
      ext q
      simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
      exact lt_of_le_of_lt (cutInv_le_cutoff _ _ _) hx
    rw [hall]
    exact MeasurableSet.univ
  · rw [not_lt] at hx
    have hset : (fun q : α × ℝ≥0 => cutInv (C q.1) n q.2) ⁻¹' Iio x =
        ⋃ (r : ℚ), ⋃ (_ : 0 ≤ (r : ℝ) ∧ (r : ℝ) < x),
          {q : α × ℝ≥0 | (q.2 : ℝ) < C q.1 (Real.toNNReal r)} := by
      ext q
      constructor
      · intro h
        obtain ⟨r, hr0, hrx, hrt⟩ := (cutInv_lt_iff (hmono q.1) hx).1 h
        exact mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨⟨hr0, hrx⟩, hrt⟩⟩
      · intro h
        obtain ⟨r, hr⟩ := mem_iUnion.1 h
        obtain ⟨hr', ht⟩ := mem_iUnion.1 hr
        exact (cutInv_lt_iff (hmono q.1) hx).2 ⟨r, hr'.1, hr'.2, ht⟩
    rw [hset]
    refine MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun hr => ?_
    have hf : Measurable fun q : α × ℝ≥0 => (q.2 : ℝ) :=
      NNReal.continuous_coe.measurable.comp measurable_snd
    have hg : Measurable fun q : α × ℝ≥0 => C q.1 (Real.toNNReal r) :=
      hC.comp (measurable_fst.prodMk measurable_const)
    exact measurableSet_lt hf hg

end MatedCRT
