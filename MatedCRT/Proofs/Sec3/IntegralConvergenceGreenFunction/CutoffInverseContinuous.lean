import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffMeasurable

/-!
# Lemma 3.4 (item 4): continuity of the cutoff approximate inverse

For a strictly increasing continuous approximate Liouville clock `C` (the time integral of a positive continuous density along
a Brownian path, Garban–Rhodes–Vargas, Section 2), the cutoff inverse `t ↦ cutInv C n t` is continuous. Its upper level sets
`{t | cutInv C n t < x}` are unions of rays `{t | t < C q}` over rational `q`, and its lower level sets `{t | x < cutInv C n t}`
are rays `{t | C x < t}` (or empty); both are open. Hence the time-changed approximate paths `b ∘ cutInv C n` are continuous,
which is what the grid approximation of bounded Lipschitz path functionals needs.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- Upper level sets of the cutoff inverse are open. -/
theorem isOpen_cutInv_lt {C : ℝ≥0 → ℝ} (hC : StrictMono C) (n x : ℝ≥0) :
    IsOpen {t : ℝ≥0 | cutInv C n t < x} := by
  by_cases hx : n < x
  · have hall : {t : ℝ≥0 | cutInv C n t < x} = univ := by
      ext t
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact lt_of_le_of_lt (cutInv_le_cutoff C n t) hx
    rw [hall]
    exact isOpen_univ
  · rw [not_lt] at hx
    have hset : {t : ℝ≥0 | cutInv C n t < x} =
        ⋃ (r : ℚ), ⋃ (_ : 0 ≤ (r : ℝ) ∧ (r : ℝ) < x),
          {t : ℝ≥0 | (t : ℝ) < C (Real.toNNReal r)} := by
      ext t
      constructor
      · intro h
        obtain ⟨r, hr0, hrx, hrt⟩ := (cutInv_lt_iff hC.monotone hx).1 h
        exact mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨⟨hr0, hrx⟩, hrt⟩⟩
      · intro h
        obtain ⟨r, hr⟩ := mem_iUnion.1 h
        obtain ⟨hr', ht⟩ := mem_iUnion.1 hr
        exact (cutInv_lt_iff hC.monotone hx).2 ⟨r, hr'.1, hr'.2, ht⟩
    rw [hset]
    exact isOpen_iUnion fun r => isOpen_iUnion fun _ => isOpen_lt NNReal.continuous_coe continuous_const

/-- Lower level sets of the cutoff inverse are open: they are rays `{t | C x < t}` below the cutoff, and empty above it. -/
theorem isOpen_lt_cutInv {C : ℝ≥0 → ℝ} (hC : StrictMono C) (hCc : Continuous C) (n x : ℝ≥0) :
    IsOpen {t : ℝ≥0 | x < cutInv C n t} := by
  by_cases hxn : x < n
  · have hset : {t : ℝ≥0 | x < cutInv C n t} = {t : ℝ≥0 | C x < (t : ℝ)} := by
      ext t
      simp only [mem_ofPred_eq]
      constructor
      · intro h
        by_contra hle
        have hle' : (t : ℝ) ≤ C x := not_lt.1 hle
        obtain ⟨a, hxa, hat⟩ := exists_between h
        by_cases ha : a ≤ n
        · have hmem : a ∈ ({s : ℝ≥0 | s ≤ n ∧ (t : ℝ) < C s} ∪ {n} : Set ℝ≥0) :=
            Or.inl ⟨ha, lt_of_le_of_lt hle' (hC hxa)⟩
          have hca : cutInv C n t ≤ a := by
            unfold cutInv
            exact csInf_le (OrderBot.bddBelow _) hmem
          exact absurd hat (not_lt.2 hca)
        · have hca : cutInv C n t ≤ n := cutInv_le_cutoff C n t
          exact absurd hat (not_lt.2 (hca.trans (not_le.1 ha).le))
      · intro h
        have hev : ∀ᶠ s in 𝓝[>] x, C s < (t : ℝ) :=
          nhdsWithin_le_nhds ((hCc.tendsto x).eventually (gt_mem_nhds h))
        have hIoo : ∀ᶠ s in 𝓝[>] x, s ∈ Ioo x n := Ioo_mem_nhdsGT hxn
        obtain ⟨s, hs1, hs2⟩ := (hev.and hIoo).exists
        rw [mem_Ioo] at hs2
        have hle : s ≤ cutInv C n t := by
          unfold cutInv
          refine le_csInf ⟨n, Or.inr rfl⟩ fun a ha => ?_
          rcases ha with ⟨han, hta⟩ | han
          · by_contra hlt
            have hlt' : a < s := not_le.1 hlt
            have hCa : C a ≤ C s := hC.monotone hlt'.le
            linarith
          · rw [mem_singleton_iff] at han
            rw [han]
            exact hs2.2.le
        exact lt_of_lt_of_le hs2.1 hle
    rw [hset]
    exact isOpen_lt continuous_const NNReal.continuous_coe
  · rw [not_lt] at hxn
    have hempty : {t : ℝ≥0 | x < cutInv C n t} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (cutInv_le_cutoff C n t).trans hxn
    rw [hempty]
    exact isOpen_empty

/-- **Continuity of the cutoff approximate inverse.** For a strictly increasing continuous approximate clock `C`, the cutoff
inverse `t ↦ cutInv C n t` is continuous. -/
theorem continuous_cutInv {C : ℝ≥0 → ℝ} (hC : StrictMono C) (hCc : Continuous C) (n : ℝ≥0) :
    Continuous fun t : ℝ≥0 => cutInv C n t :=
  continuous_iff_lower_upperSemicontinuous.2
    ⟨lowerSemicontinuous_iff_isOpen_preimage.2 fun x => isOpen_lt_cutInv hC hCc n x,
      upperSemicontinuous_iff_isOpen_preimage.2 fun x => isOpen_cutInv_lt hC n x⟩

end MatedCRT
