import MatedCRT.FirstPass.Derived.BlockEdgeCount

/-!
# Strict prefix minima of cell minima and running minima of the path

This is the pointwise part of the reduction of BG20 Lemma A.8 to BG20 Lemma A.9 (the count `K_n` of unit
intervals containing a running minimum of a Brownian motion).

For a continuous path `X` and the cells `[εk - ε, εk]`, a strict prefix minimum `k` of the cell minima of
the block `[lo, hi]` is a cell containing a *running minimum* of `X` relative to the block start
`ε lo - ε`: a minimizer of `X` over the cell `k` is such a time. Hence the number of strict prefix minima
is at most the number of cells of the block that contain a running minimum
(`card_blockPrefixMins_le_blockRunningMinCells`). The strict suffix minima are the strict prefix minima of
the time-reversed path `t ↦ X (ε (lo + hi - 1) - t)` on the same block
(`card_blockSuffixMins_le_blockRunningMinCells_reflect`).

Finally `card_blockRunningMinCells_rescale` moves the count of a block `[a + 1, a + N]` of cells of size
`ε` to the unit cells `[1, N]` of the path `u ↦ X (ε a + ε u) + c` (Brownian scaling and translation of
the time origin to the block start, plus an arbitrary shift of the values).
-/

open Finset

namespace MatedCRT

open Classical in
/-- The cells `k ∈ [lo, hi]` whose time interval `[εk - ε, εk]` contains a *running minimum* of `X`
relative to the block start `ε lo - ε`: a time `t` with `X t ≤ X s` for every `s ∈ [ε lo - ε, t]`. -/
noncomputable def blockRunningMinCells (ε : ℝ) (X : ℝ → ℝ) (lo hi : ℤ) : Finset ℤ :=
  (Icc lo hi).filter fun k =>
    ∃ t ∈ Set.Icc (ε * k - ε) (ε * k), ∀ s ∈ Set.Icc (ε * lo - ε) t, X t ≤ X s

theorem mem_blockRunningMinCells {ε : ℝ} {X : ℝ → ℝ} {lo hi k : ℤ} :
    k ∈ blockRunningMinCells ε X lo hi ↔ k ∈ Icc lo hi ∧
      ∃ t ∈ Set.Icc (ε * k - ε) (ε * k), ∀ s ∈ Set.Icc (ε * lo - ε) t, X t ≤ X s := by
  simp only [blockRunningMinCells, mem_filter]

/-- Every time `s` lies in the cell `⌊s / ε⌋ + 1`. -/
theorem mem_cell_floor_add_one {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    s ∈ Set.Icc (ε * ((⌊s / ε⌋ + 1 : ℤ) : ℝ) - ε) (ε * ((⌊s / ε⌋ + 1 : ℤ) : ℝ)) := by
  have h1 : (⌊s / ε⌋ : ℝ) * ε ≤ s := (le_div_iff₀ hε).mp (Int.floor_le (s / ε))
  have h2 : s < ((⌊s / ε⌋ : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp (Int.lt_floor_add_one (s / ε))
  push_cast
  constructor <;> nlinarith

/-- **Prefix minima are running-minimum cells.** For a continuous path and `ε > 0`, every strict prefix
minimum `k` of the cell minima of the block `[lo, hi]` contains a running minimum of `X` relative to the
block start: a minimizer of `X` over the cell `k`. -/
theorem blockPrefixMins_subset_blockRunningMinCells {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : Continuous X) (lo hi : ℤ) :
    blockPrefixMins (bmCellMin ε X) lo hi ⊆ blockRunningMinCells ε X lo hi := by
  intro k hk
  simp only [blockPrefixMins, mem_filter] at hk
  obtain ⟨hkB, hmin⟩ := hk
  rw [mem_blockRunningMinCells]
  refine ⟨hkB, ?_⟩
  have hne : (Set.Icc (ε * k - ε) (ε * k)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  obtain ⟨t, ht, htmin⟩ := isCompact_Icc.exists_isMinOn hne hX.continuousOn
  have htk : bmCellMin ε X k = X t := by
    refine IsLeast.csInf_eq ⟨Set.mem_image_of_mem X ht, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact isMinOn_iff.mp htmin u hu
  refine ⟨t, ht, fun s hs => ?_⟩
  by_cases hsk : ε * k - ε ≤ s
  · exact isMinOn_iff.mp htmin s ⟨hsk, hs.2.trans ht.2⟩
  · have hsk' : s < ε * k - ε := not_le.mp hsk
    have hsi := mem_cell_floor_add_one hε s
    have hlo : ((lo - 1 : ℤ) : ℝ) ≤ s / ε := by
      rw [le_div_iff₀ hε]; push_cast; nlinarith [hs.1]
    have hk1 : s / ε < ((k - 1 : ℤ) : ℝ) := by
      rw [div_lt_iff₀ hε]; push_cast; nlinarith
    have hilo : lo - 1 ≤ ⌊s / ε⌋ := Int.le_floor.mpr hlo
    have hik : ⌊s / ε⌋ < k - 1 := Int.floor_lt.mpr hk1
    have hiB : ⌊s / ε⌋ + 1 ∈ Icc lo hi := by
      rw [mem_Icc] at hkB ⊢; omega
    have h1 := hmin (⌊s / ε⌋ + 1) hiB (by omega)
    have h2 := bmCellMin_le hX hsi
    linarith

/-- The number of strict prefix minima of the cell minima of a block is at most the number of its cells
that contain a running minimum of the path (BG20 (A.34), pointwise). -/
theorem card_blockPrefixMins_le_blockRunningMinCells {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : Continuous X) (lo hi : ℤ) :
    #(blockPrefixMins (bmCellMin ε X) lo hi) ≤ #(blockRunningMinCells ε X lo hi) :=
  card_le_card (blockPrefixMins_subset_blockRunningMinCells hε hX lo hi)

/-- Reflecting the block `[lo, hi]` by `k ↦ lo + hi - k` exchanges strict suffix and prefix minima. -/
theorem card_blockSuffixMins_eq_reflect (m : ℤ → ℝ) (lo hi : ℤ) :
    #(blockSuffixMins m lo hi) = #(blockPrefixMins (fun k => m (lo + hi - k)) lo hi) := by
  refine card_nbij' (fun k => lo + hi - k) (fun k => lo + hi - k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [coe_filter, blockSuffixMins, blockPrefixMins, Set.mem_ofPred_eq, mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hmin⟩ := hk
    refine ⟨⟨by omega, by omega⟩, fun i hi' hik => ?_⟩
    have := hmin (lo + hi - i) ⟨by omega, by omega⟩ (by omega)
    simpa only [sub_sub_cancel] using this
  · intro k hk
    simp only [coe_filter, blockSuffixMins, blockPrefixMins, Set.mem_ofPred_eq, mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hmin⟩ := hk
    refine ⟨⟨by omega, by omega⟩, fun i hi' hik => ?_⟩
    have := hmin (lo + hi - i) ⟨by omega, by omega⟩ (by omega)
    simpa only [sub_sub_cancel] using this
  · intro k _
    simp only [sub_sub_cancel]
  · intro k _
    simp only [sub_sub_cancel]

/-- The cell minima of the reflected path `t ↦ X (ε (lo + hi - 1) - t)` are those of `X`, read in the
reflected order `k ↦ lo + hi - k`. -/
theorem bmCellMin_reflect (ε : ℝ) (X : ℝ → ℝ) (lo hi k : ℤ) :
    bmCellMin ε (fun t => X (ε * ((lo + hi - 1 : ℤ) : ℝ) - t)) k = bmCellMin ε X (lo + hi - k) := by
  unfold bmCellMin
  congr 1
  rw [show (fun t => X (ε * ((lo + hi - 1 : ℤ) : ℝ) - t)) =
      X ∘ fun t => ε * ((lo + hi - 1 : ℤ) : ℝ) - t from rfl, Set.image_comp,
    Set.image_const_sub_Icc]
  congr 2 <;> push_cast <;> ring

/-- The number of strict suffix minima of the cell minima of a block is at most the number of its cells
that contain a running minimum of the reflected path `t ↦ X (ε (lo + hi - 1) - t)`. -/
theorem card_blockSuffixMins_le_blockRunningMinCells_reflect {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : Continuous X) (lo hi : ℤ) :
    #(blockSuffixMins (bmCellMin ε X) lo hi) ≤
      #(blockRunningMinCells ε (fun t => X (ε * ((lo + hi - 1 : ℤ) : ℝ) - t)) lo hi) := by
  rw [card_blockSuffixMins_eq_reflect]
  have h : (fun k => bmCellMin ε X (lo + hi - k)) =
      bmCellMin ε (fun t => X (ε * ((lo + hi - 1 : ℤ) : ℝ) - t)) :=
    funext fun k => (bmCellMin_reflect ε X lo hi k).symm
  rw [h]
  exact card_blockPrefixMins_le_blockRunningMinCells hε
    (hX.comp (continuous_const.sub continuous_id)) lo hi

/-- **Rescaling the running-minimum count.** The count for the block `[a + 1, a + N]` of cells of size
`ε` equals the count for the unit cells `[1, N]` of the path `u ↦ X (ε a + ε u) + c`. -/
theorem card_blockRunningMinCells_rescale {ε : ℝ} (hε : 0 < ε) (X : ℝ → ℝ) (a : ℤ) (N : ℕ)
    (c : ℝ) :
    #(blockRunningMinCells ε X (a + 1) (a + N)) =
      #(blockRunningMinCells 1 (fun u => X (ε * a + ε * u) + c) 1 N) := by
  refine card_nbij' (fun k => k - a) (fun k => k + a) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [coe_filter, blockRunningMinCells, Set.mem_ofPred_eq, mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, t, ht, hrun⟩ := hk
    refine ⟨⟨by omega, by omega⟩, (t - ε * a) / ε, ?_, fun v hv => ?_⟩
    · rw [Set.mem_Icc] at ht ⊢
      push_cast
      constructor
      · rw [le_div_iff₀ hε]; nlinarith [ht.1]
      · rw [div_le_iff₀ hε]; nlinarith [ht.2]
    · have hv' : ε * a + ε * v ∈ Set.Icc (ε * ((a + 1 : ℤ) : ℝ) - ε) t := by
        rw [Set.mem_Icc] at hv ⊢
        have h2 := hv.2
        rw [le_div_iff₀ hε] at h2
        have hv0 : 0 ≤ v := by simpa using hv.1
        push_cast
        constructor <;> nlinarith [mul_nonneg hε.le hv0]
      have := hrun _ hv'
      have ht' : ε * a + ε * ((t - ε * a) / ε) = t := by field_simp; ring
      rw [ht']
      linarith
  · intro k hk
    simp only [coe_filter, blockRunningMinCells, Set.mem_ofPred_eq, mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, u, hu, hrun⟩ := hk
    refine ⟨⟨by omega, by omega⟩, ε * a + ε * u, ?_, fun s hs => ?_⟩
    · rw [Set.mem_Icc] at hu ⊢
      push_cast at hu ⊢
      constructor <;> nlinarith [hu.1, hu.2]
    · have hv : (s - ε * a) / ε ∈ Set.Icc ((1 : ℝ) * ((1 : ℤ) : ℝ) - 1) u := by
        rw [Set.mem_Icc] at hs ⊢
        push_cast at hs ⊢
        constructor
        · rw [le_div_iff₀ hε]; nlinarith [hs.1]
        · rw [div_le_iff₀ hε]; nlinarith [hs.2]
      have := hrun _ hv
      have hs' : ε * a + ε * ((s - ε * a) / ε) = s := by field_simp; ring
      rw [hs'] at this
      linarith
  · intro k _
    simp only [sub_add_cancel]
  · intro k _
    simp only [add_sub_cancel_right]

end MatedCRT
