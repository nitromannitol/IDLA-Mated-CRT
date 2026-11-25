import MatedCRT.FirstPass.Derived.IntrinsicWindowChart
import MatedCRT.FirstPass.Derived.WindowChartBGFieldSurface

/-!
# The intrinsic inverse chart is the inverse chart of Berestycki–Gwynne

Let the window `(a, u, b)` of `η` have an inverse chart at `η(u)` (`IsInverseChart`), let the time segments of `η` be
regular closed (`SegmentsRegularClosed`; almost surely for the space-filling SLE, `ae_regularClosed_segmentImages`)
and let `η` visit `η(u)` only at the time `u`. Then:

* the intrinsic entry time `windowEntryIntr` is the time `a' = windowStartBG` (`windowEntryIntr_eq_windowStartBG`):
  the rational visits of `η` to the window domain `U` are dense after `a'`, since a nondegenerate segment
  `η([c', d']) ⊆ Ū` is the closure of its interior, which meets `U`;
* the chart values `v(η(q_m))` converge to `ψ(η(a'))` for the extended normalized inverse chart `ψ = windowChart`,
  which is continuous on the plane, so the intrinsic entry point is `ψ(η(a')) ≠ 0`;
* the construction succeeds and `windowChartIntr = windowChartBG` on `U`
  (`windowGoodIntr_and_eqOn_windowChartBG`).
-/

set_option autoImplicit false

open Set Metric Filter Topology Function MeasureTheory

namespace MatedCRT

/-- The nondegenerate time segments of `η` are regular closed: each is the closure of its interior. -/
def SegmentsRegularClosed (η : C(ℝ, ℂ)) : Prop :=
  ∀ c d : ℝ, c < d → closure (interior (η '' Icc c d)) = η '' Icc c d

section Deterministic

variable {a u b : ℝ} {η : C(ℝ, ℂ)}

/-- On the window domain, the inverse of the normalized conformal map of the open disc is the normalized inverse
chart `windowChart`. -/
theorem openWindowDiscInv_eq_windowChart (hψ : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) :
    HasOpenWindowDiscMap a u b η ∧
      ∀ x ∈ windowDomain η a u b, openWindowDiscInv a u b η x = windowChart a u b η x := by
  obtain ⟨ψ, hψ'⟩ := hψ
  have hN := isNormalizedDiscMap_windowDiscMap hψ'
  have hD : HasOpenWindowDiscMap a u b η :=
    exists_mem_openWindowDiscMapGraph hN.isDiscMap.isOpenDiscMap hN.apply_zero
  refine ⟨hD, fun x hx => ?_⟩
  have hw := openWindowDiscInv_mem_ball a u b η x
  have hE := (isNormalizedOpenDiscMap_openWindowDiscMap hD).eqOn hN.isNormalizedOpenDiscMap hw
  have hx' : windowDiscMap a u b η (openWindowDiscInv a u b η x) = x :=
    hE.symm.trans (openWindowDiscMap_openWindowDiscInv hD hx)
  have hinv : windowChart a u b η (windowDiscMap a u b η (openWindowDiscInv a u b η x)) =
      openWindowDiscInv a u b η x :=
    discInverseExt_apply_image hN.isDiscMap.injOn (ball_subset_closedBall hw)
  rw [hx'] at hinv
  exact hinv.symm

/-- After the time `a'`, the rational visits of the curve to the window domain are dense, if the time segments of
the curve are regular closed. -/
theorem windowVisitsDense_of_windowStartBG_lt (hau : a ≤ u)
    (hψ : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ)
    (hreg : SegmentsRegularClosed η) {r : ℝ} (hr : windowStartBG a u b η < r) :
    WindowVisitsDense a u b η r := by
  intro c d hc hcd hd
  obtain ⟨c', hcc', hc'd⟩ := exists_rat_btwn hcd
  obtain ⟨d', hc'd', hd'd⟩ := exists_rat_btwn hc'd
  set U := windowDomain η a u b
  -- the segment `[c', d']` is filled inside the closure of the window
  have hS : windowStartBG a u b η = sInf {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure U} := by
    rw [windowStartBG, ite_eq_left hψ]
  obtain ⟨ψ, hψ'⟩ := hψ
  have huS : u ∈ {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure U} := by
    refine ⟨⟨hau, le_rfl⟩, fun t ht => ?_⟩
    · rw [le_antisymm ht.2 ht.1]
      exact subset_closure hψ'.mem
  have hlt : sInf {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure U} < c' := by
    rw [← hS]
    linarith
  obtain ⟨s, hs, hsc'⟩ := exists_lt_of_csInf_lt ⟨u, huS⟩ hlt
  have hseg : η '' Icc (c' : ℝ) d' ⊆ closure U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hs.2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the interior of the segment meets the window
  have hne : (interior (η '' Icc (c' : ℝ) d')).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have h1 := hreg c' d' hc'd'
    rw [hemp, closure_empty] at h1
    have h2 : η c' ∈ η '' Icc (c' : ℝ) d' := mem_image_of_mem η ⟨le_rfl, hc'd'.le⟩
    rw [← h1] at h2
    exact h2
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hzI, hzU⟩ := mem_closure_iff.1 (hseg (interior_subset hy)) _ isOpen_interior hy
  obtain ⟨t, ht, rfl⟩ := interior_subset hzI
  -- a rational time near `t` visits the window
  have hopen : IsOpen (η ⁻¹' U) := (isOpen_windowDomain η a u b).preimage η.continuous
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t hzU
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show max (c : ℝ) (t - δ / 2) < min (d : ℝ) (t + δ / 2) by
    refine max_lt (lt_min ?_ ?_) (lt_min ?_ ?_) <;> linarith [ht.1, ht.2])
  refine ⟨q, lt_of_le_of_lt (le_max_left _ _) hq₁, lt_of_lt_of_le hq₂ (min_le_left _ _), hball ?_⟩
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [le_max_right (c : ℝ) (t - δ / 2), min_le_right (d : ℝ) (t + δ / 2)]

/-- **The intrinsic entry time is the time `a'` of Berestycki–Gwynne.** -/
theorem windowEntryIntr_eq_windowStartBG (hau : a < u)
    (hψ : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) (hreg : SegmentsRegularClosed η) :
    windowEntryIntr a u b η = windowStartBG a u b η := by
  set U := windowDomain η a u b
  have hS : windowStartBG a u b η = sInf {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure U} := by
    rw [windowStartBG, ite_eq_left hψ]
  obtain ⟨ψ, hψ'⟩ := hψ
  have hs₀ := windowStartBG_mem_Icc (b := b) hau.le η
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (lt_min hcon (windowStartBG_lt (b := b) hau η))
    have hdense := windowVisitsDense_of_windowStartBG_lt hau.le ⟨ψ, hψ'⟩ hreg hr₁
    have hle := windowEntryIntr_le_of (b := b) hau.le
      ⟨⟨by linarith [hs₀.1], (lt_of_lt_of_le hr₂ (min_le_right _ _)).le⟩, hdense⟩
    linarith [min_le_left (windowEntryIntr a u b η) u]
  · refine le_ciInf fun r => ?_
    unfold windowEntryTerm
    split_ifs with h
    · rw [hS]
      refine csInf_le ⟨a, fun s hs => hs.1.1⟩ ⟨h.1, fun t ht => ?_⟩
      rcases ht.2.eq_or_lt with heq | htu
      · rw [heq]
        exact subset_closure hψ'.mem
      · rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 η.continuous t ε hε
        obtain ⟨c, hc₁, hc₂⟩ := exists_rat_btwn (show t < min (t + δ / 2) u by
          refine lt_min (by linarith) htu)
        obtain ⟨d, hd₁, hd₂⟩ := exists_rat_btwn hc₂
        obtain ⟨q, hq₁, hq₂, hq⟩ := h.2 c d (by linarith [ht.1]) hd₁ (hd₂.le.trans (min_le_right _ _))
        refine ⟨η q, hq, ?_⟩
        rw [dist_comm]
        refine hcont q ?_
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_left (t + δ / 2) u]
    · exact hs₀.2

/-- **The intrinsic chart succeeds and is the inverse chart of Berestycki–Gwynne on the window domain.** -/
theorem windowGoodIntr_and_eqOn_windowChartBG (hau : a < u)
    (hψ : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) (hreg : SegmentsRegularClosed η)
    (hfib : ∀ t, η t = η u → t = u) :
    WindowGoodIntr a u b η ∧
      ∀ x ∈ windowDomain η a u b, windowChartBG a u b η x = windowChartIntr a u b η x := by
  obtain ⟨hD, hv⟩ := openWindowDiscInv_eq_windowChart hψ
  have hα := windowEntryIntr_eq_windowStartBG hau hψ hreg
  have hs₀ := windowStartBG_mem_Icc (b := b) hau.le η
  have hs₀u := windowStartBG_lt (b := b) hau η
  set α := windowStartBG a u b η
  have hψ₀ := isInverseChart_windowChart hψ.choose_spec
  -- every interval `(α, α + 1/(m+1))` contains a rational visit
  have hex : ∀ m : ℕ, ∃ n, IsEntryVisit a u b η m n := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (lt_min (show α < α + 1 / ((m : ℝ) + 1) by linarith) hs₀u)
    obtain ⟨d, hd₁, hd₂⟩ := exists_rat_btwn hr₂
    obtain ⟨q, hq₁, hq₂, hq⟩ :=
      windowVisitsDense_of_windowStartBG_lt hau.le hψ hreg hr₁ r d le_rfl hd₁ (hd₂.le.trans (min_le_right _ _))
    obtain ⟨n, hn⟩ := ratEnum_surjective q
    refine ⟨n, ?_⟩
    unfold IsEntryVisit
    rw [hn, hα]
    refine ⟨by linarith, ?_, ?_, hq⟩
    · linarith [min_le_left (α + 1 / ((m : ℝ) + 1)) u]
    · linarith [min_le_right (α + 1 / ((m : ℝ) + 1)) u]
  -- the chart values converge to the chart image of `η(α)`
  have hval : ∀ m, entryChartValue a u b η m =
      windowChart a u b η (η (ratEnum (entryIdx a u b η m))) := by
    intro m
    have hvis : IsEntryVisit a u b η m (entryIdx a u b η m) := Nat.sInf_mem (hex m)
    unfold entryChartValue
    rw [ite_eq_left (hex m)]
    exact hv _ hvis.2.2.2
  have htime : Tendsto (fun m => ((ratEnum (entryIdx a u b η m) : ℚ) : ℝ)) atTop (𝓝 α) := by
    have hup : Tendsto (fun m : ℕ => α + 1 / ((m : ℝ) + 1)) atTop (𝓝 α) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add α
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_) (fun m => ?_)
    · have hvis : IsEntryVisit a u b η m (entryIdx a u b η m) := Nat.sInf_mem (hex m)
      have h1 := hvis.1
      rw [hα] at h1
      exact h1.le
    · have hvis : IsEntryVisit a u b η m (entryIdx a u b η m) := Nat.sInf_mem (hex m)
      have h1 := hvis.2.1
      rw [hα] at h1
      exact h1.le
  have hlim : Tendsto (fun m => entryChartValue a u b η m) atTop (𝓝 (windowChart a u b η (η α))) := by
    rw [funext hval]
    exact ((windowChart a u b η).continuous.comp η.continuous).continuousAt.tendsto.comp htime
  have hC : EntryConverges a u b η := ⟨_, hlim⟩
  have hξ : windowEntryPoint a u b η = windowChart a u b η (η α) :=
    tendsto_nhds_unique (tendsto_windowEntryPoint hC) hlim
  -- the entry point is not the chart centre
  have hξ0 : windowEntryPoint a u b η ≠ 0 := by
    rw [hξ]
    intro h0
    have hmem := (windowStartBG_mem (b := b) hau.le hψ).2
    have heq : η α = η u := hψ₀.injOn hmem (subset_closure hψ₀.mem) (h0.trans hψ₀.apply_point.symm)
    exact (ne_of_lt hs₀u) (hfib α heq)
  refine ⟨⟨hD, hC, hξ0⟩, fun x hx => ?_⟩
  rw [windowChartBG_apply, windowRotBG, windowChartIntr, hξ, hv x hx]

end Deterministic

end MatedCRT
