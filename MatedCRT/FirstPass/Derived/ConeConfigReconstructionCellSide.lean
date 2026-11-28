import MatedCRT.FirstPass.Derived.CellSideMult

/-!
# The frontier-side count of two cells under reparametrization of time

The contact relation `cellSideContact`, the branch times `cellSideBranchTimes` and the count
`cellSideCount` of two cells depend on the curve only through the images of intervals of times.
Hence they are transported by an increasing homeomorphism `τ` of the time line: the count of the
cell intervals `[a, b]`, `[c, d]` for `η ∘ τ` is the count of `[τ a, τ b]`, `[τ c, τ d]` for `η`
(`cellSideCount_comp_orderIso`).

Every increasing quadruple `a < b < c < d` is the image of `0 < 1 < 2 < 3` under an explicit
increasing piecewise linear homeomorphism of the line, which depends continuously on the
quadruple. Together with `measurable_cellSideMult` this gives
`measurable_cellSideCount_endpoints`: the count is jointly measurable in the four endpoints and
the curve.
-/

set_option autoImplicit false

open Set Metric Filter Topology MeasureTheory

namespace MatedCRT

/-! ### Transport of contacts and counts under an increasing homeomorphism of time -/

/-- Contacts pull back along an increasing homeomorphism of time. -/
theorem cellSideContact_of_comp_orderIso (τ : ℝ ≃o ℝ) {a d : ℝ} {η : ℝ → ℂ} {v w : ℝ}
    (h : cellSideContact a d (η ∘ τ) v w) : cellSideContact (τ a) (τ d) η (τ v) (τ w) := by
  intro p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  have hlt : ∀ (p x : ℝ), p < τ x → τ.symm p < x := fun p x hp => by
    simpa using τ.symm.strictMono hp
  have hgt : ∀ (p x : ℝ), τ x < p → x < τ.symm p := fun p x hp => by
    simpa using τ.symm.strictMono hp
  have hlt' : ∀ (p x : ℝ), τ.symm p < x → p < τ x := fun p x hp => by
    simpa using τ.strictMono hp
  have hgt' : ∀ (p x : ℝ), x < τ.symm p → τ x < p := fun p x hp => by
    simpa using τ.strictMono hp
  obtain ⟨p₁', hp₁'1, hp₁'2⟩ := exists_rat_btwn (hlt _ _ hv.1)
  obtain ⟨p₂', hp₂'1, hp₂'2⟩ := exists_rat_btwn (hgt _ _ hv.2)
  obtain ⟨q₁', hq₁'1, hq₁'2⟩ := exists_rat_btwn (hlt _ _ hw.1)
  obtain ⟨q₂', hq₂'1, hq₂'2⟩ := exists_rat_btwn (hgt _ _ hw.2)
  have hPm : ∀ x ∈ Icc (p₁' : ℝ) p₂', τ x ∈ Icc (p₁ : ℝ) p₂ := fun x hx =>
    ⟨(hlt' _ _ (hp₁'1.trans_le hx.1)).le, (hgt' _ _ (lt_of_le_of_lt hx.2 hp₂'2)).le⟩
  have hQm : ∀ x ∈ Icc (q₁' : ℝ) q₂', τ x ∈ Icc (q₁ : ℝ) q₂ := fun x hx =>
    ⟨(hlt' _ _ (hq₁'1.trans_le hx.1)).le, (hgt' _ _ (lt_of_le_of_lt hx.2 hq₂'2)).le⟩
  obtain ⟨K, hK, hKc, hKconn, hKd⟩ := h p₁' p₂' q₁' q₂' ⟨hp₁'2, hp₂'1⟩ ⟨hq₁'2, hq₂'1⟩
    (Set.disjoint_left.2 fun x hx1 hx2 => Set.disjoint_left.1 hdisj
      ⟨hlt' _ _ (hp₁'1.trans hx1.1), hgt' _ _ (hx1.2.trans hp₂'2)⟩
      ⟨hlt' _ _ (hq₁'1.trans hx2.1), hgt' _ _ (hx2.2.trans hq₂'2)⟩)
    (fun x hx => by
      have := hP (hPm x hx)
      exact ⟨τ.lt_iff_lt.1 this.1, τ.lt_iff_lt.1 this.2⟩)
    (fun x hx => by
      have := hQ (hQm x hx)
      exact ⟨τ.lt_iff_lt.1 this.1, τ.lt_iff_lt.1 this.2⟩)
  refine ⟨K, fun z hz => ?_, hKc, hKconn, hKd⟩
  obtain ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩ := hK hz
  exact ⟨⟨τ x, hPm x hx, hxz⟩, ⟨τ y, hQm y hy, hyz⟩⟩

/-- **Contacts are transported by an increasing homeomorphism of time.** -/
theorem cellSideContact_comp_orderIso (τ : ℝ ≃o ℝ) (a d : ℝ) (η : ℝ → ℂ) (v w : ℝ) :
    cellSideContact a d (η ∘ τ) v w ↔ cellSideContact (τ a) (τ d) η (τ v) (τ w) := by
  refine ⟨cellSideContact_of_comp_orderIso τ, fun h => ?_⟩
  have hcomp : (η ∘ ⇑τ) ∘ ⇑τ.symm = η := funext fun t => by simp
  have h' := cellSideContact_of_comp_orderIso τ.symm (η := η ∘ τ) (a := τ a) (d := τ d)
    (v := τ v) (w := τ w) (by rwa [hcomp])
  simpa using h'

/-- The branch times of the curve `η ∘ τ` are the preimage under `τ` of the branch times of `η`. -/
theorem cellSideBranchTimes_comp_orderIso (τ : ℝ ≃o ℝ) (a b c d : ℝ) (η : ℝ → ℂ) :
    cellSideBranchTimes a b c d (η ∘ τ) = τ ⁻¹' cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η := by
  ext u
  simp only [cellSideBranchTimes, mem_ofPred_eq, mem_preimage, mem_Ioo,
    cellSideContact_comp_orderIso, τ.lt_iff_lt]
  refine and_congr_right fun _ => ⟨fun ⟨s, hs, t, ht, h⟩ => ⟨τ s, ?_, τ t, ?_, h⟩, ?_⟩
  · exact ⟨τ.strictMono hs.1, τ.strictMono hs.2⟩
  · exact ⟨τ.strictMono ht.1, τ.strictMono ht.2⟩
  · rintro ⟨s', hs', t', ht', h⟩
    refine ⟨τ.symm s', ⟨?_, ?_⟩, τ.symm t', ⟨?_, ?_⟩, ?_⟩
    · simpa using τ.symm.strictMono hs'.1
    · simpa using τ.symm.strictMono hs'.2
    · simpa using τ.symm.strictMono ht'.1
    · simpa using τ.symm.strictMono ht'.2
    · simpa using h

open Classical in
/-- **The frontier-side count of two cells is invariant under an increasing reparametrization of
time.** -/
theorem cellSideCount_comp_orderIso (τ : ℝ ≃o ℝ) (a b c d : ℝ) (η : ℝ → ℂ) :
    cellSideCount a b c d (η ∘ τ) = cellSideCount (τ a) (τ b) (τ c) (τ d) η := by
  unfold cellSideCount
  rw [cellSideBranchTimes_comp_orderIso]
  have h1 : (τ ⁻¹' cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η).Nonempty ↔
      (cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η).Nonempty := by
    refine ⟨fun ⟨u, hu⟩ => ⟨τ u, hu⟩, fun ⟨u, hu⟩ => ⟨τ.symm u, ?_⟩⟩
    simpa using hu
  have h2 : (∃ u ∈ τ ⁻¹' cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η,
      ∃ v ∈ τ ⁻¹' cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η, u ≠ v) ↔
      ∃ u ∈ cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η,
        ∃ v ∈ cellSideBranchTimes (τ a) (τ b) (τ c) (τ d) η, u ≠ v := by
    refine ⟨fun ⟨u, hu, v, hv, huv⟩ => ⟨τ u, hu, τ v, hv, fun h => huv (τ.injective h)⟩,
      fun ⟨u, hu, v, hv, huv⟩ => ⟨τ.symm u, ?_, τ.symm v, ?_, fun h => huv (τ.symm.injective h)⟩⟩
    · simpa using hu
    · simpa using hv
  exact congrArg₂ (· + ·) (if_congr h1 rfl rfl) (if_congr h2 rfl rfl)

/-! ### An explicit increasing homeomorphism of time with prescribed values at `0, 1, 2, 3` -/

/-- The clamp of a real number to `[0, 1]`. -/
def clampUnit (t : ℝ) : ℝ := max 0 (min t 1)

theorem clampUnit_mono : Monotone clampUnit := fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

/-- The increasing piecewise linear map with `0 ↦ a`, `1 ↦ b`, `2 ↦ c`, `3 ↦ d` and slope `1`
outside `[0, 3]`. -/
def timeChange (a b c d t : ℝ) : ℝ :=
  a + min t 0 + (b - a) * clampUnit t + (c - b) * clampUnit (t - 1) + (d - c) * clampUnit (t - 2) +
    max (t - 3) 0

theorem timeChange_zero (a b c d : ℝ) : timeChange a b c d 0 = a := by
  norm_num [timeChange, clampUnit]

theorem timeChange_one (a b c d : ℝ) : timeChange a b c d 1 = b := by
  norm_num [timeChange, clampUnit]

theorem timeChange_two (a b c d : ℝ) : timeChange a b c d 2 = c := by
  norm_num [timeChange, clampUnit]

theorem timeChange_three (a b c d : ℝ) : timeChange a b c d 3 = d := by
  norm_num [timeChange, clampUnit]

theorem continuous_timeChange : Continuous fun p : (ℝ × ℝ × ℝ × ℝ) × ℝ =>
    timeChange p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 := by
  unfold timeChange clampUnit
  fun_prop

/-- The five pieces of `t` add up to `t`. -/
theorem min_add_clampUnit_add (t : ℝ) :
    min t 0 + clampUnit t + clampUnit (t - 1) + clampUnit (t - 2) + max (t - 3) 0 = t := by
  unfold clampUnit
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- `timeChange` increases at least linearly, with a slope bounded below by a positive constant. -/
theorem exists_timeChange_lower {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ s t : ℝ, s ≤ t →
      μ * (t - s) ≤ timeChange a b c d t - timeChange a b c d s := by
  refine ⟨min (min 1 (b - a)) (min (c - b) (d - c)), lt_min (lt_min one_pos (sub_pos.2 hab))
    (lt_min (sub_pos.2 hbc) (sub_pos.2 hcd)), fun s t hst => ?_⟩
  set μ := min (min 1 (b - a)) (min (c - b) (d - c)) with hμ
  have hμ1 : μ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hμ2 : μ ≤ b - a := (min_le_left _ _).trans (min_le_right _ _)
  have hμ3 : μ ≤ c - b := (min_le_right _ _).trans (min_le_left _ _)
  have hμ4 : μ ≤ d - c := (min_le_right _ _).trans (min_le_right _ _)
  have hD0 : 0 ≤ min t 0 - min s 0 := sub_nonneg.2 (min_le_min hst le_rfl)
  have hD1 : 0 ≤ clampUnit t - clampUnit s := sub_nonneg.2 (clampUnit_mono hst)
  have hD2 : 0 ≤ clampUnit (t - 1) - clampUnit (s - 1) :=
    sub_nonneg.2 (clampUnit_mono (sub_le_sub_right hst 1))
  have hD3 : 0 ≤ clampUnit (t - 2) - clampUnit (s - 2) :=
    sub_nonneg.2 (clampUnit_mono (sub_le_sub_right hst 2))
  have hD4 : 0 ≤ max (t - 3) 0 - max (s - 3) 0 :=
    sub_nonneg.2 (max_le_max (sub_le_sub_right hst 3) le_rfl)
  have hsum := min_add_clampUnit_add t
  have hsum' := min_add_clampUnit_add s
  unfold timeChange
  nlinarith [mul_nonneg (sub_nonneg.2 hμ1) hD0, mul_nonneg (sub_nonneg.2 hμ2) hD1,
    mul_nonneg (sub_nonneg.2 hμ3) hD2, mul_nonneg (sub_nonneg.2 hμ4) hD3,
    mul_nonneg (sub_nonneg.2 hμ1) hD4]

/-- For `a < b < c < d`, `timeChange a b c d` is an increasing homeomorphism of the line. -/
theorem exists_orderIso_timeChange {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ τ : ℝ ≃o ℝ, ⇑τ = timeChange a b c d := by
  obtain ⟨μ, hμ, hlow⟩ := exists_timeChange_lower hab hbc hcd
  have hmono : StrictMono (timeChange a b c d) := fun s t hst => by
    have := hlow s t hst.le
    nlinarith [mul_pos hμ (sub_pos.2 hst)]
  have hcont : Continuous (timeChange a b c d) := by
    unfold timeChange clampUnit
    fun_prop
  have hsurj : Function.Surjective (timeChange a b c d) := by
    refine hcont.surjective ?_ ?_
    · refine tendsto_atTop_mono' _ (eventually_atTop.2 ⟨0, fun t ht => ?_⟩)
        ((tendsto_id.const_mul_atTop hμ).atTop_add (tendsto_const_nhds (x := a)))
      have := hlow 0 t ht
      rw [timeChange_zero] at this
      simp only [id]
      linarith
    · refine tendsto_atBot_mono' _ (eventually_atBot.2 ⟨0, fun t ht => ?_⟩)
        (((tendsto_const_mul_atBot_of_pos hμ).2 tendsto_id).atBot_add (tendsto_const_nhds (x := a)))
      have := hlow t 0 ht
      rw [timeChange_zero] at this
      simp only [id]
      linarith
  exact ⟨hmono.orderIsoOfSurjective _ hsurj, rfl⟩

/-- The multiplicity of the cells `1` and `3` at mesh `1` is the count of the intervals
`[0, 1]` and `[2, 3]`. -/
theorem cellSideMult_one_one_three (η : ℝ → ℂ) :
    cellSideMult 1 η 1 3 = cellSideCount 0 1 2 3 η := by
  norm_num [cellSideMult]

/-- Joint measurability in the four endpoints and the curve, on increasing quadruples. -/
theorem measurable_cellSideCount_endpoints :
    Measurable fun x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) =>
      if x.1.1 < x.1.2.1 ∧ x.1.2.1 < x.1.2.2.1 ∧ x.1.2.2.1 < x.1.2.2.2 then
        cellSideCount x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 ⇑x.2 else 0 := by
  let Φ : ℝ × ℝ × ℝ × ℝ → C(ℝ, ℝ) := fun q =>
    ⟨timeChange q.1 q.2.1 q.2.2.1 q.2.2.2, by unfold timeChange clampUnit; fun_prop⟩
  have hΦ : Continuous Φ := ContinuousMap.continuous_of_continuous_uncurry _ continuous_timeChange
  have hG : Continuous fun x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) => x.2.comp (Φ x.1) :=
    continuous_snd.compCM (hΦ.comp continuous_fst)
  have hinc : MeasurableSet {x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) |
      x.1.1 < x.1.2.1 ∧ x.1.2.1 < x.1.2.2.1 ∧ x.1.2.2.1 < x.1.2.2.2} := by
    have h1 : MeasurableSet {x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) | x.1.1 < x.1.2.1} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) | x.1.2.1 < x.1.2.2.1} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    have h3 : MeasurableSet {x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) | x.1.2.2.1 < x.1.2.2.2} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  have heq : (fun x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) =>
      if x.1.1 < x.1.2.1 ∧ x.1.2.1 < x.1.2.2.1 ∧ x.1.2.2.1 < x.1.2.2.2 then
        cellSideCount x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 ⇑x.2 else 0) =
      fun x : (ℝ × ℝ × ℝ × ℝ) × C(ℝ, ℂ) =>
        if x.1.1 < x.1.2.1 ∧ x.1.2.1 < x.1.2.2.1 ∧ x.1.2.2.1 < x.1.2.2.2 then
          cellSideMult 1 ⇑(x.2.comp (Φ x.1)) 1 3 else 0 := by
    funext x
    split_ifs with h
    · obtain ⟨τ, hτ⟩ := exists_orderIso_timeChange h.1 h.2.1 h.2.2
      have hcoe : ⇑(x.2.comp (Φ x.1)) = ⇑x.2 ∘ ⇑τ := by
        rw [hτ]
        rfl
      rw [hcoe, cellSideMult_one_one_three, cellSideCount_comp_orderIso, hτ, timeChange_zero,
        timeChange_one, timeChange_two, timeChange_three]
    · rfl
  rw [heq]
  exact Measurable.ite hinc ((measurable_cellSideMult 1 1 3).comp hG.measurable) measurable_const

end MatedCRT
