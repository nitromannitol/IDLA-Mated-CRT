import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonDiscrete
import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonCrossing
import MatedCRT.FirstPass.Derived.ValidCurveFixedTime

/-!
# The inside cells of the window

Deterministic facts on the cells inside the window `(a, u, b)` with retained times `[p, q]` (written answer MQ-sbl-35,
lines 13-21 and 40-45), and the almost sure visit property of a valid curve.

* `MatedCRT.FrozenPath.modulusOn`: the modulus of continuity of a curve on `[p, q]`; it bounds the diameters of the
  retained cells and tends to `0` along locally uniformly convergent curves (`tendsto_modulusOn`).
* `MatedCRT.FrozenPath.windowGapBG_pos_of_windowCellInside`: the vertex of an inside cell lies in the window.
* `MatedCRT.FrozenPath.windowCellInside_of_modulusOn_lt`: a vertex at signed distance larger than the modulus is the
  vertex of an inside cell, when the curve visits the window domain during `[a, b]` only.
* `MatedCRT.FrozenPath.eventually_windowCellInside_ceil`: the cell `⌈u/ε⌉` is inside for all small `ε`.
* `MatedCRT.FrozenPath.ae_windowDomain_preimage_subset`: a valid curve visits the window domain during `[a, b]` only
  (rational times have singleton fibres).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

namespace FrozenPath

/-! ### The frozen index stays inside -/

theorem frozenIdx_mem {In : ℕ → Prop} (h0 : In 0) (i : ℕ) : In (frozenIdx In i) := by
  classical
  by_cases hex : ∃ j, ¬ In j
  · rw [frozenIdx_eq_min hex i]
    exact mem_of_le_find_sub_one hex (min_le_right _ _) h0
  · have hall : ∀ j, In j := fun j => by_contra fun hn => hex ⟨j, hn⟩
    exact hall _

/-! ### The modulus of continuity on `[p, q]` -/

/-- The modulus of continuity `sup {|f s - f t| : s, t ∈ [p, q], |s - t| ≤ δ}` of `f` on `[p, q]` at scale `δ`. -/
noncomputable def modulusOn (f : C(ℝ, ℂ)) (p q δ : ℝ) : ℝ :=
  sSup ((fun st : ℝ × ℝ => ‖f st.1 - f st.2‖) '' {st | st.1 ∈ Icc p q ∧ st.2 ∈ Icc p q ∧ |st.1 - st.2| ≤ δ})

theorem bddAbove_modulusOn_set (f : C(ℝ, ℂ)) (p q δ : ℝ) :
    BddAbove ((fun st : ℝ × ℝ => ‖f st.1 - f st.2‖) ''
      {st | st.1 ∈ Icc p q ∧ st.2 ∈ Icc p q ∧ |st.1 - st.2| ≤ δ}) := by
  have hc : IsCompact ((fun st : ℝ × ℝ => ‖f st.1 - f st.2‖) '' (Icc p q ×ˢ Icc p q)) :=
    (isCompact_Icc.prod isCompact_Icc).image
      ((f.continuous.comp continuous_fst).sub (f.continuous.comp continuous_snd)).norm
  refine hc.bddAbove.mono (image_mono ?_)
  intro st hst
  exact ⟨hst.1, hst.2.1⟩

theorem norm_sub_le_modulusOn (f : C(ℝ, ℂ)) {p q δ s t : ℝ} (hs : s ∈ Icc p q) (ht : t ∈ Icc p q)
    (hst : |s - t| ≤ δ) : ‖f s - f t‖ ≤ modulusOn f p q δ :=
  le_csSup (bddAbove_modulusOn_set f p q δ) ⟨(s, t), ⟨hs, ht, hst⟩, rfl⟩

theorem modulusOn_nonneg (f : C(ℝ, ℂ)) (p q δ : ℝ) : 0 ≤ modulusOn f p q δ :=
  Real.sSup_nonneg (by
    rintro _ ⟨st, -, rfl⟩
    exact norm_nonneg _)

/-- **The modulus of continuity tends to `0` along locally uniformly convergent curves and vanishing scales.** -/
theorem tendsto_modulusOn {fs : ℕ → C(ℝ, ℂ)} {f : C(ℝ, ℂ)} (hf : Tendsto fs atTop (𝓝 f)) {δs : ℕ → ℝ}
    (hδ : Tendsto δs atTop (𝓝 0)) (p q : ℝ) :
    Tendsto (fun l => modulusOn (fs l) p q (δs l)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro c hc
  obtain ⟨ρ, hρ, hρf⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc p q) f.continuous.continuousOn) (c / 4)
    (by positivity)
  have hu : TendstoUniformlyOn (fun l => ⇑(fs l)) f atTop (Icc p q) := by
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact] at hf
    exact hf _ isCompact_Icc
  have hu' := Metric.tendstoUniformlyOn_iff.1 hu (c / 4) (by positivity)
  have hδ' : ∀ᶠ l in atTop, δs l < ρ := hδ.eventually (eventually_lt_nhds hρ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu'.and hδ')
  refine ⟨N, fun l hl => ?_⟩
  obtain ⟨h1, h2⟩ := hN l hl
  have hle : modulusOn (fs l) p q (δs l) ≤ 3 * (c / 4) := by
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨⟨s, t⟩, ⟨hs, ht, hst⟩, rfl⟩
    have e1 := h1 s hs
    have e2 := h1 t ht
    have e3 := hρf s hs t ht (by rw [Real.dist_eq]; exact hst.trans_lt h2)
    rw [dist_eq_norm] at e1 e2 e3
    have t1 := norm_sub_le_norm_sub_add_norm_sub (fs l s) (f s) (fs l t)
    have t2 := norm_sub_le_norm_sub_add_norm_sub (f s) (f t) (fs l t)
    have t3 := norm_sub_rev (fs l s) (f s)
    show ‖fs l s - fs l t‖ ≤ 3 * (c / 4)
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulusOn_nonneg _ p q _)]
  linarith

/-! ### Inside cells and the signed distance -/

/-- The vertex `η(εj)` of an inside cell lies in the window: the signed distance is positive there. -/
theorem windowGapBG_pos_of_windowCellInside {a u b p q ε : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (hη : η ∈ windowChartCurves a u b) (hε : 0 < ε) {j : ℤ} (hj : WindowCellInside a u b p q ε η j) :
    0 < windowGapBG a u b η (η (ε * j)) := by
  have h := hG.mem_windowDomain_of_windowCellInside hε hj (t := ε * j)
    ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩
  rw [← gapDomain_windowGapBG_of_mem hη] at h
  exact h

/-- **A vertex deep in the window is the vertex of an inside cell.** If the curve visits the window domain during
`[a, b]` only, `ε ≤ a - p` and `b ≤ q`, and the signed distance at `η(εj)` exceeds the modulus of continuity of `η` on
`[p, q]` at scale `ε`, then the cell of `j` is inside. -/
theorem windowCellInside_of_modulusOn_lt {a u b p q ε : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (hη : η ∈ windowChartCurves a u b) (hε : 0 < ε) (hεa : ε ≤ a - p) (hbq : b ≤ q)
    (hpre : ∀ t, η t ∈ windowDomain η a u b → t ∈ Icc a b) {j : ℤ}
    (hlt : modulusOn η p q ε < windowGapBG a u b η (η (ε * j))) :
    WindowCellInside a u b p q ε η j := by
  have hU := gapDomain_windowGapBG_of_mem hη
  have hpos : 0 < windowGapBG a u b η (η (ε * j)) := (modulusOn_nonneg η p q ε).trans_lt hlt
  have hmem : η (ε * j) ∈ windowDomain η a u b := by
    rw [← hU]
    exact hpos
  have hab := hpre _ hmem
  have h3 : ε * ((j : ℝ) - 1) = ε * j - ε := by ring
  have hret : WindowRetained p q ε j := ⟨by linarith [hab.1], by linarith [hab.2]⟩
  refine (hG.windowCellInside_iff_subset hε j).2 ⟨hret, fun t ht => ?_⟩
  have htpq : t ∈ Icc p q := ⟨hret.1.trans ht.1, ht.2.trans hret.2⟩
  have hjpq : ε * (j : ℝ) ∈ Icc p q := ⟨by linarith [hret.1], hret.2⟩
  have hd : ‖η t - η (ε * j)‖ ≤ modulusOn η p q ε := by
    refine norm_sub_le_modulusOn η htpq hjpq ?_
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  by_contra hnot
  have hgap : windowGapBG a u b η (η (ε * j)) ≤ infDist (η (ε * j)) (windowDomain η a u b)ᶜ := by
    rw [windowGapBG, ite_eq_left hη, signedGap_apply]
    linarith [infDist_nonneg (x := η (ε * j)) (s := closure (windowDomain η a u b))]
  have hinf : infDist (η (ε * j)) (windowDomain η a u b)ᶜ ≤ dist (η (ε * j)) (η t) :=
    infDist_le_dist_of_mem hnot
  rw [dist_eq_norm, norm_sub_rev] at hinf
  linarith

/-- **The starting cell is inside for all small cell sizes.** If the window has an intrinsic chart and contains
`η(u)`, and `p < u < q`, then the cell `⌈u/ε⌉` is inside for all small `ε`. -/
theorem eventually_windowCellInside_ceil {a u b p q : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (hpu : p < u) (huq : u < q) (hu : η u ∈ windowDomain η a u b) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ n in atTop, WindowCellInside a u b p q (ε n) η ⌈u / ε n⌉ := by
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ t, |t - u| < ρ → η t ∈ windowDomain η a u b := by
    have h := (η.continuous.continuousAt (x := u)).preimage_mem_nhds
      ((isOpen_windowDomain η a u b).mem_nhds hu)
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 h
    exact ⟨ρ, hρ, fun t ht => hsub (by rw [Metric.mem_ball, Real.dist_eq]; exact ht)⟩
  have hsmall : ∀ᶠ n in atTop, ε n < min ρ (min (u - p) (q - u)) :=
    hε0.eventually (eventually_lt_nhds (lt_min hρ (lt_min (by linarith) (by linarith))))
  filter_upwards [hsmall] with n hn
  have hεn := hε n
  have hne : ε n ≠ 0 := hεn.ne'
  have hc1 : u / ε n ≤ ⌈u / ε n⌉ := Int.le_ceil _
  have hc2 : (⌈u / ε n⌉ : ℝ) < u / ε n + 1 := Int.ceil_lt_add_one _
  have he : ε n * (u / ε n) = u := by field_simp
  have h1 : u ≤ ε n * ⌈u / ε n⌉ := by
    have h := mul_le_mul_of_nonneg_left hc1 hεn.le
    rwa [he] at h
  have h2 : ε n * ⌈u / ε n⌉ < u + ε n := by
    have h := mul_lt_mul_of_pos_left hc2 hεn
    rwa [mul_add, he, mul_one] at h
  have hρn : ε n < ρ := hn.trans_le (min_le_left _ _)
  have hpn : ε n < u - p := hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hqn : ε n < q - u := hn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have h3 : ε n * ((⌈u / ε n⌉ : ℝ) - 1) = ε n * ⌈u / ε n⌉ - ε n := by ring
  refine (hG.windowCellInside_iff_subset hεn _).2 ⟨⟨by linarith, by linarith⟩, fun t ht => hball t ?_⟩
  rw [abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-! ### Visits of a valid curve to the window domain -/

/-- **A valid curve visits the window domain during `[a, b]` only** (written answer MQ-sbl-35, line 15): otherwise
an open time interval outside `[a, b]` has a rational visit to `U ⊆ η([a, b])`, contradicting the singleton fibre of
the rational time. -/
theorem ae_windowDomain_preimage_subset {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (a u b : ℝ) : ∀ᵐ ω ∂S.P, ∀ t, η' ω t ∈ windowDomain (η' ω) a u b → t ∈ Icc a b := by
  have hrat : ∀ᵐ ω ∂S.P, ∀ r : ℚ, ∀ t, S.η ω t = S.η ω r → t = r :=
    ae_all_iff.2 fun r => hS.ae_fixedTime_singleton_fibre r
  filter_upwards [hrat, hae] with ω hω he
  intro t ht
  by_contra hnot
  have hopen : IsOpen ((η' ω) ⁻¹' windowDomain (η' ω) a u b ∩ (Icc a b)ᶜ) :=
    ((isOpen_windowDomain _ a u b).preimage (η' ω).continuous).inter isClosed_Icc.isOpen_compl
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) ∈ (η' ω) ⁻¹' windowDomain (η' ω) a u b ∩ (Icc a b)ᶜ :=
    Rat.denseRange_cast.exists_mem_open hopen ⟨t, ht, hnot⟩
  have hsub : windowDomain (η' ω) a u b ⊆ (η' ω) '' Icc a b :=
    (connectedComponentIn_subset _ _).trans interior_subset
  obtain ⟨s, hs, hsr⟩ := hsub hr.1
  have hsr' : S.η ω s = S.η ω r := by
    rw [← he]
    exact hsr
  have hsr'' := hω r s hsr'
  rw [hsr''] at hs
  exact hr.2 hs

end FrozenPath

end MatedCRT
