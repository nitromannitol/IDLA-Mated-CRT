import MatedCRT.FirstPass.Derived.ConeRadialLevelLimits

/-!
# Measurability of the cone scale radius and of the rescaled circle average process

For a `γ`-quantum cone the cone scale radius `R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}` is almost surely
well defined (`ae_coneScaleRadius_spec`); here it is shown to be `P`-almost measurable, and so is the circle average
process `(r, z) ↦ h_{R_b r}(R_b z) + Q log R_b - γ⁻¹ log b` of the rescaled field, as a random element of
`(0, ∞) × ℂ → ℝ` with the product σ-algebra.  (Both facts are part of the statement `P.map (rescaled) = P.map h`:
`Measure.map` vanishes on a map that is not almost everywhere measurable.)

The scale radius is not read off the rational times of the level function `f s = h_{e^s}(0) + Q s`: `f` may touch
the level `c` from above at `log R_b`.  Instead, almost surely, `R_b > x` iff `f` takes a value `≤ c` at some
`s > log x` (intermediate value theorem and `f > c` beyond `R_b`), and for a function continuous on a compact
interval the existence of a point with `g ≤ 0` is the countable condition "for every `k` some rational point has
`g < 1/(k+1)`".  The circle average process of the rescaled field is the composition of a Carathéodory function
(continuous in `(r, z)`, measurable in the sample) with the measurable random point `(R_b r, R_b z)`.
-/

open MeasureTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- A point of `(a, b)` where a function continuous on `(0, ∞)` is `≤ 0` gives rational points of `(a, b)` where it is
below any prescribed positive level. -/
lemma exists_rat_mem_Ioo_lt_of_le {g : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (Ioi 0)) (ha : 0 < a)
    {r : ℝ} (hr : r ∈ Ioo a b) (hgr : g r ≤ 0) (k : ℕ) :
    ∃ q : ℚ, (q : ℝ) ∈ Ioo a b ∧ g q < 1 / ((k : ℝ) + 1) := by
  have hr0 : 0 < r := ha.trans hr.1
  have hcont : ContinuousAt g r := hg.continuousAt (Ioi_mem_nhds hr0)
  have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hev : ∀ᶠ s in 𝓝 r, s ∈ Ioo a b ∧ g s < 1 / ((k : ℝ) + 1) :=
    Filter.Eventually.and (Ioo_mem_nhds hr.1 hr.2)
      (hcont.tendsto.eventually (gt_mem_nhds (lt_of_le_of_lt hgr hε)))
  obtain ⟨V, hVsub, hVopen, hrV⟩ := mem_nhds_iff.1 hev
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hVopen ⟨r, hrV⟩
  exact ⟨q, hVsub hq⟩

/-- Conversely, rational points of `(a, b)` with arbitrarily small values of a function continuous on `[a, b]` give a
point of `[a, b]` where it is `≤ 0` (the minimum on the compact interval). -/
lemma exists_mem_Icc_le_of_rat {g : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (Ioi 0)) (ha : 0 < a) (hab : a < b)
    (h : ∀ k : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Ioo a b ∧ g q < 1 / ((k : ℝ) + 1)) :
    ∃ r ∈ Icc a b, g r ≤ 0 := by
  have hsub : Icc a b ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le ha hs.1
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) (hg.mono hsub)
  refine ⟨r, hr, ?_⟩
  by_contra hpos
  push Not at hpos
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  obtain ⟨q, hq, hgq⟩ := h k
  have := isMinOn_iff.1 hmin (q : ℝ) (Ioo_subset_Icc_self hq)
  linarith

/-- **Pathwise description of `{R_b > x}`.**  For a circle average family continuous on `(0, ∞) × ℂ`, with `R` a point
of the level set beyond which the level function stays above `c`, and `x ≥ 0`: `x < R` iff for some `n, m` and every `k`
there is a rational `q` in `(x + 1/(n+1), x + m + 2)` with `h_q(0) + Q log q - c < 1/(k+1)`. -/
lemma lt_scaleRadius_iff {γ b R : ℝ} {hc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ))
    (h1 : hc R 0 + lqgQ γ * Real.log R = γ⁻¹ * Real.log b)
    (h2 : ∀ r : ℝ, R < r → γ⁻¹ * Real.log b < hc r 0 + lqgQ γ * Real.log r) {x : ℝ} (hx : 0 ≤ x) :
    x < R ↔ ∃ n m : ℕ, ∀ k : ℕ, ∃ q : ℚ,
      (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hc q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1) := by
  set g : ℝ → ℝ := fun r => hc r 0 + lqgQ γ * Real.log r - γ⁻¹ * Real.log b with hg
  have hgc : ContinuousOn g (Ioi 0) := by
    have h0 : ContinuousOn (fun r : ℝ => hc r 0) (Ioi 0) :=
      hcont.comp (f := fun r : ℝ => (r, (0 : ℂ))) (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, mem_univ _⟩)
    have hl : ContinuousOn (fun r : ℝ => Real.log r) (Ioi 0) :=
      Real.continuousOn_log.mono (fun r hr => ne_of_gt hr)
    exact (h0.add (continuousOn_const.mul hl)).sub continuousOn_const
  constructor
  · intro hxR
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hxR)
    obtain ⟨m, hm⟩ := exists_nat_gt (R - x)
    have hpos : 0 < x + 1 / ((n : ℝ) + 1) := by positivity
    have hRmem : R ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) := ⟨by linarith, by linarith⟩
    have hgR : g R ≤ 0 := by simp only [hg]; linarith
    exact ⟨n, m, fun k => exists_rat_mem_Ioo_lt_of_le hgc hpos hRmem hgR k⟩
  · rintro ⟨n, m, hq⟩
    have hpos : 0 < x + 1 / ((n : ℝ) + 1) := by positivity
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hab : x + 1 / ((n : ℝ) + 1) < x + m + 2 := by
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    obtain ⟨r, hr, hgr⟩ := exists_mem_Icc_le_of_rat hgc hpos hab hq
    have hxr : x < r := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith [hr.1]
    by_contra hRx
    push Not at hRx
    have := h2 r (lt_of_le_of_lt hRx hxr)
    simp only [hg] at hgr
    linarith

/-- The countable measurable event of `lt_scaleRadius_iff`. -/
lemma measurableSet_scaleRadius_witness {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ} (γ b : ℝ)
    (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {x : ℝ} (hx : 0 ≤ x) :
    MeasurableSet {ω | ∃ n m : ℕ, ∀ k : ℕ, ∃ q : ℚ,
      (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)} := by
  have hset : {ω | ∃ n m : ℕ, ∀ k : ℕ, ∃ q : ℚ,
      (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)} =
      ⋃ n : ℕ, ⋃ m : ℕ, ⋂ k : ℕ, ⋃ q : ℚ, {ω | (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)} := by
    ext ω; simp
  rw [hset]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun k =>
    MeasurableSet.iUnion fun q => ?_
  by_cases hq : (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2)
  · have hq0 : 0 < (q : ℝ) := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith [hq.1]
    have : {ω | (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)} =
        {ω | hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)} := by
      ext ω; exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
    rw [this]
    exact measurableSet_lt (((hmeas q 0 hq0).add_const _).sub_const _) measurable_const
  · have : {ω | (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)} = ∅ := by
      ext ω; exact ⟨fun h => absurd h.1 hq, fun h => h.elim⟩
    rw [this]
    exact MeasurableSet.empty

/-- A positive function whose strict superlevel sets agree with measurable sets off a measurable null set is almost
everywhere measurable. -/
lemma aemeasurable_of_gt_iff_off_null {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {R : Ω → ℝ} {N : Set Ω}
    (hN : MeasurableSet N) (hN0 : μ N = 0) (hpos : ∀ ω, ω ∉ N → 0 < R ω) (E : ℝ → Set Ω)
    (hE : ∀ x, 0 ≤ x → MeasurableSet (E x)) (hRE : ∀ x, 0 ≤ x → ∀ ω, ω ∉ N → (x < R ω ↔ ω ∈ E x)) :
    AEMeasurable R μ := by
  classical
  refine ⟨fun ω => if ω ∈ N then 1 else R ω, measurable_of_Ioi fun x => ?_, ?_⟩
  · by_cases hx : 0 ≤ x
    · have : (fun ω => if ω ∈ N then (1 : ℝ) else R ω) ⁻¹' Ioi x = (N ∩ {_ω | x < 1}) ∪ (Nᶜ ∩ E x) := by
        ext ω
        by_cases hω : ω ∈ N
        · simp [hω]
        · simp only [hω, ite_false, mem_preimage, mem_Ioi, mem_union, mem_inter_iff, mem_compl_iff]
          rw [hRE x hx ω hω]; tauto
      rw [this]
      exact (hN.inter (MeasurableSet.const _)).union (hN.compl.inter (hE x hx))
    · push Not at hx
      have : (fun ω => if ω ∈ N then (1 : ℝ) else R ω) ⁻¹' Ioi x = univ := by
        ext ω
        by_cases hω : ω ∈ N
        · simp [hω]; linarith
        · simp [hω]; exact lt_trans hx (hpos ω hω)
      rw [this]; exact MeasurableSet.univ
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simp [hω]

/-- **The cone scale radius is almost everywhere measurable.** -/
theorem aemeasurable_coneScaleRadius {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    AEMeasurable (fun ω => coneScaleRadius γ (hcirc ω) b) P := by
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      (0 < coneScaleRadius γ (hcirc ω) b ∧
      hcirc ω (coneScaleRadius γ (hcirc ω) b) 0 + lqgQ γ * Real.log (coneScaleRadius γ (hcirc ω) b)
        = γ⁻¹ * Real.log b ∧
      ∀ r : ℝ, coneScaleRadius γ (hcirc ω) b < r →
        γ⁻¹ * Real.log b < hcirc ω r 0 + lqgQ γ * Real.log r) := by
    filter_upwards [h.ae_continuousOn_circle, ae_coneScaleRadius_spec hγ0 hγ2 h b] with ω h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hok : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      (0 < coneScaleRadius γ (hcirc ω) b ∧
      hcirc ω (coneScaleRadius γ (hcirc ω) b) 0 + lqgQ γ * Real.log (coneScaleRadius γ (hcirc ω) b)
        = γ⁻¹ * Real.log b ∧
      ∀ r : ℝ, coneScaleRadius γ (hcirc ω) b < r →
        γ⁻¹ * Real.log b < hcirc ω r 0 + lqgQ γ * Real.log r) := fun ω hω => by
    by_contra hc; exact hω (hsub hc)
  refine aemeasurable_of_gt_iff_off_null hNm hN0 (fun ω hω => (hok ω hω).2.1)
    (fun x => {ω | ∃ n m : ℕ, ∀ k : ℕ, ∃ q : ℚ,
      (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hcirc ω q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)})
    (fun x hx => measurableSet_scaleRadius_witness γ b h.measurable_circle hx) ?_
  intro x hx ω hω
  exact lt_scaleRadius_iff (hok ω hω).1 (hok ω hω).2.2.1 (hok ω hω).2.2.2 hx

/-- **Random evaluation of a continuous random field at a random scale.**  If `(r, z) ↦ h_r(z)` is measurable for
each `(r, z)` and almost surely continuous on `(0, ∞) × ℂ`, and `R > 0` is almost everywhere measurable, then the circle
average process `(r, z) ↦ h_{R r}(R z) + Q log R - γ⁻¹ log b` of the rescaled field is almost everywhere measurable
as a random element of `(0, ∞) × ℂ → ℝ`. -/
theorem aemeasurable_circleProcess_rescaledCircle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} (γ b : ℝ) (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {R : Ω → ℝ} (hR : AEMeasurable R P) (hRpos : ∀ᵐ ω ∂P, 0 < R ω) :
    AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) P := by
  classical
  obtain ⟨R₀, hR₀m, hR₀⟩ := hR
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      R ω = R₀ ω ∧ 0 < R ω := by
    filter_upwards [hcont, hR₀, hRpos] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hok : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      R ω = R₀ ω ∧ 0 < R ω := fun ω hω => by
    by_contra hc; exact hω (hsub hc)
  set h' : Ω → ℝ → ℂ → ℝ := fun ω r z => if ω ∈ N then 0 else hcirc ω r z with hh'
  set R' : Ω → ℝ := fun ω => if ω ∈ N then 1 else R₀ ω with hR'
  have hR'm : Measurable R' := Measurable.ite hNm measurable_const hR₀m
  have hR'pos : ∀ ω, 0 < R' ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp [hR', hω]
    · simp only [hR', hω, ite_false]
      rw [← (hok ω hω).2.1]; exact (hok ω hω).2.2
  set u : (Ioi (0 : ℝ) × ℂ) → Ω → ℝ := fun p ω => h' ω p.1 p.2 with hu
  have hu_cont : ∀ ω, Continuous fun p : Ioi (0 : ℝ) × ℂ => u p ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hu, hh', hω, ite_true]; exact continuous_const
    · simp only [hu, hh', hω, ite_false]
      exact (hok ω hω).1.comp_continuous (by fun_prop : Continuous fun p : Ioi (0 : ℝ) × ℂ => ((p.1 : ℝ), p.2))
        (fun p => ⟨p.1.2, mem_univ _⟩)
  have hu_meas : ∀ p : Ioi (0 : ℝ) × ℂ, Measurable (u p) := fun p =>
    Measurable.ite hNm measurable_const (hmeas p.1 p.2 p.1.2)
  have hU : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable hu_cont hu_meas
  refine ⟨fun ω p => h' ω (R' ω * p.1.1) ((R' ω : ℂ) * p.2) + lqgQ γ * Real.log (R' ω) - γ⁻¹ * Real.log b,
    ?_, ?_⟩
  · refine measurable_pi_iff.2 fun p => ?_
    have hψ : Measurable fun ω => ((⟨R' ω * p.1.1, mul_pos (hR'pos ω) p.1.2⟩ : Ioi (0 : ℝ)), (R' ω : ℂ) * p.2) :=
      Measurable.prodMk (Measurable.subtype_mk (hR'm.mul_const _))
        ((Complex.measurable_ofReal.comp hR'm).mul_const _)
    have hcomp : Measurable fun ω => h' ω (R' ω * p.1.1) ((R' ω : ℂ) * p.2) :=
      hU.comp (hψ.prodMk measurable_id)
    exact (hcomp.add ((Real.measurable_log.comp hR'm).const_mul _)).sub_const _
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    funext p
    have hRR : R ω = R' ω := by simp only [hR', hω, ite_false]; exact (hok ω hω).2.1
    simp only [circleProcess, rescaledCircle, hh', hR', hω, ite_false] at hRR ⊢
    rw [hRR]

/-- **The rescaled circle average process of a `γ`-quantum cone is almost everywhere measurable.** -/
theorem aemeasurable_coneRescaledCircleProcess {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) P :=
  aemeasurable_circleProcess_rescaledCircle γ b h.measurable_circle h.ae_continuousOn_circle
    (aemeasurable_coneScaleRadius hγ0 hγ2 h b)
    ((ae_coneScaleRadius_spec hγ0 hγ2 h b).mono fun _ hω => hω.1)

end MatedCRT.FirstPass.Derived
