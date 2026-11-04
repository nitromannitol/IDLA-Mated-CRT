import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# Scaling of harmonic balls: conditions (a) and (b) of Theorem 2.3

For `R, b > 0`, the dilation `x ↦ R x` transports the family `{Λ_t}_{0 < t < bT}` for `μ` to the family
`{R⁻¹ Λ_{bt}}_{0 < t < T}` (`rescaledFamily`) for `b⁻¹ μ(R ·)` (`rescaledMeasure`): measures, frontiers, regular
openness, boundedness, connectedness, monotonicity, Hausdorff continuity and `⋂_t Λ_t = {0}` are preserved
(`SatisfiesHarmonicBallConditionsOn.rescaledFamily`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The dilation `x ↦ R x` of the plane, `R ≠ 0`. -/
noncomputable def dilation (R : ℝ) (hR : R ≠ 0) : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (R : ℂ) (Complex.ofReal_ne_zero.2 hR)

theorem dilation_apply {R : ℝ} (hR : R ≠ 0) (x : ℂ) : dilation R hR x = (R : ℂ) * x := rfl

theorem rescaledFamily_eq_preimage (Λ : ℝ → Set ℂ) {R : ℝ} (hR : R ≠ 0) (b t : ℝ) :
    rescaledFamily Λ R b t = dilation R hR ⁻¹' Λ (b * t) := rfl

/-- `b⁻¹ μ(R ·)` of the preimage of `B` under `x ↦ R x` is `b⁻¹ μ(B)`. -/
theorem rescaledMeasure_preimage (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) (b : ℝ) (B : Set ℂ) :
    rescaledMeasure μ R b ((fun x => (R : ℂ) * x) ⁻¹' B) = ENNReal.ofReal b⁻¹ * μ B := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  have hemb : MeasurableEmbedding fun x : ℂ => (R : ℂ)⁻¹ * x :=
    (Homeomorph.mulLeft₀ _ (inv_ne_zero hRc)).measurableEmbedding
  rw [rescaledMeasure, Measure.smul_apply, hemb.map_apply, smul_eq_mul]
  congr 2
  ext x
  simp [hRc]

theorem norm_dilation {R : ℝ} (hR : 0 < R) (x : ℂ) : ‖(R : ℂ) * x‖ = R * ‖x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]

/-- Hausdorff distance of preimages under the dilation `x ↦ R x`. -/
theorem hausdorffEDist_dilation_preimage_le {A B : Set ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ)
    (h : hausdorffEDist A B < ENNReal.ofReal δ) :
    hausdorffEDist ((fun x => (R : ℂ) * x) ⁻¹' A) ((fun x => (R : ℂ) * x) ⁻¹' B) ≤
      ENNReal.ofReal (R⁻¹ * δ) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have key : ∀ {A B : Set ℂ}, hausdorffEDist A B < ENNReal.ofReal δ →
      ∀ x ∈ (fun x => (R : ℂ) * x) ⁻¹' A, ∃ y ∈ (fun x => (R : ℂ) * x) ⁻¹' B,
        edist x y ≤ ENNReal.ofReal (R⁻¹ * δ) := by
    intro A B h x hx
    obtain ⟨z, hz, hxz⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt (show (R : ℂ) * x ∈ A from hx) h
    refine ⟨(R : ℂ)⁻¹ * z, ?_, ?_⟩
    · show (R : ℂ) * ((R : ℂ)⁻¹ * z) ∈ B
      rw [mul_inv_cancel_left₀ hRc]
      exact hz
    · rw [edist_lt_ofReal] at hxz
      rw [edist_le_ofReal (by positivity), dist_eq_norm]
      have e : x - (R : ℂ)⁻¹ * z = (R : ℂ)⁻¹ * ((R : ℂ) * x - z) := by
        field_simp
      rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left hxz.le (inv_nonneg.2 hR.le)
  refine Metric.hausdorffEDist_le_of_mem_edist (key h) ?_
  intro x hx
  rw [Metric.hausdorffEDist_comm] at h
  obtain ⟨y, hy, hxy⟩ := key h x hx
  exact ⟨y, hy, hxy⟩

/-- **Conditions (a) and (b) of Theorem 2.3 are preserved by scaling.** -/
theorem SatisfiesHarmonicBallConditionsOn.rescale {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {R b T : ℝ}
    (h : SatisfiesHarmonicBallConditionsOn μ Λ 0 (b * T)) (hR : 0 < R) (hb : 0 < b) :
    SatisfiesHarmonicBallConditionsOn (rescaledMeasure μ R b) (rescaledFamily Λ R b) 0 T := by
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  have hbt : ∀ t ∈ Ioo 0 T, b * t ∈ Ioo 0 (b * T) := fun t ht =>
    ⟨mul_pos hb ht.1, mul_lt_mul_of_pos_left ht.2 hb⟩
  have hpre : ∀ t, rescaledFamily Λ R b t = dilation R hR0 ⁻¹' Λ (b * t) := fun t => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [rescaledFamily, show {x : ℂ | (R : ℂ) * x ∈ Λ (b * t)} = (fun x => (R : ℂ) * x) ⁻¹' Λ (b * t) from rfl,
      rescaledMeasure_preimage μ hR0, h.measure_eq _ (hbt t ht), ← ENNReal.ofReal_mul (inv_nonneg.2 hb.le),
      inv_mul_cancel_left₀ hb.ne']
  · intro t ht
    rw [hpre, ← (dilation R hR0).preimage_frontier]
    show rescaledMeasure μ R b ((fun x => (R : ℂ) * x) ⁻¹' frontier (Λ (b * t))) = 0
    rw [rescaledMeasure_preimage μ hR0, h.measure_frontier _ (hbt t ht), mul_zero]
  · intro t ht
    have h1 := h.isRegularOpen _ (hbt t ht)
    show interior (closure (rescaledFamily Λ R b t)) = rescaledFamily Λ R b t
    rw [hpre, ← (dilation R hR0).preimage_closure, ← (dilation R hR0).preimage_interior]
    exact congrArg _ h1
  · intro t ht
    obtain ⟨r, hr⟩ := (h.isBounded _ (hbt t ht)).subset_ball 0
    refine (isBounded_ball (x := (0 : ℂ)) (r := r / R)).subset fun x hx => ?_
    have hx' : (R : ℂ) * x ∈ ball 0 r := hr hx
    rw [mem_ball_zero_iff, norm_dilation hR] at hx'
    rw [mem_ball_zero_iff, lt_div_iff₀ hR]
    linarith
  · intro t ht
    rw [hpre]
    exact (dilation R hR0).isConnected_preimage.2 (h.isConnected _ (hbt t ht))
  · intro t ht
    show (R : ℂ) * 0 ∈ Λ (b * t)
    rw [mul_zero]
    exact h.mem _ (hbt t ht)
  · intro s hs t ht hst
    exact preimage_mono (h.monotoneOn (hbt s hs) (hbt t ht) (mul_le_mul_of_nonneg_left hst hb.le))
  · intro t ht ε hε
    obtain ⟨η, hη0, hη, hηε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hη0' : 0 < η := ENNReal.ofReal_pos.1 hη
    have h1 := h.hausdorffContinuousOn (b * t) (hbt t ht) (ENNReal.ofReal (R * η))
      (ENNReal.ofReal_pos.2 (mul_pos hR hη0'))
    rw [isOpen_Ioo.nhdsWithin_eq (hbt t ht)] at h1
    rw [isOpen_Ioo.nhdsWithin_eq ht]
    have htend : Tendsto (fun s => b * s) (𝓝 t) (𝓝 (b * t)) := tendsto_id.const_mul b
    filter_upwards [htend.eventually h1] with s hs
    calc hausdorffEDist (rescaledFamily Λ R b s) (rescaledFamily Λ R b t)
        ≤ ENNReal.ofReal (R⁻¹ * (R * η)) := hausdorffEDist_dilation_preimage_le hR (by positivity) hs
      _ = ENNReal.ofReal η := by rw [inv_mul_cancel_left₀ hR0]
      _ < ε := hηε
  · ext x
    simp only [mem_iInter, mem_singleton_iff]
    constructor
    · intro hx
      have hmem : (R : ℂ) * x ∈ ⋂ u ∈ Ioo 0 (b * T), Λ u := by
        simp only [mem_iInter]
        intro u hu
        have hu' : u / b ∈ Ioo 0 T := ⟨div_pos hu.1 hb, by rw [div_lt_iff₀ hb]; linarith [hu.2]⟩
        have h2 : (R : ℂ) * x ∈ Λ (b * (u / b)) := hx (u / b) hu'
        have e : b * (u / b) = u := by field_simp
        rwa [e] at h2
      rw [h.iInter_eq, mem_singleton_iff] at hmem
      exact (mul_eq_zero.1 hmem).resolve_left hRc
    · rintro rfl t ht
      show (R : ℂ) * 0 ∈ Λ (b * t)
      rw [mul_zero]
      exact h.mem _ (hbt t ht)

end MatedCRT
